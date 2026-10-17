#!/usr/bin/env python3
"""deficient_tree.py — the modules of a library the tree has merged that are deficient, and the raze plan that follows from them.

  deficient_tree.py --bundle bundle-<key>-proposed.tar --tree TENGOKU_CHECKOUT --lib KEY [--out plan.json]

A library that arrives in parts is cut from the tree (`from_tree`, bundle_layers.py): a recut can only ADD modules, so a module merged by an earlier part is final. When the compose
that cut it was wrong (2026-10-11: the first pruner cut declarations that proofs of other modules still name), the merged module lacks declarations the corrected compose keeps, and
every later module that names them fails to build in the tree.

A tree module is DEFICIENT when the bundle (the full compose of the same library, with today's compose) declares a name the tree's module does not (`lean_names.names`: the
non-private declarations; a name the tree has and the bundle lacks is not a deficiency). A deficient module has to leave the tree before the next cut can bring it back, and so does
everything in the tree that imports it, transitively (tengoku's `raze` class takes modules out only with their dependents: scripts/ci/raze_check.py there). The plan lists

  deficient   module -> the names the tree's version lacks
  dependents  the modules of the tree that import a deficient one (directly or not), and are not deficient themselves
  raze        the marker's `modules`: the deficient modules the tree can get back, and their dependents. A deficient module whose dependents include a module the bundle does not
              carry (today's compose drops it) is BLOCKED: razing it would delete modules that cannot come back, so it stays, and is listed under `blocked`
  all         everything deficient + dependents, blocked or not (the plan without that restraint), and `lost`: the modules of it that the bundle does not carry
  at_risk     modules of the bundle that the tree does not have yet and that name a declaration a blocked module lacks: a cut would ship them and the queue would eject them
              (they and what imports them are for the drop list)

Nothing is written but the plan. `make_raze.py` turns a plan into the files of a raze PR.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tolerant_build as tb  # noqa: E402
from bundle_layers import own_modules, tree_modules  # noqa: E402
from lean_names import names  # noqa: E402


def bundle_files(tar_path: Path) -> dict[str, bytes]:
    out: dict[str, bytes] = {}
    with tarfile.open(tar_path) as t:
        for m in t:
            if m.isfile():
                f = t.extractfile(m)
                assert f is not None
                out[m.name.removeprefix("./")] = f.read()
    return out


def tree_files(root: Path, ns: str) -> dict[str, bytes]:
    """The library's files of a tengoku checkout, keyed like a bundle: Tengoku/<Ns>.lean and Tengoku/<Ns>/**.lean."""
    out: dict[str, bytes] = {}
    umbrella = root / "Tengoku" / f"{ns}.lean"
    if umbrella.exists():
        out[f"Tengoku/{ns}.lean"] = umbrella.read_bytes()
    for p in sorted((root / "Tengoku" / ns).rglob("*.lean")):
        if p.is_file() and not p.is_symlink():
            out[str(p.relative_to(root))] = p.read_bytes()
    return out


def plan(bundle: dict[str, bytes], tree: dict[str, bytes], ns: str) -> dict:
    umbrella = tree.get(f"Tengoku/{ns}.lean")
    if umbrella is None:
        raise SystemExit(f"the tree has no Tengoku/{ns}.lean: {ns} is not in it")
    in_bundle = own_modules(bundle, ns)
    in_tree = own_modules(tree, ns)
    listed = tree_modules(umbrella.decode("utf-8", "replace"), ns)
    merged = {m: p for m, p in in_tree.items() if m in listed}  # the umbrella's modules (and the marker Deps, which no umbrella lists)
    deficient: dict[str, list[str]] = {}
    for m, p in sorted(merged.items()):
        if m not in in_bundle:
            continue
        missing = names(bundle[in_bundle[m]].decode("utf-8", "replace")) - names(tree[p].decode("utf-8", "replace"))
        if missing:
            deficient[m] = sorted(missing)
    own = set(merged)
    importers: dict[str, set[str]] = {m: set() for m in merged}  # module -> the tree modules that import it
    for m, p in merged.items():
        for d in tb.header_imports(tree[p].decode("utf-8", "replace")):
            if d in own and d != m:
                importers[d].add(m)
    def importers_of(roots) -> set[str]:
        """The modules of the tree that import any of `roots`, directly or not (the roots themselves left out)."""
        out: set[str] = set()
        todo = list(roots)
        while todo:
            for u in importers[todo.pop()]:
                if u not in out and u not in roots:
                    out.add(u)
                    todo.append(u)
        return out

    def closure(d: str) -> set[str]:
        return {d} | importers_of({d})

    lost_of = {d: sorted(closure(d) - set(in_bundle)) for d in deficient}
    blocked = {d: lost_of[d] for d in sorted(deficient) if lost_of[d]}
    fixable = {d: miss for d, miss in deficient.items() if d not in blocked}
    razed: set[str] = set()
    for d in fixable:
        razed |= closure(d)
    everything: set[str] = set()
    for d in deficient:
        everything |= closure(d)
    # what a cut would ship that still names what a blocked module lacks: the textual reading keep_closure.py uses (a distinctive last component)
    missing = {n.rsplit(".", 1)[-1] for d in blocked for n in deficient[d]}
    distinctive = {n for n in missing if len(n) >= 8 and ("_" in n or any(c.isupper() for c in n[1:]))}
    at_risk = sorted(
        m
        for m, p in in_bundle.items()
        if m not in merged and any(re.search(rf"(?<![\w.']){re.escape(n)}(?![\w'])", bundle[p].decode("utf-8", "replace")) for n in distinctive)
    )
    return {
        "library_namespace": ns,
        "tree_modules": len(merged),
        "bundle_modules": len(in_bundle),
        "deficient": deficient,
        "dependents": sorted(razed - set(deficient)),
        "raze": sorted(razed),
        "blocked": blocked,
        "all": sorted(everything),
        "lost": sorted(everything - set(in_bundle)),
        "at_risk": at_risk,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", required=True, help="the full compose of the library (bundle-<key>-proposed.tar of a bump run)")
    ap.add_argument("--tree", required=True, help="a checkout of tengoku with Tengoku/<Ns>.lean and Tengoku/<Ns>/")
    ap.add_argument("--lib", required=True, help="the library key")
    ap.add_argument("--out", default="")
    a = ap.parse_args(argv)
    ns = "".join(p[:1].upper() + p[1:] for p in a.lib.replace("_", "-").split("-") if p)
    p = plan(bundle_files(Path(a.bundle)), tree_files(Path(a.tree), ns), ns)
    p["library"] = a.lib
    print(
        f"{a.lib}: {p['tree_modules']} modules in the tree, {p['bundle_modules']} in the bundle: {len(p['deficient'])} deficient ({len(p['blocked'])} blocked by modules the bundle does not carry), "
        f"{len(p['raze'])} to raze; without the restraint {len(p['all'])}, of which {len(p['lost'])} could not come back; {len(p['at_risk'])} modules of the bundle name what a blocked one lacks"
    )
    if a.out:
        Path(a.out).write_text(json.dumps(p, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
