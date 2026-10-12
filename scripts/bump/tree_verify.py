#!/usr/bin/env python3
"""tree_verify.py — build the bundle in the TREE's own environment before it is cut into parts.

The factory builds a library in the library's own environment and checks every proof again against the tree's Mathlib, but until now the first time the shipped TEXT was
compiled in the tree was the merge queue, one part at a time: a part came back for every module the tree behaves differently on (typeclass searches that time out in a bigger
instance set, a Mathlib that differs, an instance the text never names). This does that build ahead of time, for every module the tree does not have yet at once, with the queue's
own command (`lake build Tengoku.<Ns>.<module> …`) on a checkout seeded from the tree's cache. The modules that fail are dropped (with their importers) by `bundle.py compose
--tree-failures`, and `check` then proves that every module that ships is byte for byte a module that was built there.

  tree_verify.py apply   --bundle DIR --tree CHECKOUT --out OUT   copy the bundle's new modules into the checkout, write OUT/targets.txt (what to build) and OUT/new.json
  tree_verify.py collect --new OUT/new.json --log build.log --out OUT   read the build: OUT/failing.txt (library modules), OUT/ok.json (module -> sha256), OUT/summary.txt
  tree_verify.py check   --bundle DIR --new OUT/new.json --ok OUT/ok.json   exit 1 unless every new module of the final bundle was built there with the same bytes

`apply` and `check` take the bundle as `compose` wrote it (DIR/Tengoku/<Ns>.lean, DIR/Tengoku/<Ns>/**.lean). "New" is what the tree's umbrella `Tengoku/<Ns>.lean` does not import
(bundle_layers.tree_modules): the modules the parts will carry. The build runs no token and the job that runs it signs nothing: the library's own code is compiled there.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bundle_layers as bl  # noqa: E402

ERROR = re.compile(r"^(?:\S+\s+)?error: (?P<path>Tengoku/[^/\s]+/\S+?\.lean):\d+:\d+: ", re.M)
SORRY = re.compile(r"^(?:\S+\s+)?warning: (?P<path>Tengoku/[^/\s]+/\S+?\.lean):\d+:\d+: declaration uses .sorry.", re.M)
BUILT = re.compile(r"Built (?P<mod>Tengoku\.\S+)(?: \(|\s*$)", re.M)
FAILED_TARGET = re.compile(r"^(?:\S+\s+)?- (?P<mod>Tengoku\.\S+)\s*$", re.M)
FINISHED = re.compile(r"Build completed successfully|Some required targets logged failures|error: build failed")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def new_modules(files: dict[str, bytes], ns: str, tree_umbrella: str | None) -> dict[str, str]:
    """module -> path of the bundle's modules the tree does not have yet (`Deps` is the marker of the library, no module)."""
    mods = bl.own_modules(files, ns)
    have = bl.tree_modules(tree_umbrella, ns) if tree_umbrella else {f"Tengoku.{ns}.Deps"}
    return {m: p for m, p in mods.items() if m not in have}


def dependents(failing: set[str], graph: dict[str, list[str]]) -> set[str]:
    """Every module that imports a failing one, directly or not (the build never reports them: it does not reach them)."""
    out: set[str] = set()
    todo = list(failing)
    while todo:
        x = todo.pop()
        for m, deps in graph.items():
            if x in deps and m not in out:
                out.add(m)
                todo.append(m)
    return out


def failures_from_log(log: str, ns: str) -> set[str]:
    """The modules (as Lean spells them) the build refused: an error in them, a `sorry` (the queue treats it as an error), or a failing target the build lists."""
    prefix = f"Tengoku/{ns}/"
    out = {bl.module_name(m.group("path")) for m in ERROR.finditer(log) if m.group("path").startswith(prefix)}
    out |= {bl.module_name(m.group("path")) for m in SORRY.finditer(log) if m.group("path").startswith(prefix)}
    out |= {m.group("mod") for m in FAILED_TARGET.finditer(log) if m.group("mod").startswith(f"Tengoku.{ns}.")}
    return out


def library_module(module: str, ns: str) -> str:
    """`Tengoku.LeanPool.LeanPool.Foo` -> `LeanPool.Foo`: the library's own name, which `compose --tree-failures` takes."""
    return module.removeprefix(f"Tengoku.{ns}.")


def cmd_apply(a: argparse.Namespace) -> None:
    files = bl.read_bundle(Path(a.bundle))
    ns = bl.namespace(files)
    tree = Path(a.tree)
    umbrella_path = tree / "Tengoku" / f"{ns}.lean"
    umbrella = umbrella_path.read_text(encoding="utf-8") if umbrella_path.is_file() else None
    new = new_modules(files, ns, umbrella)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for p in new.values():
        dest = tree / p
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(files[p])
    (out / "targets.txt").write_text("".join(m + "\n" for m in sorted(new)))
    (out / "new.json").write_text(json.dumps({"ns": ns, "modules": {m: {"path": p, "sha256": sha256(files[p])} for m, p in sorted(new.items())}}, indent=1) + "\n")
    print(f"{len(new)} new module(s) of {len(bl.own_modules(files, ns))} in the bundle: copied into {tree}; targets in {out / 'targets.txt'}")


def cmd_collect(a: argparse.Namespace) -> None:
    new = json.loads(Path(a.new).read_text())
    ns, mods = new["ns"], new["modules"]
    log = Path(a.log).read_text(errors="replace")
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    if mods and not FINISHED.search(log):
        sys.exit("the build log has no ending (the build was killed or timed out): nothing is known about the modules; refusing to guess")
    failing = failures_from_log(log, ns) & set(mods)
    built = {m.group("mod") for m in BUILT.finditer(log)} & set(mods)
    graph: dict[str, list[str]] = {}
    if a.bundle:
        bfiles = bl.read_bundle(Path(a.bundle))
        graph = {m: [d for d in deps if d in mods] for m, deps in bl.import_graph(bfiles, {m: p["path"] for m, p in mods.items()}).items()}
    cascade = dependents(failing, graph)
    unaccounted = set(mods) - failing - cascade - built  # no error, no `Built` line, not downstream of a failure: the build did not reach it, so it was not verified
    failing |= unaccounted
    cascade = dependents(failing, graph)
    ok = {m: mods[m]["sha256"] for m in mods if m not in failing and m not in cascade}
    (out / "failing.txt").write_text("".join(library_module(m, ns) + "\n" for m in sorted(failing)))
    (out / "ok.json").write_text(json.dumps(ok, indent=1) + "\n")
    summary = (
        f"{len(mods)} new module(s): {len(ok)} built in the tree, {len(failing)} refused ({len(unaccounted)} of them not reached), "
        f"{len(cascade - failing)} more import a refused one and go with it"
    )
    (out / "summary.txt").write_text(summary + "\n")
    print(summary)


def cmd_check(a: argparse.Namespace) -> None:
    files = bl.read_bundle(Path(a.bundle))
    ns = bl.namespace(files)
    new = json.loads(Path(a.new).read_text())
    ok = json.loads(Path(a.ok).read_text())
    shipped = bl.own_modules(files, ns)
    problems = []
    for m, spec in sorted(new["modules"].items()):
        if m not in shipped:
            continue  # dropped: nothing to prove
        if m not in ok:
            problems.append(f"{m}: ships, but the tree's build did not accept it")
        elif sha256(files[shipped[m]]) != ok[m]:
            problems.append(f"{m}: ships with other bytes than the ones the tree's build accepted")
    if problems:
        sys.exit("the bundle ships what the tree's build did not verify:\n  " + "\n  ".join(problems[:20]) + (f"\n  … and {len(problems) - 20} more" if len(problems) > 20 else ""))
    print(f"every one of the {sum(1 for m in new['modules'] if m in shipped)} shipped new module(s) is byte for byte a module the tree's build accepted")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("apply")
    p.add_argument("--bundle", required=True)
    p.add_argument("--tree", required=True)
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_apply)
    p = sub.add_parser("collect")
    p.add_argument("--new", required=True)
    p.add_argument("--log", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--bundle", default="", help="the bundle the modules came from: its import graph says which modules go with a refused one")
    p.set_defaults(fn=cmd_collect)
    p = sub.add_parser("check")
    p.add_argument("--bundle", required=True)
    p.add_argument("--new", required=True)
    p.add_argument("--ok", required=True)
    p.set_defaults(fn=cmd_check)
    a = ap.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
