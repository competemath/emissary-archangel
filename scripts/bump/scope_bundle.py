#!/usr/bin/env python3
"""scope_bundle.py — a bundle must not leak notation, macros, elaborators or syntax into the rest of the tree: every global command of its modules is made `scoped` or `local`.

A GLOBAL `notation`, `infix`, `prefix`, `macro`, `elab` or `syntax` command of one library is a second reading of a symbol, or a reserved word, in every file of the tree that imports it
(2026-10-17: lean-pool's `prefix:80 "-"` made `-(3 * x)` "Ambiguous term" on a real number on every Leak service; `fun v => …` failed with "unexpected token 'v'" for an atom of a
notation, and 35 such words were found in two libraries). Until now the factory shipped them and a census (notation_census.py) found the colliding ones afterwards, as a scope-fix PR on
the tree. Tengoku's lint refuses a global command in an added line in every mode (scripts/ci/allowlist.py `unscoped_violations`), so the bundle is cut the way the tree takes it:
`bundle.py compose` calls `scope_dir` on every bundle it writes, and `dry_run` on the text of every module before the cut, so that a module whose command cannot be scoped is left out with
what imports it (like one that does not lint), with the reason in the report.

The edit is scope_rewrite.py's (a command becomes `scoped` inside a namespace, with `open scoped N` where the code after it, or an importer inside the library, still uses it; `local` at
the root, declared again in the importers) driven by the commands themselves, not by a leak report: ALL global commands, whether or not they collide with a token the seed has today.
A namespace in which core Lean or Mathlib have scoped entries (seed-scoped-namespaces.json) or the library has some already is never opened with `open scoped`: a command that would need it stays
global, and `unscoped` names it.

  scope_bundle.py --bundle DIR [--bundle DIR …] --key K     (rewrites in place; prints one JSON line per bundle)
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import notation_census as nc  # noqa: E402
import scope_rewrite as sr  # noqa: E402

SEED_SCOPED = HERE / "seed-scoped-namespaces.json"
# a `scoped` entry of any kind (tengoku scripts/ci/scope_fix_check.py SCOPED_USE): `open scoped N` turns on all of them
SCOPED_USE = re.compile(
    r"(?:^|[\s@\[,])scoped(?:\[(?P<ns>[\w.«»']+)\])?[ \t]+(?:instance|notation3?|infix[lr]?|prefix|postfix|macro|syntax|elab|attribute|simp|irreducible_def|def|abbrev|theorem|lemma)\b"
    r"|@\[[^\]]*\bscoped\b"
)


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def seed_scoped() -> set[str]:
    return set(json.loads(SEED_SCOPED.read_text())["namespaces"])


def module_files(root: Path, key: str) -> dict[str, Path]:
    """the library's modules in a bundle directory, by their full module name (`Tengoku.<Library>.A.B`)"""
    tree_root = root / "Tengoku" / pascal(key)
    return {
        ".".join(f.relative_to(root).with_suffix("").parts): f
        for f in sorted(tree_root.rglob("*.lean"))
        if not f.is_symlink() and f.name != "Deps.lean"  # Deps.lean is a comment that marks the library for Tengoku/All.lean
    }


def own_scoped(files: dict[str, Path]) -> set[str]:
    """the namespaces in which the library's modules declare something `scoped` already"""
    out: set[str] = set()
    for f in files.values():
        code = sr.mask(f.read_text(encoding="utf-8", errors="replace")).split("\n")
        blocks: list[list[str]] = []
        for ln in code:
            if nm := sr.NAMESPACE.match(ln):
                blocks.append(nm.group(1).split("."))
            elif sr.OPENER.match(ln):
                blocks.append([])
            elif sr.CLOSER.match(ln):
                if blocks:
                    blocks.pop()
            elif use := SCOPED_USE.search(ln):
                out.add(use.group("ns") or ".".join(c for blk in blocks for c in blk))
    return out


def global_commands(files: dict[str, Path]) -> list[dict]:
    """every global notation-family command of the modules, as the leak lines scope_rewrite.py takes: ALL of them, not the ones that collide with a token of today's seed"""
    leaks = []
    for mod, f in files.items():
        for rec in nc.census(f.read_text(encoding="utf-8", errors="replace"), None):
            leaks.append({"kind": "notation", "name": f"src@{rec['line']}", "mod": mod, "line": rec["line"], "prio": None})
    return leaks


def scope_dir(root: Path, key: str) -> dict:
    """Make every global notation-family command of the bundle in `root` scoped or local, in place. Returns {"scoped": n, "unscoped": {module: [why, …]}}: the second is what is still global
    afterwards (a namespace the seed or the library has scoped entries in, an `open` the importers lack): the caller leaves those modules out."""
    files = module_files(root, key)
    leaks = global_commands(files)
    if not leaks:
        return {"scoped": 0, "unscoped": {}}
    sr.FORBIDDEN_NS.clear()
    sr.FORBIDDEN_NS.update(seed_scoped() | own_scoped(files))
    report = sr.apply_bundle(root, leaks)
    report.update(sr.reexport(root, leaks))
    unscoped: dict[str, list[str]] = {}
    for s in report["skipped"]:  # "<module>: notation src@LINE: why"
        mod, _, why = s.partition(": ")
        unscoped.setdefault(mod, []).append(why)
    return {"scoped": report["rewritten"], "unscoped": unscoped}


def dry_run(texts: dict[str, str], key: str) -> tuple[dict[str, str], dict[str, list[str]]]:
    """The modules of a library as they would ship (`texts`: path inside the library, e.g. `Toy/A.lean` -> its text in the tree's layout), scoped in a scratch directory: (the scoped
    texts, the modules whose commands cannot be made scoped or local, by path, with why). Nothing is written outside the scratch directory."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        base = root / "Tengoku" / pascal(key)
        for rel, text in texts.items():
            (base / rel).parent.mkdir(parents=True, exist_ok=True)
            (base / rel).write_text(text)
        result = scope_dir(root, key)
        scoped = {rel: (base / rel).read_text() for rel in texts}
        by_path = {".".join(Path(rel).with_suffix("").parts): rel for rel in texts}
        prefix = f"Tengoku.{pascal(key)}."
        return scoped, {by_path.get(m.removeprefix(prefix), m): why for m, why in result["unscoped"].items()}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", required=True)
    ap.add_argument("--key", required=True)
    a = ap.parse_args()
    bad = 0
    for b in a.bundle:
        if not Path(b).exists():
            continue
        r = scope_dir(Path(b), a.key)
        bad += len(r["unscoped"])
        print(b, json.dumps(r, ensure_ascii=False))
    if bad:
        sys.exit(f"{bad} module(s) still declare a global notation that cannot be made scoped or local")


if __name__ == "__main__":
    main()
