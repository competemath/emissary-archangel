#!/usr/bin/env python3
"""root_lines.py --merged DIR --out FILE — the names a library declares in the root namespace, as the `root: NAME` lines `scope_rewrite.py --qualify-roots` reads.

No Lean runs. Every module the factory compiled left a sidecar next to its olean (`<module>.olean.ranges.json`, TolerantBuild.lean: the name and the lines of every declaration of that
module that has a place in the source, read from the compiled environment), and `shard_pack.py merge` puts the sidecars of every shard, of this run and of the runs it reuses, under
`DIR/.lake/build/lib/lean`. A name there with ONE component is a declaration of the library in the root namespace: nothing in it tells libraries apart, a bare `X` reads as a second
`X` after `open Polynomial`, and the tree's merge queue refuses it once TENGOKU_ROOTS_REQUIRED is 1 (tengoku scripts/ci/roots_gate.py). bump-sharded.yml gives the file to
scope_rewrite.py on every cut, so that a first cut moves them to `Tengoku.<Library>` as a recut with `scope` always did.

The file lists every such name, the ones nobody wrote too (an anonymous instance's `instAddFoo`, a notation's `«term_∘_»`): scope_rewrite renames what a module's text declares and
reports the rest as `unresolved`, and the queue's scanner exempts exactly the names Lean generated. Names that start with `_` are Lean's own (`_example`, `_auxLemma`): left out.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SUFFIX = ".olean.ranges.json"
QUOTED = r"«[^»\n]*»"
ATOMIC = re.compile(rf"(?:{QUOTED}|[^.«»\s])+")  # one component: plain characters and «quoted» stretches (which may hold dots and spaces), no dot outside quotes


def atomic(name: object) -> bool:
    """a Lean name with one component, as `Name.toString` writes it (`X`, `instAddFoo`, `«termℝ²»`, `«a.b»`), and not one of Lean's own (`_example`)"""
    return isinstance(name, str) and bool(ATOMIC.fullmatch(name)) and not name.startswith("_")


def roots_of(merged: Path) -> list[str]:
    """the atomic names of every sidecar under `merged`, sorted (the same file from the same shards: `finish` cuts the bundle `compose` cut)"""
    base = merged / ".lake" / "build" / "lib" / "lean"
    names: set[str] = set()
    for f in sorted(base.rglob("*" + SUFFIX)) if base.is_dir() else []:
        if f.is_symlink():  # an artifact is data from a job that compiled someone's code
            continue
        try:
            rows = json.loads(f.read_text(encoding="utf-8", errors="replace"))
        except json.JSONDecodeError:
            sys.exit(f"root_lines: {f} is not JSON: the sidecar of a compiled module is cut (re-run the shard that built it)")
        if not isinstance(rows, list):
            sys.exit(f"root_lines: {f} is not a list of [name, first line, last line]")
        for row in rows:
            # TolerantBuild.lean writes [name, first line, last line]: a row of another shape means the sidecar is not what the shard built, and a quietly shorter list would leave declarations unqualified
            if not (isinstance(row, list) and len(row) == 3 and isinstance(row[0], str) and all(isinstance(x, int) and not isinstance(x, bool) for x in row[1:])):
                sys.exit(f"root_lines: {f} has a row that is not [name, first line, last line]: {str(row)[:120]}")
            if atomic(row[0]):
                names.add(row[0])
    return sorted(names)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--merged", required=True, help="the merged shards (shard_pack.py merge --out)")
    ap.add_argument("--out", required=True, help="the file of `root: NAME` lines (written even when empty)")
    a = ap.parse_args(argv)
    names = roots_of(Path(a.merged))
    Path(a.out).write_text("".join(f"root: {n}\n" for n in names), encoding="utf-8")
    print(f"root_lines: {len(names)} declaration(s) of the library are in the root namespace" + (f": {', '.join(names[:20])}" + (" …" if len(names) > 20 else "") if names else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
