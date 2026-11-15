#!/usr/bin/env python3
"""clash_recheck.py — the tree modules to build again before a name clash is believed.

  clash_recheck.py others CLASHES.txt --new BUILT.txt     one module per line: the side of every `CLASH` line that is not new (the module that was already in the tree)

15 Nov 2026, flt-anthropic: the verify job seeds its tree from the newest published cache (`cache-20261114T1152Z`, "Lake rebuilds only what differs") and then builds only the NEW modules. ModuleClashes.lean
reads the names declared by EVERY olean in `.lake/build`, so a tree module that the build does not need keeps the olean the cache holds, from before its source changed. The libraries' root names were
qualified in the tree on 14 Nov 15:09 (tengoku #799, wave 4); the cache is from 11:52. The library's `FreyPackage.freyCurveInt` was reported as declared by `Tengoku.Flt.FLT.FreyCurve.Basic`, whose source
on main says `namespace Tengoku.Flt.FreyPackage` (`Tengoku.Flt.FreyPackage.freyCurveInt`): the olean was the old one. Four modules were refused, and with their importers 15,006 names stayed out of the tree
(2,014 of them listed under the Frey module).

The fix is to look again after the tree module is built: `lake build <the other module>` rebuilds it (and what it needs, if the cache is older) and the scan is run again. A name that is still declared by
both is a real clash; one that was only in the stale olean is gone. The scan reads the oleans, so the later steps (dups, the final clash scan) see the fresh ones without a change.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

LIMIT = 300  # modules built again at most: a pair per library the new modules vendor is a handful; more than this is another problem and is not built here
LINE = re.compile(r"^CLASH\t(?P<first>[^\t\n]+)\t(?P<second>[^\t\n]+)\t(?P<names>\d+)\t(?P<name>[^\n]*)$")
MODULE = re.compile(r"^Tengoku\.[^\t\r\n;&|$`\\<>]+$")  # a module as Lean spells it: `«…»` may hold a space, and the workflow passes every module as one array element; no tab, newline or shell character


def others(text: str, new: set[str] | frozenset[str] = frozenset(), limit: int = LIMIT) -> list[str]:
    """The distinct modules of the `CLASH` lines that are NOT new (`new`: the modules passed to ModuleClashes, out/built.txt), sorted: the tree modules. ModuleClashes.lean prints the later module of a pair first and
    the earlier second, and either may be the new one (it lists a pair when at least one of the two is new), so both sides are looked at and the new ones left out (cubic on #202). A line this does not
    understand is not a clash line (the program's own summary, Lean's warnings); a name that is not a plain `Tengoku.…` module is skipped with a warning, the others are still built."""
    found: set[str] = set()
    for line in text.splitlines():
        m = LINE.match(line)
        if not m:
            continue
        for side in (m.group("first"), m.group("second")):
            if side in new:
                continue
            if not MODULE.fullmatch(side):
                print(f"::warning::not a module name, not built again: {side!r}", file=sys.stderr)
                continue
            found.add(side)
    return sorted(found)[:limit]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="the tree modules to build again before a name clash is believed")
    sub = ap.add_subparsers(dest="cmd", required=True)
    o = sub.add_parser("others", help="one module per line: the other side of every CLASH line")
    o.add_argument("clashes", help="the output of ModuleClashes.lean")
    o.add_argument("--new", required=True, help="the modules that were passed to ModuleClashes.lean (out/built.txt), one per line: the new side of a pair is not built again")
    a = ap.parse_args(argv)
    new = {ln.strip() for ln in Path(a.new).read_text(encoding="utf-8", errors="replace").splitlines() if ln.strip()}
    mods = others(Path(a.clashes).read_text(encoding="utf-8", errors="replace"), new)
    if len(mods) == LIMIT:
        print(f"::warning::{LIMIT} or more modules to build again: only the first {LIMIT} are", file=sys.stderr)
    if mods:  # no module, no output at all: one newline would make `[ -s ]` true and the workflow would build a module named ""
        print("\n".join(mods))
    return 0


if __name__ == "__main__":
    sys.exit(main())
