#!/usr/bin/env python3
"""clash_recheck.py — the tree modules to build again before a name clash is believed.

  clash_recheck.py others CLASHES.txt     one module per line: the OTHER side of every `CLASH` line (the module that was already in the tree)

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
LINE = re.compile(r"^CLASH\t(?P<new>[^\t\n]+)\t(?P<other>[^\t\n]+)\t(?P<names>\d+)\t(?P<first>[^\n]*)$")
MODULE = re.compile(r"^Tengoku\.[^\s;&|$`\"'\\<>]+$")  # a module as Lean spells it (guillemets and all), no whitespace or shell character: the workflow passes it as one argument


def others(text: str, limit: int = LIMIT) -> list[str]:
    """The distinct modules on the second side of the `CLASH` lines, sorted. A line this does not understand is not a clash line (the program's own summary, Lean's warnings); a module name that is not a plain
    `Tengoku.…` name is refused."""
    found: set[str] = set()
    for line in text.splitlines():
        m = LINE.match(line)
        if not m:
            continue
        other = m.group("other")
        if not MODULE.fullmatch(other):
            raise SystemExit(f"not a module name: {other!r}")
        found.add(other)
    return sorted(found)[:limit]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="the tree modules to build again before a name clash is believed")
    sub = ap.add_subparsers(dest="cmd", required=True)
    o = sub.add_parser("others", help="one module per line: the other side of every CLASH line")
    o.add_argument("clashes", help="the output of ModuleClashes.lean")
    a = ap.parse_args(argv)
    mods = others(Path(a.clashes).read_text(encoding="utf-8", errors="replace"))
    if len(mods) == LIMIT:
        print(f"::warning::{LIMIT} or more modules to build again: only the first {LIMIT} are", file=sys.stderr)
    print("\n".join(mods))
    return 0


if __name__ == "__main__":
    sys.exit(main())
