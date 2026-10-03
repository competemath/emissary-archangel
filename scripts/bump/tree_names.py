#!/usr/bin/env python3
"""tree_names.py TENGOKU_DIR [--lib KEY] --out FILE — the names the Tengoku tree already declares, one per line.

The tree's trusted and staging records are one record per declaration of the tree (the seeded Mathlib modules, every library already in it). A bundle
that declares one of these names cannot be imported next to it ("already declared"), and tengoku's intake gate refuses it
(scripts/ci/intake_check.py: "is already a record of the tree"). The bundler (bundle.py compose --tree-names) drops what clashes before it is cut.
The library's own records are left out, as the gate does (they are what the bundle translates).
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

NAME = re.compile(r'"name":\s*"((?:[^"\\]|\\.)*)"')


def tree_names(root: Path, lib: str = "") -> set[str]:
    names: set[str] = set()
    for tier in ("trusted", "staging"):
        d = root / "data" / tier
        if not d.exists():
            continue
        for f in list(d.glob("*.jsonl")) + list(d.glob("*/*.jsonl")):
            if lib and (f.stem == lib or f.parent.name == lib):
                continue
            with f.open(encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    m = NAME.search(line)
                    if m:
                        try:
                            names.add(json.loads(f'"{m.group(1)}"'))
                        except ValueError:
                            names.add(m.group(1))
    return names


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("tengoku")
    ap.add_argument("--lib", default="")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    ns = tree_names(Path(a.tengoku), a.lib)
    Path(a.out).write_text("".join(n + "\n" for n in sorted(ns)))
    print(f"{len(ns)} names the tree already declares")
