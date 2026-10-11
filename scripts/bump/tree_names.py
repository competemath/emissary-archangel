#!/usr/bin/env python3
"""tree_names.py — the record names the tengoku tree already has, for `bundle.py compose --tree-names`.

  tree_names.py --root TENGOKU_CHECKOUT --lib KEY --out names.txt

Exactly the set tengoku's intake gate (scripts/ci/intake_check.py) refuses a bundle theorem against: every `"name"` of the trusted records (`data/trusted/**/*.jsonl`) and of the
intake bundles already merged (`data/intake/**/*.jsonl`), except the library's own files (its earlier parts are what this bundle continues, not a clash). Staging and tentative
records are not in the tree and are not read. The files are data: they are matched with a regular expression and nothing in them is run.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

NAME = re.compile(r'"name":\s*"([^"]+)"')


def tree_names(root: Path, lib: str) -> set[str]:
    names: set[str] = set()
    for tier in ("trusted", "intake"):
        for f in sorted((root / "data" / tier).glob("**/*.jsonl")):
            if f.stem == lib or f.parent.name == lib:  # the gate's own exclusion: the library's records are what the bundle translates
                continue
            names.update(NAME.findall(f.read_text(errors="replace")))
    return names


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, help="a checkout of tengoku with data/trusted and data/intake")
    ap.add_argument("--lib", required=True, help="the library key: its own files are left out")
    ap.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    names = tree_names(Path(a.root), a.lib)
    if not names:
        raise SystemExit(f"no record name under {a.root}/data/{{trusted,intake}}: the checkout is wrong, and an empty list would let every clash through")
    Path(a.out).write_text("".join(n + "\n" for n in sorted(names)))
    print(f"{len(names)} record names the tree already has (library {a.lib} excluded)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
