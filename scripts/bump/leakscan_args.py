#!/usr/bin/env python3
"""leakscan_args.py --key K --src PRUNED_SRC --roots R,R --out FILE — the arguments of TengokuLeak.lean for a library's pruned sources:
every module under the roots (`--module`), the roots as the library's own prefixes (`--prefix`), and the tree's name for the library
(`--tree-prefix Tengoku.<Library>`) so that the report is read in the tree's module names. NUL-separated: `xargs -0 -a FILE`."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bundle  # noqa: E402
import tolerant_build as tb  # noqa: E402


def args_for(key: str, src: Path, roots: list[str]) -> list[str]:
    mods = sorted(tb.module_files(src, roots))
    out: list[str] = []
    for m in mods:
        out += ["--module", m]
    for r in roots:
        out += ["--prefix", r]
    return out + ["--tree-prefix", f"Tengoku.{bundle.pascal(key)}"]


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--src", required=True)
    ap.add_argument("--roots", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    argv = args_for(a.key, Path(a.src), [r for r in a.roots.split(",") if r])
    Path(a.out).write_bytes(b"\0".join(x.encode() for x in argv) + b"\0")
    print(f"{argv.count('--module')} modules")
