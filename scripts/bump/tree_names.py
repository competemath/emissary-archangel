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

import lean_names

NAME = re.compile(r'"name":\s*"([^"]+)"')


def tree_names(root: Path, lib: str) -> set[str]:
    names: set[str] = set()
    for tier in ("trusted", "intake"):
        for f in sorted((root / "data" / tier).glob("**/*.jsonl")):
            # the gate's own exclusion, to the letter (intake_check.py: `f.stem != lib and f.parent.name != lib`): the library's records are what the bundle translates. A name the gate counts
            # that this list left out would let a module through that the gate then refuses; the part files are `.json` (parts/NNN.json), which the glob does not read
            if f.stem == lib or f.parent.name == lib:
                continue
            names.update(NAME.findall(f.read_text(errors="replace")))
    return names


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def tree_decls(root: Path, lib: str) -> set[str]:
    """The Lean names the other namespaces of the tree declare (`Tengoku/<Ns>/**/*.lean`, the seed and the library's own namespace left out): a module of the bundle that declares one
    of them cannot be imported with it ('environment already contains')."""
    out: set[str] = set()
    own = pascal(lib)
    for f in sorted((root / "Tengoku").glob("*/**/*.lean")):
        ns = f.relative_to(root / "Tengoku").parts[0]
        if ns == own or ns == "Seed":
            continue
        out |= lean_names.names(f.read_text(errors="replace"))
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, help="a checkout of tengoku with data/trusted and data/intake")
    ap.add_argument("--lib", required=True, help="the library key: its own files are left out")
    ap.add_argument("--out", required=True)
    ap.add_argument("--decls-out", default="", help="also write the Lean names the other namespaces of the tree declare (one per line) for bundle.py compose --tree-decls")
    a = ap.parse_args(argv)
    names = tree_names(Path(a.root), a.lib)
    if not names:
        raise SystemExit(f"no record name under {a.root}/data/{{trusted,intake}}: the checkout is wrong, and an empty list would let every clash through")
    Path(a.out).write_text("".join(n + "\n" for n in sorted(names)))
    print(f"{len(names)} record names the tree already has (library {a.lib} excluded)")
    if a.decls_out:
        decls = tree_decls(Path(a.root), a.lib)
        if not decls:
            raise SystemExit(f"no declaration under {a.root}/Tengoku: the checkout is wrong, and an empty list would let every clash through")
        Path(a.decls_out).write_text("".join(n + "\n" for n in sorted(decls)))
        print(f"{len(decls)} Lean names the other namespaces of the tree declare")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
