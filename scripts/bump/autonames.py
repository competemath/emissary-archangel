#!/usr/bin/env python3
"""autonames.py — references to auto-generated instance names, which depend on the module they are compiled in.

Lean names an instance from its type (`instInhabitedNat`). When that name already exists in the environment it appends `_<root of the main module, first
letter lower-cased>` (checked on Lean 4.34.0-rc2: `instance : Inhabited Nat` compiled in module `virtual_sandbox` is `instInhabitedNat_virtual_sandbox`,
while a clash-free `instInhabitedIsnadProbeFoo` has no suffix). A library's module `FLT.Patching.X` therefore names such an instance `…_fLT`, and the
same file compiled in the tree (main module `Tengoku.Flt.FLT.Patching.X`, root `Tengoku`) names it `…_tengoku`. Code that refers to the instance by name
(`attribute [local instance] instFoo_fLT`, `@instFoo_fLT`, `open … in`) breaks when the module moves into the tree: `Unknown constant`. Found when the
merge queue ejected flt (2026-10-05): six modules, and what imports them, 138 theorems.

The rewrite is purely textual and exact: `<name starting with inst…>_<library root, first letter lower-cased>` becomes `<name>_tengoku`. Whether the
instance still clashes in the tree (and so still has a suffix) is for the tree's build to say; a module where it does not is dropped there, as before.

  autonames.py --bundle DIR [--bundle DIR2 …]     DIR/Tengoku/<Library>/<Root>/**.lean; <Root> is the library's own root module
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

TREE_ROOT = "Tengoku"
BOUNDARY_BEFORE = r"(?<![\w'.])"  # not inside a longer name
BOUNDARY_AFTER = r"(?![\w'])"


def suffix_of(root: str) -> str:
    """The suffix Lean adds for a main module whose root component is `root`: `FLT` is `fLT`, `Tengoku` is `tengoku`."""
    return root[:1].lower() + root[1:]


def name_pattern(root: str) -> re.Pattern[str]:
    # an optionally qualified name whose last component starts with `inst`, then `_` and the library's suffix, and nothing more of the name
    return re.compile(BOUNDARY_BEFORE + r"((?:[^\W\d][\w']*\.)*inst[\w']*?)_" + re.escape(suffix_of(root)) + BOUNDARY_AFTER)


def rewrite(text: str, root: str) -> tuple[str, int]:
    """The text with the library's suffix on instance names replaced by the tree's, and how many names changed."""
    if suffix_of(root) == suffix_of(TREE_ROOT):
        return text, 0
    return name_pattern(root).subn(lambda m: f"{m.group(1)}_{suffix_of(TREE_ROOT)}", text)


def root_of(rel: Path) -> str:
    """The library root module a file belongs to: the first component of its path under Tengoku/<Library>/ (`FLT/Patching/X.lean` is `FLT`)."""
    first = rel.parts[0]
    return first[: -len(".lean")] if first.endswith(".lean") else first


def rewrite_dir(bundle: Path) -> dict:
    changed = names = files = 0
    for lib in sorted(p for p in (bundle / TREE_ROOT).iterdir() if p.is_dir()):
        for f in sorted(lib.rglob("*.lean")):
            if f.is_symlink() or f.name == "Deps.lean":
                continue
            files += 1
            old = f.read_text(encoding="utf-8")
            new, n = rewrite(old, root_of(f.relative_to(lib)))
            if n:
                f.write_text(new, encoding="utf-8")
                changed += 1
                names += n
    return {"files": files, "changed": changed, "names": names}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", required=True)
    a = ap.parse_args()
    out = {}
    for b in map(Path, a.bundle):
        if not (b / TREE_ROOT).is_dir():
            sys.exit(f"{b}: not a bundle (no {TREE_ROOT}/ folder)")
        out[b.name] = rewrite_dir(b)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
