#!/usr/bin/env python3
"""A Lake project whose modules live under a source folder (`srcDir` in its lakefile, sources.json `srcdir`): each root is linked at the top of the project.

Module `ClassFieldTheory.X` of classfieldtheory-yamaguchi is the file Lean4/ClassFieldTheory/X.lean. Everything else in the factory reads a module at the path its name spells,
so after these links `ClassFieldTheory/X.lean` is that file. The links are the only change: no file moves, the lakefile stays as upstream wrote it, Lake still builds from the
source folder, and an edit made through a link (the import rewrite of the bump) lands in the file Lake compiles.

usage: link_srcdir.py KEY PROJECT   (PROJECT: the Lake project; nothing to do for a library with no `srcdir`)
"""

import json
import sys
from pathlib import Path, PurePosixPath


def link(project: Path, srcdir: str, roots: list[str]) -> list[str]:
    """Link every root found under `srcdir`; returns what was linked. Raises ValueError for a source folder that leaves the project, or a root the project already has at the top."""
    parts = PurePosixPath(srcdir).parts
    if not parts or PurePosixPath(srcdir).is_absolute() or ".." in parts:
        raise ValueError(f"srcdir {srcdir!r}: a folder inside the Lake project")
    made = []
    inside = project.resolve()
    for root in roots:
        for name in (root, f"{root}.lean"):
            target = project.joinpath(*parts, name)
            if not target.exists():
                continue
            if not target.resolve().is_relative_to(inside):  # a link in the repository (the folder itself, or a root under it) that leads out of the project
                raise ValueError(f"{srcdir}/{name} resolves outside the project")
            here = project / name
            relative = PurePosixPath(*parts, name).as_posix()
            if here.is_symlink() and here.readlink().as_posix() == relative:
                made.append(name)  # a second run over the same clone
                continue
            if here.exists() or here.is_symlink():
                raise ValueError(f"{name} is both at the top of the project and under {srcdir}: which one is the module?")
            here.symlink_to(relative)
            made.append(name)
    if not made:
        raise ValueError(f"none of the roots {roots} is under {srcdir}")
    return made


def main(argv: list[str]) -> int:
    key, project = argv[1], Path(argv[2])
    src = json.loads((Path(__file__).resolve().parents[2] / "sources.json").read_text())["sources"][key]
    if not src.get("srcdir"):
        return 0
    try:
        print(f"{key}: linked at the top of the project: {', '.join(link(project, src['srcdir'], src['roots']))}")
    except ValueError as e:
        print(f"::error::{key}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
