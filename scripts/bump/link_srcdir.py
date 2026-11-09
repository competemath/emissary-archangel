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


def srcdirs_of(src: dict) -> list[str]:
    """The source folders of a library: `srcdir` is one folder or a list of them (a monorepo of Lake libraries, each with its own srcDir)."""
    v = src.get("srcdir") or []
    return [v] if isinstance(v, str) else list(v)


def _holds_lean(path: Path) -> bool:
    return path.suffix == ".lean" if path.is_file() else any(path.rglob("*.lean"))


def _make(project: Path, inside: Path, here_rel: PurePosixPath, target_rel: PurePosixPath, label: str, made: list[str]) -> None:
    """A link at `here_rel` (inside the project) to `target_rel` (relative to the folder the link is in), refused if it leads out of the project or takes a place something else has."""
    here = project.joinpath(*here_rel.parts)
    target = (here.parent / target_rel)
    if not target.resolve().is_relative_to(inside):  # a link in the repository (the folder itself, or a root under it) that leads out of the project
        raise ValueError(f"{label} resolves outside the project")
    if here.is_symlink() and here.readlink().as_posix() == target_rel.as_posix():
        made.append(here_rel.as_posix())  # a second run over the same clone
        return
    if here.exists() or here.is_symlink():
        raise ValueError(f"{here_rel} is both in the project and under a source folder ({label}): which one is the module?")
    here.symlink_to(target_rel.as_posix())
    made.append(here_rel.as_posix())


def link(project: Path, srcdirs: str | list[str], roots: list[str]) -> list[str]:
    """Link what each source folder holds at the top of the project: the roots, and every other top-level name that holds Lean files (a root imports the library's other folders). Returns
    what was linked. A source folder named after the module inside it (lean_lib Common, srcDir Common: Common.X is Common/Common/X.lean) cannot be linked at the top, which is that folder:
    the children of the module folder are linked inside it. Raises ValueError for a source folder that leaves the project, a name something else already has, or no root found."""
    srcdirs = [srcdirs] if isinstance(srcdirs, str) else srcdirs
    for root in roots:
        if "/" in root or "\\" in root or root in ("", ".", ".."):  # a root is one name at the top of the project: anything else would put the link somewhere else
            raise ValueError(f"root {root!r}: one name at the top of the project")
    if not srcdirs:
        raise ValueError("no source folder")
    named = {n for r in roots for n in (r, f"{r}.lean")}
    made: list[str] = []
    inside = project.resolve()
    for srcdir in srcdirs:
        parts = PurePosixPath(srcdir).parts
        if not parts or PurePosixPath(srcdir).is_absolute() or ".." in parts:
            raise ValueError(f"srcdir {srcdir!r}: a folder inside the Lake project")
        folder = project.joinpath(*parts)
        if not folder.is_dir():
            continue
        for child in sorted(folder.iterdir()):
            if child.name.startswith(".") or not (child.name in named or _holds_lean(child)):
                continue
            if len(parts) == 1 and child.is_symlink() and child.readlink().as_posix().startswith(parts[0] + "/"):
                continue  # one of this function's own links from an earlier run, inside a folder named after its module
            if len(parts) == 1 and child.name == parts[0]:  # the module folder has the source folder's own name
                for inner in sorted(child.iterdir()):
                    if not inner.name.startswith(".") and _holds_lean(inner):
                        _make(project, inside, PurePosixPath(parts[0], inner.name), PurePosixPath(child.name, inner.name), f"{srcdir}/{child.name}/{inner.name}", made)
                continue
            _make(project, inside, PurePosixPath(child.name), PurePosixPath(*parts, child.name), f"{srcdir}/{child.name}", made)
    if not named & set(made):
        raise ValueError(f"none of the roots {roots} is under {srcdirs}")
    return made


def main(argv: list[str]) -> int:
    key, project = argv[1], Path(argv[2])
    src = json.loads((Path(__file__).resolve().parents[2] / "sources.json").read_text())["sources"][key]
    if not srcdirs_of(src):
        return 0
    try:
        print(f"{key}: linked at the top of the project: {', '.join(link(project, srcdirs_of(src), src['roots']))}")
    except ValueError as e:
        print(f"::error::{key}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
