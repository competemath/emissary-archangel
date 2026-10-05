#!/usr/bin/env python3
"""bundle_rehead.py — give a finished bundle the header the tree has today, without a rebuild.

A bundle composed before tengoku moved its seed into Tengoku/Seed/ (competemath/tengoku#278) has the old header: the umbrella of
each seeded package under the tree's name for it (`Tengoku`, `Tengoku.Std`, `Tengoku.Tactic.Aesop`, `Tengoku.Meta.Qq`) and, for a library
that did not normalise its imports, specific seeded modules (`Tengoku.NumberTheory.NumberField.…`). None of those modules exists any more.
The root `Tengoku` re-exports the whole seed, so every import of the seed becomes the one `Tengoku` (`public` if any of them was, `import all`
plain, the other copies dropped): what `bundle.py compose` writes today, and right before and after the move. A single-job bump has its
bundle composed already, so this works on the bundle's files (a sharded run re-composes at a recut, so it needs no help).

Only the import lines of a file's header change; every other byte stays. Idempotent: a bundle with today's header is left alone.

  bundle_rehead.py --bundle DIR [--bundle DIR2 ...]   (each DIR is a composed bundle: DIR/Tengoku/<Library>/**.lean)
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tolerant_build as tb  # noqa: E402

# The seeded top-level modules of the tree: the stems of Tengoku/Seed/ when the seed moved (tengoku#278), without the Penrose `widget`
# folder (not a module). A library is never named like one of them: the tree has one namespace per top-level name.
SEED_TOPS = frozenset(
    "Algebra AlgebraicGeometry AlgebraicTopology Analysis CategoryTheory Combinatorics Computability Condensed Control Data Deprecated"
    " Dynamics FieldTheory Geometry GroupTheory InformationTheory Init Lean LinearAlgebra Logic MeasureTheory Meta ModelTheory NumberTheory"
    " Order Probability RepresentationTheory RingTheory Search SetTheory Std Tactic Testing Topology Util Widgets".split()
)
IMPORT = re.compile(r"^(?P<pre>[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+)(?P<all>all[ \t]+)?(?P<mod>" + tb.MODNAME + r")(?P<rest>.*)$")
KEYWORD = re.compile(r"(module|prelude)\b")


def seeded(mod: str) -> bool:
    parts = mod.split(".")
    return parts[0] == "Tengoku" and (len(parts) == 1 or parts[1] in SEED_TOPS)


def header_end(lines: list[str]) -> tuple[int, list[bool]]:
    """(the index after the header, and per line before it whether it is code and not a line of a block comment)."""
    depth, code = 0, []
    for i, ln in enumerate(lines):
        s = ln.strip()
        inside = depth > 0 or s.startswith("/-")
        if inside:
            depth = max(0, depth + s.count("/-") - s.count("-/"))
        elif s and not s.startswith("--") and not KEYWORD.match(s) and not IMPORT.match(ln.rstrip("\r")):
            return i, code
        code.append(not inside)
    return len(lines), code


def made_public(pre: str) -> str:
    """The prefix of an import line (`  meta import `) with `public` added and `private` removed."""
    indent = pre[: len(pre) - len(pre.lstrip())]
    mods = [w for w in pre.split()[:-1] if w not in ("public", "private")]
    return indent + " ".join(["public", *mods, "import"]) + " "


def rehead(text: str) -> str:
    """One `Tengoku` import where the header had seeded ones: at the first such line, `public` if any of them was (a private copy of an
    import that another line makes public adds nothing)."""
    lines = text.split("\n")
    end, code = header_end(lines)
    out: list[str] = []
    kept: tuple[int, str, str, str] | None = None  # (index in out, prefix, rest of the line, line ending) of the one Tengoku import
    for i, ln in enumerate(lines):
        cr = "\r" if ln.endswith("\r") else ""
        m = IMPORT.match(ln[: len(ln) - len(cr)]) if i < end and code[i] else None
        if not (m and seeded(m.group("mod"))):
            out.append(ln)
            continue
        pre = m.group("pre")
        if kept is None:
            kept = (len(out), pre, m.group("rest"), cr)
            out.append("")
        elif re.search(r"\bpublic\b", pre) and not re.search(r"\bpublic\b", kept[1]):
            kept = (kept[0], made_public(kept[1]), kept[2], kept[3])
    if kept is not None:
        out[kept[0]] = kept[1] + "Tengoku" + kept[2] + kept[3]
    return "\n".join(out)


def rehead_dir(bundle: Path) -> dict:
    """Rewrite the headers of every module under bundle/Tengoku/<Library>/; the library's own files only (not Deps.lean)."""
    changed = files = 0
    for f in sorted((bundle / "Tengoku").rglob("*.lean")):
        if f.is_symlink() or f.name == "Deps.lean":
            continue
        files += 1
        old = f.read_text(encoding="utf-8")
        new = rehead(old)
        if new != old:
            f.write_text(new, encoding="utf-8")
            changed += 1
    return {"files": files, "changed": changed}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", required=True)
    a = ap.parse_args()
    out = {}
    for b in map(Path, a.bundle):
        if not (b / "Tengoku").is_dir():
            sys.exit(f"{b}: not a bundle (no Tengoku/ folder)")
        out[b.name] = rehead_dir(b)
    print(json.dumps(out))


if __name__ == "__main__":
    main()
