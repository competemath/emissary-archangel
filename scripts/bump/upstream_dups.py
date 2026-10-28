#!/usr/bin/env python3
"""upstream_dups.py — take out of a library the declarations that the target Mathlib now declares too.

A library written for an older Mathlib often carries compatibility shims: a spelling Mathlib did not have yet (stafford38-formal: `abbrev MvPolynomial.coeff`, "Compatibility spelling for sources using
`MvPolynomial.coeff m p`"). When Mathlib later adds the name, the shim fails with "`X` has already been declared", the module is dropped and every module that imports it with it: in the
2026-10-28 baseline ONE such shim took 372 of 436 modules down, and 365 were left out of the bundle.

The remedy is the one a person would make: delete the shim. This does it, deterministically, from the build log:

  * the error is `error: FILE:LINE:COL: `N` has already been declared`, and LINE is the line of a declaration (`abbrev`, `def`, `theorem` or `lemma`) whose name ends in N's last component;
  * nothing else of the library declares that name: no other declaration of the same last component in the library's own modules, and none earlier in the same file (then it is the library's own duplicate,
    which is not for this program to choose between, and it stays);
  * the declaration's whole block goes (its docstring, its attributes, its body, up to the next command), replaced by ONE comment line and blank lines, so that no other line of the file moves and
    every other position of the log stays valid;
  * `instance`, `structure`, `inductive`, `class` and `opaque` are never removed: other declarations are built on them in ways the name does not tell.

What it does not decide: whether Mathlib's declaration MEANS what the shim meant. Everything that mentioned the name now reads Mathlib's, and Gate 2 compares statements and definitions with the
original export (a drift is `name_collision` or a definition drift there), so a shim that differed from Mathlib's version costs the theorems that used it, never a wrong translation.

  upstream_dups.py --lib LIB --roots A,B --log build.log     prints what it removed as JSON
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "lint"))
import tolerant_build as tb  # noqa: E402
from lean_lex import code_only  # noqa: E402

ALREADY = re.compile(r"^(?:\S+\s+)?error: (?:\./)*(?P<path>\S+?\.lean):(?P<line>\d+):(?P<col>\d+): `(?P<name>[^`]+)` has already been declared", re.M)
MODIFIERS = r"(?:(?:private|protected|noncomputable|nonrec|public|meta|scoped|local|unsafe|partial)\s+)*"
ATTRS = r"(?:@\[[^\]\n]*\][ \t]*)*"  # attributes on the same line as the keyword: `@[simp] abbrev coeff …`
DECL = re.compile(r"^" + ATTRS + MODIFIERS + r"(?P<kind>abbrev|def|theorem|lemma|instance|structure|inductive|class|opaque|axiom|example)\b[ \t]*(?P<name>[^\s:({\[⦃]*)")
REMOVABLE = {"abbrev", "def", "theorem", "lemma"}
COMMAND_START = re.compile(r"^(?:@\[|" + MODIFIERS + r"(?:abbrev|def|theorem|lemma|instance|structure|inductive|class|opaque|axiom|example|namespace|end|section|open|variable|universe|set_option|attribute|noncomputable|mutual|deriving|export|alias|omit|include|macro_rules|macro|syntax|declare_syntax_cat|notation3|notation|infixl|infixr|infix|prefix|postfix|elab_rules|elab|builtin_initialize|initialize|register_\w+)(?![\w'.])|#)")


def last_component(name: str) -> str:
    return tb.split_mod(name)[-1]


def attribute_opener(lines: list[str], end: int) -> int | None:
    """The index of the line that opens the attribute whose closing `]` ends line end-1, or None. Only an attribute that ENCLOSES the lines in between counts: its bracket must stay open from the `@[`
    to that last `]` (a complete earlier attribute, or a list literal, is not it), and the lines between must continue it (indented), never start a command of their own."""
    for k in range(end - 1, max(-1, end - 9), -1):
        if lines[k].startswith("@["):
            if any(l[:1] not in (" ", "\t") and l.strip() for l in lines[k + 1 : end]):
                return None
            text = "\n".join(lines[k:end]).rstrip()
            depth = 0
            for i, ch in enumerate(text):
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                    if depth == 0 and i != len(text) - 1:
                        return None  # closed before the end: a complete attribute, and what follows it is something else
            return k if depth == 0 else None
    return None


def block_bounds(lines: list[str], code: list[str], decl: int) -> tuple[int, int]:
    """[start, end) of the block whose declaration keyword is on line index `decl`: its attribute lines and its docstring above, and everything up to the next command at column 0."""
    start = decl
    while start > 0:
        prev = lines[start - 1]
        if prev.startswith("@["):
            start -= 1
            continue
        if prev.rstrip().endswith("]") and not prev.startswith("@[") and code[start - 1].strip():  # the end of an attribute that goes over several lines: back to its opener
            k = attribute_opener(lines, start)
            if k is not None:
                start = k
                continue
        if prev.rstrip().endswith("-/") and not code[start - 1].strip():  # the end of a docstring: back to its opener
            k = start - 1
            while k >= 0 and not lines[k].lstrip().startswith("/--"):
                k -= 1
            if k >= 0 and lines[k].startswith("/--"):
                start = k
                continue
        break
    end = decl + 1
    while end < len(lines):
        raw, c = lines[end], code[end]
        if raw[:1] not in (" ", "\t", "") and (raw.startswith("/--") or raw.startswith("@[") or (c.strip() and COMMAND_START.match(c))):
            break
        end += 1
    return start, end


def declares(text_code: str, last: str, skip: range | None = None) -> bool:
    """Whether the code declares (abbrev/def/theorem/lemma/instance/structure/…) a name ending in `last`, outside the lines `skip`."""
    for i, line in enumerate(text_code.split("\n")):
        if skip is not None and i in skip:
            continue
        m = DECL.match(line)
        if m and m.group("name") and last_component(m.group("name")) == last:
            return True
    return False


def remove(lib: Path, roots: list[str], log: str) -> list[dict]:
    wanted: dict[str, dict[int, str]] = {}
    for m in ALREADY.finditer(log):
        wanted.setdefault(m.group("path"), {})[int(m.group("line"))] = m.group("name")
    if not wanted:
        return []
    own = tb.module_files(lib, roots)
    codes: dict[Path, str] = {}

    def code_of(p: Path) -> str:
        if p not in codes:
            codes[p] = code_only(p.read_text(errors="replace"))
        return codes[p]

    done: list[dict] = []
    for rel, errs in sorted(wanted.items()):
        path = lib / rel
        if not path.is_file():
            continue
        text = path.read_text(errors="replace")
        lines = text.split("\n")
        code = code_only(text).split("\n")
        if len(code) != len(lines):
            continue
        cuts: list[tuple[int, int, str, str]] = []
        for line_no, name in sorted(errs.items()):
            i = line_no - 1
            if i >= len(lines):
                continue
            m = DECL.match(code[i])
            if not m or m.group("kind") not in REMOVABLE or not m.group("name") or last_component(m.group("name")) != last_component(name):
                continue
            start, end = block_bounds(lines, code, i)
            last = last_component(name)
            # the library's own: another declaration of that name in this file (outside this block), or in any other module of the library
            if declares("\n".join(code), last, range(start, end)):
                continue
            if any(declares(code_of(f), last) for f in own.values() if f.resolve() != path.resolve()):
                continue
            cuts.append((start, end, name, m.group("kind")))
        if not cuts:
            continue
        for start, end, name, kind in sorted(cuts, reverse=True):
            note = f"-- [Emissary] removed `{name}`: the target Mathlib declares it too (a compatibility shim of the library)"
            lines[start:end] = [note] + [""] * (end - start - 1)
            done.append({"file": rel, "name": name, "kind": kind, "lines": [start + 1, end]})
        path.write_text("\n".join(lines))
    return sorted(done, key=lambda d: (d["file"], d["lines"][0]))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--roots", required=True)
    ap.add_argument("--log", required=True)
    a = ap.parse_args()
    done = remove(Path(a.lib), [r for r in a.roots.split(",") if r], Path(a.log).read_text(errors="replace"))
    json.dump(done, sys.stdout, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
