#!/usr/bin/env python3
"""scope_rewrite.py — make what a library registers for other libraries' types local to the module that registers it.

Once the tree is imported as one, a GLOBAL instance or simp lemma that mentions nothing of its own library changes how every other
library's statements elaborate (formal-mathfin's `attribute [instance] Matrix.linftyOpNormedAddCommGroup` makes the norm of every matrix
the L-infinity operator norm; compfiles' `Coe (ℕ × ℕ) (ℤ × ℤ)` is a silent coercion everywhere). The merge queue's `tengoku-leakscan` lists
them, with positions, from the compiled environment:

    leak: instance Imo1977P2.instCoeForallIntForallReal registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 34)
    leak: instance Matrix.linftyOpNormedAddCommGroup registered in Tengoku.X.Y (declared in Tengoku.Analysis.Matrix.Normed: an `attribute` command ...)
    leak: simp Imo1979P6.Walk.take_append registered in Tengoku.Compfiles.Compfiles.Imo1979P6 (declared at line 62)

This turns each of those into `local` (`instance` -> `local instance`, `@[simp]` -> `@[local simp]`, `attribute [instance] X` ->
`attribute [local instance] X`) in the bundle's module. It edits inside lines and never adds one, so the positions of the report stay valid;
a note is appended at the end of each changed file. Nothing is trusted: the tree's build of the rewritten bundle decides whether a
module still compiles (a later module of the library that used the instance fails and is dropped, as any module that does not build).

  scope_rewrite.py [--bundle DIR …] [--pruned DIR …] --leaks "<report lines, separated by newlines or ;>"
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

LEAK = re.compile(
    r"leak:\s+(?P<kind>instance|simp)\s+(?P<name>\S+)\s+registered in\s+(?P<mod>\S+)"
    r"(?:\s+\(declared at line (?P<line>\d+)\)|\s+\(declared in (?P<other>\S+?):)?"
)
ATTR_CMD = re.compile(r"^\s*attribute\s*\[")


def parse(text: str) -> list[dict]:
    # every `leak:` entry of the text, whatever separates them (newlines, `;`, or the single line a log flattens them to)
    return [
        {"kind": m["kind"], "name": m["name"], "mod": m["mod"], "line": int(m["line"]) if m["line"] else None}
        for m in LEAK.finditer(text)
    ]


PART = r"«[^»/\\]*»|[^.«»/\\\s]+"
MODULE_NAME = re.compile(rf"(?:{PART})(?:\.(?:{PART}))*")


def parts_of(mod: str) -> list[str] | None:
    """the components of a module name (`«1102.4662»` is one), or None for anything that is not a plain module name"""
    if not MODULE_NAME.fullmatch(mod):
        return None
    parts = [m.group(0).strip("«»") for m in re.finditer(PART, mod)]
    return None if any(p in ("", ".", "..") for p in parts) else parts


def module_file(root: Path, mod: str, skip: int = 0) -> Path | None:
    """the file of a module in a bundle (`Tengoku/<Library>/…`) or, with skip=2, in the library's own layout (the leading `Tengoku.<Library>`
    dropped); never a file outside the root (a module name is input, and the files came from a build of the library's code)"""
    parts = parts_of(mod)
    if parts is None or len(parts) <= skip:
        return None
    p = root.joinpath(*parts[skip:]).with_suffix(".lean")
    if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        return None
    return p


def short(name: str) -> str:
    n = name.split(".")[-1]
    return n[1:-1] if n.startswith("«") and n.endswith("»") else n


def mask(text: str) -> str:
    """the text with every comment (line, nested block, doc) and string literal blanked to spaces: same length and same columns, so a word
    found in the mask is code, and its position is the position in the text"""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


class Lines:
    """a file as lines, with the mask of each; an edit goes into both so that later edits find their columns"""

    def __init__(self, text: str):
        self.text, self.code = text.split("\n"), mask(text).split("\n")

    def insert(self, i: int, col: int, word: str) -> None:
        self.text[i] = self.text[i][:col] + word + self.text[i][col:]
        self.code[i] = self.code[i][:col] + word + self.code[i][col:]


NOT_LOCAL = r"(?<!local )(?<!scoped )"


def edit_declaration(f: Lines, line: int, kind: str) -> str:
    """`instance` of the declaration that starts at `line` (1-based; the range includes its doc comment and attributes), or the `simp` of an
    `@[...]` on it: "edited", "already" when it is local/scoped already, "missing" when it is not found"""
    for i in range(max(0, line - 1), min(len(f.text), line + 14)):
        code = f.code[i]
        col = None
        if kind == "instance":
            if ATTR_CMD.match(code):
                continue
            if re.search(r"\b(?:local|scoped)\s+instance\b", code):
                return "already"
            m = re.search(rf"(?<![\w.]){NOT_LOCAL}\binstance\b", code)
            col = m.start() if m else None
        else:
            for attrs in re.finditer(r"@\[([^\]]*)\]", code):
                if re.search(r"\b(?:local|scoped)\s+simp\b", attrs.group(1)):
                    return "already"
                hit = re.search(rf"(?<![\w.]){NOT_LOCAL}\bsimp\b", attrs.group(1))
                if hit:
                    col = attrs.start(1) + hit.start()
                    break
        if col is not None:
            f.insert(i, col, "local ")
            return "edited"
    return "missing"


def edit_attribute_command(f: Lines, name: str, kind: str) -> str:
    """an `attribute [instance] … name …` (or `[simp]`) command that registers a declaration of another library"""
    n = short(name)
    word = "instance" if kind == "instance" else "simp"
    for i, s in enumerate(f.code):
        if not ATTR_CMD.match(s):
            continue
        j = i
        while j + 1 < len(f.code) and f.code[j + 1].strip() and not f.code[j + 1].lstrip().startswith(("theorem", "lemma", "def", "instance", "@[")):
            j += 1
        block = "\n".join(f.code[i : j + 1])
        if not re.search(rf"(?<![\w]){re.escape(n)}(?![\w'])", block):
            continue
        head = re.match(r"(\s*attribute\s*\[)([^\]]*)(\])", s)
        if not head:
            continue
        if re.search(rf"\b(?:local|scoped)\s+{word}\b", head.group(2)):
            return "already"
        hit = re.search(rf"(?<![\w.]){NOT_LOCAL}\b{word}\b", head.group(2))
        if hit:
            f.insert(i, head.start(2) + hit.start(), "local ")
            return "edited"
    return "missing"


def rewrite_file(path: Path, leaks: list[dict]) -> tuple[int, list[str]]:
    text = path.read_text()
    f = Lines(text)
    done, skipped = 0, []
    for lk in sorted(leaks, key=lambda x: -(x["line"] or 0)):
        r = edit_declaration(f, lk["line"], lk["kind"]) if lk["line"] else edit_attribute_command(f, lk["name"], lk["kind"])
        if r == "edited":
            done += 1
        elif r == "missing":
            skipped.append(f"{lk['kind']} {lk['name']}")
    if done:
        new = "\n".join(f.text)
        path.write_text(new + ("" if new.endswith("\n") else "\n") + f"-- Tengoku: {done} registration(s) of this module made local so they do not change other libraries (generated)\n")
    return done, skipped


def apply_bundle(root: Path, leaks: list[dict], skip: int = 0) -> dict:
    by_mod: dict[str, list[dict]] = {}
    for lk in leaks:
        by_mod.setdefault(lk["mod"], []).append(lk)
    report = {"rewritten": 0, "skipped": [], "missing_modules": []}
    for mod, ls in sorted(by_mod.items()):
        f = module_file(root, mod, skip)
        if not f:
            report["missing_modules"].append(mod)  # a leak of a module this bundle does not carry (the other bundle: strict vs proposed)
            continue
        done, skipped = rewrite_file(f, ls)
        report["rewritten"] += done
        report["skipped"] += [f"{mod}: {s}" for s in skipped]
    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", default=[], help="a bundle directory (Tengoku/<Library>/… inside)")
    ap.add_argument("--pruned", action="append", default=[], help="a directory of the library's own layout (the factory's pruned sources)")
    ap.add_argument("--leaks", required=True)
    a = ap.parse_args()
    leaks = parse(a.leaks)
    if not leaks:
        print(json.dumps({"rewritten": 0, "note": "no leak lines"}))
        return
    for dirs, skip in ((a.bundle, 0), (a.pruned, 2)):
        for b in dirs:
            if Path(b).exists():
                print(b, json.dumps(apply_bundle(Path(b), leaks, skip)))


if __name__ == "__main__":
    main()
