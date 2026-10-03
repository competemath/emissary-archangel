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

  scope_rewrite.py --bundle DIR [--bundle DIR2 …] --leaks "<report lines, separated by newlines or ;>"
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
    out = []
    for part in re.split(r"[\n;]", text):
        m = LEAK.search(part)
        if m:
            out.append({"kind": m["kind"], "name": m["name"], "mod": m["mod"], "line": int(m["line"]) if m["line"] else None})
    return out


MODULE = re.compile(r"[\w.«»'!?]+")


def module_file(root: Path, mod: str) -> Path | None:
    """the bundle's file of a module; never one outside the bundle (a module name is input, and the bundle came from a build of the library's code)"""
    if not MODULE.fullmatch(mod) or ".." in mod:
        return None
    p = root.joinpath(*mod.split(".")).with_suffix(".lean")
    if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        return None
    return p


def short(name: str) -> str:
    n = name.split(".")[-1]
    return n[1:-1] if n.startswith("«") and n.endswith("»") else n


def localize(attr: str, text: str) -> str:
    """the first bare `attr` (not already `local`/`scoped`) in an attribute list or before `instance`: prefixed by `local `"""
    return re.sub(rf"(?<![\w.])(?<!local )(?<!scoped )\b{attr}\b", f"local {attr}", text, count=1)


def edit_declaration(lines: list[str], line: int, kind: str) -> bool:
    """`instance` at the declaration that starts at `line` (1-based), or `@[... simp ...]` on its attributes: one line each"""
    for i in range(max(0, line - 1), min(len(lines), line + 14)):
        s = lines[i]
        code = s.split("--", 1)[0]
        if kind == "instance":
            if re.search(r"(?<![\w.@])instance\b", code) and not re.search(r"\b(local|scoped)\s+instance\b", code) and "attribute" not in code:
                lines[i] = localize("instance", s) if "@[" not in code.split("instance")[0] else re.sub(r"(?<![\w.@])instance\b", "local instance", s, count=1)
                return lines[i] != s
        else:
            m = re.search(r"@\[([^\]]*)\]", code)
            if m and re.search(r"(?<![\w.])simp\b", m.group(1)) and not re.search(r"\b(local|scoped)\s+simp\b", m.group(1)):
                new_attrs = localize("simp", m.group(1))
                lines[i] = s[: m.start(1)] + new_attrs + s[m.end(1) :]
                return True
    return False


def edit_attribute_command(lines: list[str], name: str, kind: str) -> bool:
    """an `attribute [instance] … name …` (or `[simp]`) command that registers a declaration of another library"""
    n = short(name)
    word = "instance" if kind == "instance" else "simp"
    for i, s in enumerate(lines):
        if not ATTR_CMD.match(s):
            continue
        j = i
        while j + 1 < len(lines) and lines[j + 1].strip() and not lines[j + 1].lstrip().startswith(("theorem", "lemma", "def", "instance", "@[")):
            j += 1
        block = "\n".join(lines[i : j + 1])
        if re.search(rf"(?<![\w]){re.escape(n)}(?![\w'])", block) and re.search(rf"\[[^\]]*(?<![\w.])(?<!local )(?<!scoped ){word}\b", block):
            head = re.match(r"(\s*attribute\s*\[)([^\]]*)(\])", s)
            if head and re.search(rf"(?<![\w.]){word}\b", head.group(2)):
                lines[i] = head.group(1) + localize(word, head.group(2)) + head.group(3) + s[head.end() :]
                return lines[i] != s
    return False


def rewrite_file(path: Path, leaks: list[dict]) -> tuple[int, list[str]]:
    lines = path.read_text().split("\n")
    done, skipped = 0, []
    for lk in sorted(leaks, key=lambda x: -(x["line"] or 0)):  # bottom first; edits stay inside their line
        ok = edit_declaration(lines, lk["line"], lk["kind"]) if lk["line"] else edit_attribute_command(lines, lk["name"], lk["kind"])
        if ok:
            done += 1
        else:
            skipped.append(f"{lk['kind']} {lk['name']}")
    if done:
        text = "\n".join(lines)
        path.write_text(text + ("" if text.endswith("\n") else "\n") + f"-- Tengoku: {done} registration(s) of this module made local so they do not change other libraries (generated)\n")
    return done, skipped


def apply_bundle(root: Path, leaks: list[dict]) -> dict:
    by_mod: dict[str, list[dict]] = {}
    for lk in leaks:
        by_mod.setdefault(lk["mod"], []).append(lk)
    report = {"rewritten": 0, "skipped": [], "missing_modules": []}
    for mod, ls in sorted(by_mod.items()):
        f = module_file(root, mod)
        if not f:
            report["missing_modules"].append(mod)  # a leak of a module this bundle does not carry (the other bundle: strict vs proposed)
            continue
        done, skipped = rewrite_file(f, ls)
        report["rewritten"] += done
        report["skipped"] += [f"{mod}: {s}" for s in skipped]
    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", required=True)
    ap.add_argument("--leaks", required=True)
    a = ap.parse_args()
    leaks = parse(a.leaks)
    if not leaks:
        print(json.dumps({"rewritten": 0, "note": "no leak lines"}))
        return
    for b in a.bundle:
        root = Path(b)
        if root.exists():
            print(b, json.dumps(apply_bundle(root, leaks)))
    sys.exit(0)


if __name__ == "__main__":
    main()
