#!/usr/bin/env python3
"""notation_census.py — the global notation of the tree's libraries that leaks into every other library, read from the SOURCES (no Lean).

TengokuLeak.lean finds them in a compiled environment (`leak: notation …`); this reads the modules' text, for a tree that is not built (a checkout of tengoku's Tengoku/<Library>/):
a global `notation`/`prefix`/`infix`/`infixl`/`infixr`/`postfix`/`notation3`/`syntax`/`macro`/`elab` command (not `local`, not `scoped`) is a leak when

  - it is a term parser whose first token, at the same position (leading or trailing), is a token of a notation of core Lean or Mathlib (`prefix:80 "-" => complement`: every `-(3 * x)`
    on a real number is "Ambiguous term"), or
  - one of its atoms looks like an identifier and core Lean and Mathlib do not have it as a token (`notation "v" => …`: `fun v => …` fails in every file). The first atom of a `tactic`
    parser is no token (the category reads identifiers there).

What core Lean and Mathlib have comes from a compiled environment, once (`seed-tokens.json`: `keys` "leading -" / "trailing ∈", `idents`). The report lines are those of TengokuLeak.lean,
so scope_rewrite.py can make them scoped:

    leak: notation src@24 registered in Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Complement (declared at line 24)

  notation_census.py --tree CHECKOUT --seed seed-tokens.json [--lib NAME …] [--out leaks.txt] [--json census.json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

CMD = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*)(?P<mod>(?:local|scoped)[ \t]+)?"
    r"(?P<kw>prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab)(?![\w'.])(?P<rest>.*)$"
)
STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')
OPTION = re.compile(r"\s*(?::\s*\w+|\((?:name|priority|prec|kind)\s*:=[^)]*\))")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
READS_IDENTS = {"tactic", "conv"}  # the first atom of a parser of these categories is read as an identifier, not a token


def mask_comments(text: str) -> str:
    """the text with every comment blanked (same length and lines); string literals are kept"""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(text[i:j])
            i = j
        elif text.startswith("--", i):
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
        else:
            out.append(c)
            i += 1
    return "".join(out)


def cut_at_arrow(s: str) -> str:
    """the part of a command before its first `=>` that is not inside a string literal"""
    for m in re.finditer(r'"(?:[^"\\]|\\.)*"|=>', s):
        if m.group() == "=>":
            return s[: m.start()]
    return s


def parse_command(kw: str, rest: str):
    """(category, trailing, atoms) of a notation-family command, from the text after its keyword (continuation lines joined); None when it cannot be read"""
    s = rest
    while m := OPTION.match(s):
        s = s[m.end() :]
    spec = cut_at_arrow(s)
    cat = "term"
    if kw in ("syntax", "macro", "elab"):
        spec = re.sub(r"<=\s*\w+\??\s*$", "", spec.rstrip())
        m = re.search(r":\s*(\w+)\s*$", spec)
        if not m:
            return None
        cat, spec = m.group(1), spec[: m.start()]
    atoms = [a.strip() for a in STRING.findall(spec)]
    if not atoms:
        return None
    if kw in ("infix", "infixl", "infixr", "postfix"):
        trailing = True
    elif kw == "prefix":
        trailing = False
    else:
        trailing = not spec.lstrip().startswith('"')
    return cat, trailing, atoms


def census(text: str, seed: dict) -> list[dict]:
    """the leaking commands of one module's text: line (1-based, the keyword's), kw, category, atoms, reasons"""
    lines = mask_comments(text).split("\n")
    keys, idents = set(seed["keys"]), set(seed["idents"])
    out = []
    for i, ln in enumerate(lines):
        m = CMD.match(ln)
        if not m or m.group("mod"):
            continue
        rest = m.group("rest")
        j = i + 1
        while j < len(lines) and j < i + 6 and lines[j][:1] in " \t" and lines[j].strip():
            rest += " " + lines[j].strip()
            j += 1
        parsed = parse_command(m.group("kw"), rest)
        if not parsed:
            continue
        cat, trailing, atoms = parsed
        why = []
        key = ("trailing " if trailing else "leading ") + atoms[0]
        if cat == "term" and key in keys:
            why.append(f"token: {key}")
        words = atoms[1:] if (cat in READS_IDENTS and not trailing) else atoms
        for w in words:
            if IDENT.fullmatch(w) and w not in idents:
                why.append(f"word: {w}")
        if why:
            out.append({"line": i + 1, "kw": m.group("kw"), "category": cat, "atoms": atoms, "why": why})
    return out


def libraries(tree: Path, only: list[str]) -> list[Path]:
    root = tree / "Tengoku"
    skip = {"Seed"}
    return [d for d in sorted(root.iterdir()) if d.is_dir() and d.name not in skip and (not only or d.name in only)]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True)
    ap.add_argument("--seed", required=True)
    ap.add_argument("--lib", action="append", default=[], help="only this library's namespace (Tengoku/<NAME>)")
    ap.add_argument("--out")
    ap.add_argument("--json")
    a = ap.parse_args()
    seed = json.loads(Path(a.seed).read_text())
    tree = Path(a.tree)
    found, lines = [], []
    for lib in libraries(tree, a.lib):
        for f in sorted(lib.rglob("*.lean")):
            if f.is_symlink():
                continue
            mod = ".".join(f.relative_to(tree).with_suffix("").parts)
            for rec in census(f.read_text(encoding="utf-8", errors="replace"), seed):
                found.append({"module": mod, "path": str(f.relative_to(tree)), **rec})
                lines.append(f"leak: notation src@{rec['line']} registered in {mod} (declared at line {rec['line']})")
    if a.out:
        Path(a.out).write_text("\n".join(lines) + ("\n" if lines else ""))
    if a.json:
        Path(a.json).write_text(json.dumps(found, ensure_ascii=False, indent=1))
    print(f"notation census: {len(found)} leaking commands in {len({r['module'] for r in found})} modules", file=sys.stderr)
    for r in found:
        print(f"{r['module']}:{r['line']}: {r['kw']} {r['atoms']} -> {'; '.join(r['why'])}")


if __name__ == "__main__":
    main()
