#!/usr/bin/env python3
"""adapters.py KEY LIB ROOTS — library-specific source rewrites that run before the bump builds the library.

Some libraries are written in a dialect of their own: commands that a package of the library defines (Compfiles: `problem`, `determine`,
`snip begin/end`, `problem_file`). The tree does not run a library's code (its allow-list lint refuses `macro`, `elab`, `syntax`), so
such a library could never be intaken: the module does not even parse without the library's command. When a command is, by the library's
own definition, a synonym of a plain Lean command, rewriting it is exact, and what the factory verifies and ships is plain Lean.

An adapter is a function of the source text that returns the source text, for ONE library, with its reason written down next to it
(the library's own source). Anything it does not recognise stays as it is (and fails the build or the lint like before): an adapter
never guesses. Positions are found in code only: comments and string literals are skipped.

  adapters.py KEY LIB ROOTS     rewrite the .lean files of LIB under ROOTS (comma list); prints how many files and rewrites
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


def code_mask(text: str) -> list[bool]:
    """mask[i] is True when text[i] is code: not inside a (nested) block comment, a line comment, a string or an escaped identifier."""
    n = len(text)
    mask = [True] * n
    i = 0
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            for k in range(i, min(j, n)):
                mask[k] = False
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = False
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = False
            i = j + 1
        elif text[i] == "«":
            j = text.find("»", i + 1)
            j = n if j < 0 else j + 1
            for k in range(i, j):
                mask[k] = False
            i = j
        else:
            i += 1
    return mask


# ── Compfiles (https://github.com/dwrensha/compfiles, ProblemExtraction.lean) ───────────────────────────────────────────────────
# `problem` is a synonym of `theorem` (it elaborates `theorem` with the same modifiers, name, signature and value; the rest only records
# text ranges for "problem extraction"); `determine` is a synonym of `abbrev`; `snip begin` / `snip end` and `problem_file …` only record
# metadata and ranges. None of them changes any declaration, so each is replaced by its plain Lean meaning.
COMPFILES_IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+ProblemExtraction(?:\.[\w.]*)?[ \t]*(?:\n|\Z)", re.M)
COMPFILES_SNIP = re.compile(r"^[ \t]*snip[ \t]+(?:begin|end)[ \t]*(?:\n|\Z)", re.M)
COMPFILES_FILE = re.compile(r"^[ \t]*problem_file\b", re.M)
MODS = r"(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec|unsafe)[ \t]+)*"
COMPFILES_KW = {
    "problem": re.compile(r"^([ \t]*" + MODS + r")problem(?=[ \t]+[^\s:(])", re.M),
    "determine": re.compile(r"^([ \t]*" + MODS + r")determine(?=[ \t]+[^\s:(])", re.M),
}
COMPFILES_REPLACEMENT = {"problem": "theorem", "determine": "abbrev"}


def adapt_compfiles(text: str) -> tuple[str, int]:
    mask = code_mask(text)
    edits: list[tuple[int, int, str]] = []
    for m in COMPFILES_IMPORT.finditer(text):
        if mask[m.start() + len(m.group(0)) - len(m.group(0).lstrip(" \t"))]:
            edits.append((m.start(), m.end(), ""))
    for m in COMPFILES_SNIP.finditer(text):
        if mask[m.start() + len(m.group(0)) - len(m.group(0).lstrip(" \t"))]:
            edits.append((m.start(), m.end(), ""))
    for m in COMPFILES_FILE.finditer(text):
        if not mask[m.end() - 1]:
            continue
        j = m.end()
        while j < len(text) and text[j] in " \t":
            j += 1
        if j < len(text) and text[j] == "{":  # `problem_file { tags := [...] }`: the structure instance, balanced, in code
            depth, k = 0, j
            while k < len(text):
                if mask[k] and text[k] == "{":
                    depth += 1
                elif mask[k] and text[k] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            j = k + 1
        end = text.find("\n", j)
        end = len(text) if end < 0 else end + 1
        if text[j:end].strip():  # something else follows on the line: not the command alone
            continue
        edits.append((m.start(), end, ""))
    for word, rx in COMPFILES_KW.items():
        for m in rx.finditer(text):
            kw = m.end(1)
            if mask[kw]:
                edits.append((kw, kw + len(word), COMPFILES_REPLACEMENT[word]))
    edits.sort(reverse=True)
    last = len(text) + 1
    done = 0
    for s, e, r in edits:
        if e > last:  # overlapping edits: keep the later one only
            continue
        text = text[:s] + r + text[e:]
        last = s
        done += 1
    return text, done


ADAPTERS = {"compfiles": adapt_compfiles}


def adapt_library(key: str, lib: Path, roots: list[str]) -> tuple[int, int]:
    """Rewrite the library's files in place; returns (files changed, rewrites)."""
    fn = ADAPTERS.get(key)
    if fn is None:
        return 0, 0
    files, total = 0, 0
    paths = []
    for r in roots:
        if (lib / f"{r}.lean").is_file():
            paths.append(lib / f"{r}.lean")
        if (lib / r).is_dir():
            paths += sorted((lib / r).rglob("*.lean"))
    for p in paths:
        old = p.read_text(encoding="utf-8")
        new, n = fn(old)
        if new != old:
            p.write_text(new, encoding="utf-8")
            files += 1
            total += n
    return files, total


if __name__ == "__main__":
    key, lib, roots = sys.argv[1], Path(sys.argv[2]), [r for r in sys.argv[3].split(",") if r]
    f, n = adapt_library(key, lib, roots)
    print(f"adapters[{key}]: {n} rewrites in {f} files" if key in ADAPTERS else f"adapters[{key}]: none registered")
