#!/usr/bin/env python3
"""strip_attrs.py — leave out the attributes the tree does not allow, from the declarations of a bundle.

An attribute never changes what a declaration says (its type and value are the same with or without `@[circuit_norm]`); it registers the
declaration somewhere: a simp set, a tactic's lemma list, a code table. The tree's allow-list (scripts/bump/lint/allowlist.py, a copy of
tengoku's) refuses the attributes it does not know, because an attribute can register code of the record's to run later; a module that
carries one was lost with every theorem in it. Dropping the attribute keeps the declaration and loses only what the registration did:
a later proof that relied on it may no longer close, and the verification build (bundle.py check/refine) finds that and leaves the module out.

  `@[a, b, c]`             the attributes not on the allow-list are removed; `@[]` is removed whole
  `attribute [a, b] foo`   the same; a command left with no attribute is removed whole (to the next line that starts in column 0)

Comments and strings are skipped (adapters.code_mask). Only attributes the allow-list refuses are touched.
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "lint"))
sys.path.insert(0, str(HERE))
import allowlist  # noqa: E402
from adapters import code_mask  # noqa: E402


def _is_refused(name: str, full: str) -> bool:
    return name not in allowlist.ATTRIBUTES or (name == "aesop" and re.search(r"\btactic\b", full) is not None)


def strip_attributes(text: str) -> tuple[str, Counter]:
    """The text without the attributes the allow-list refuses, and how many of each were removed."""
    mask = code_mask(text)
    edits: list[tuple[int, int, str]] = []
    removed: Counter = Counter()
    for m in allowlist._ATTR_OPEN.finditer(text):
        start_kw = m.start() if m.group(0).startswith("@") else m.start() + len(m.group(0)) - len(m.group(0).lstrip(" \t"))
        if not mask[start_kw]:
            continue
        i, depth = m.end(), 1
        while i < len(text) and depth:
            if mask[i]:
                depth += {"[": 1, "]": -1}.get(text[i], 0)
            i += 1
        if depth:  # never closed: leave it, the lint will say what it says
            continue
        spans = _split(text, mask, m.end(), i - 1)
        gone = [(a, b) for a, b in spans if _refused_part(_code(text, mask, a, b))]
        if not gone:
            continue
        for a, b in gone:
            removed[_name(_code(text, mask, a, b))] += 1
        keep = [text[a:b].strip() for a, b in spans if (a, b) not in gone]
        if keep:
            edits.append((m.end(), i - 1, ", ".join(keep)))
        elif m.group(0).startswith("@"):  # `@[x] def …` -> `def …`; a line that was only the attribute goes whole
            end = i
            while end < len(text) and text[end] in " \t":
                end += 1
            if text[end : end + 1] == "\n" and text[: m.start()].rsplit("\n", 1)[-1].strip() == "":
                end += 1
            edits.append((m.start(), end, ""))
        else:  # `attribute [x] foo bar …`: the whole command, to the next line that starts in column 0
            nxt = re.compile(r"\n(?=\S)").search(text, i)
            edits.append((m.start(), nxt.start() + 1 if nxt else len(text), ""))
    edits.sort(reverse=True)
    last = len(text) + 1
    for s, e, r in edits:
        if e > last:
            continue
        text = text[:s] + r + text[e:]
        last = s
    return text, removed


def _code(text: str, mask: list[bool], a: int, b: int) -> str:
    """text[a:b] with everything that is not code (comments, strings) blanked."""
    return "".join(text[k] if mask[k] else " " for k in range(a, b))


def _split(text: str, mask: list[bool], a: int, b: int) -> list[tuple[int, int]]:
    """The comma-separated parts of text[a:b] as spans: only a comma in code, outside every bracket, separates two of them."""
    spans, start, depth = [], a, 0
    for k in range(a, b):
        if not mask[k]:
            continue
        depth += {"(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1}.get(text[k], 0)
        if text[k] == "," and depth == 0:
            spans.append((start, k))
            start = k + 1
    spans.append((start, b))
    return [(x, y) for x, y in spans if text[x:y].strip()]


def _name(code_part: str) -> str:
    w = code_part.strip().lstrip("-").split()
    while w and w[0] in ("scoped", "local"):
        w = w[1:]
    return w[0].rstrip("↓←!") if w else ""


def _refused_part(code_part: str) -> bool:
    name = _name(code_part)
    return bool(name) and _is_refused(name, code_part)


PORTFOLIO_TRACE = re.compile(r';\s*trace "PORTFOLIO-OK \w+"')


def strip_portfolio_traces(text: str) -> tuple[str, int]:
    """The portfolio (portfolio.py) retries a failed proof with `first | (all_goals T; done; trace "PORTFOLIO-OK T") | …`; the trace only counts which
    tactic closed what, and in a shipped module it would print a message on every build of the tree. Removed from the code (never from a string or a
    comment); the `first` block stays, so the proof is the one the verification build checked."""
    mask = code_mask(text)
    out, last, n = [], 0, 0
    for m in PORTFOLIO_TRACE.finditer(text):
        if mask[m.start()]:  # the `;` is code (not inside a comment or a string)
            out.append(text[last : m.start()])
            last, n = m.end(), n + 1
    out.append(text[last:])
    return "".join(out), n

