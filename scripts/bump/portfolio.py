#!/usr/bin/env python3
"""portfolio.py — give every theorem whose PROOF failed after a bump one more chance, with Lean's own automation.

A bumped library's remaining errors are mostly proofs that no longer close: a `simp` set that changed, a lemma whose
statement was reformulated, an `omega` that now needs a hint. The statement is untouched, the theorem's meaning is the same,
and Lean's general-purpose tactics (`grind`, `simp_all`, `aesop`, `omega`, `norm_num`, `positivity`, `linarith`, `decide`,
`tauto`) often prove the very same statement outright. This rewrites such a theorem's proof as

    theorem T <header> := by
      first
      | grind
      | simp_all
      | …

and the next build keeps whichever succeeds. Only the proof after the header's own `:=` is replaced, never the header, and
only for a theorem all of whose errors are of the proof-behaviour kind (unsolved goals, a tactic that made no progress or
failed); an error in the statement, an unknown name or a type mismatch is not something a hammer fixes.

Nothing here decides correctness: the kernel checks the new proof, and gate2_batch.py then compares the STATEMENT with the
original's. The rewritten proof is recorded in the repair report so it can be audited (a tactic proof replaces a human's).

  portfolio.py apply --lib DIR --log build.log --out report.json [--tactics grind,simp_all,...]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ERROR = re.compile(r"^error: (?:\./)*(\S+?\.lean):(\d+):(\d+): (.*)$")
# proof behaviour: the statement elaborated, the proof did not close
PROOF_ERROR = re.compile(
    r"unsolved goals|simp made no progress|`simp` made no progress|linarith failed|omega could not|`omega`|failed to prove|rewrite.* failed|Tactic `\w+` failed|"
    r"did not find (?:an )?instance of the pattern|motive is not type correct|ring failed|ring_nf failed|norm_num failed|positivity failed|aesop: failed|"
    r"`?simp`? failed|The rfl tactic failed|decide failed|nlinarith failed|failed to synthesize.*(?:Decidable)|No goals to be solved|error: no goals",
    re.I,
)
TACTICS = ["grind", "simp_all", "aesop", "omega", "norm_num", "positivity", "linarith", "decide", "tauto"]
COMMAND_START = re.compile(
    r"^(?:@\[|/--|/-!|/-|--|theorem\b|lemma\b|def\b|abbrev\b|instance\b|structure\b|class\b|inductive\b|opaque\b|axiom\b|example\b|namespace\b|section\b|end\b|open\b|variable\b|"
    r"universe\b|set_option\b|attribute\b|#|macro\b|macro_rules\b|syntax\b|notation\b|infix|prefix\b|postfix\b|elab\b|mutual\b|noncomputable\b|private\b|protected\b|"
    r"local\b|scoped\b|omit\b|include\b|deriving\b|export\b|initialize\b|unsafe\b|partial\b|nonrec\b|public\b|meta\b|import\b|module\b|compile_inductive\b|alias\b|irreducible_def\b|"
    r"lemma\b|proof_wanted\b|assert_not_exists\b|run_cmd\b|add_decl_doc\b)"
)
DECL_KW = re.compile(r"^(?:(?:private|protected|noncomputable|nonrec|public|meta)\s+)*(theorem|lemma)\s+")


def header_end(text: str, start: int = 0) -> int:
    """Index of the `:=` that ends a declaration's header: outside brackets, strings and comments; -1 if it has none (`| pat => …`)."""
    depth, i, n = 0, start, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        elif c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return i
        i += 1
    return -1


def blocks(lines: list[str]) -> list[tuple[int, int]]:
    """(first, last) 1-based lines of every top-level command: a column-0 line that starts a command ends the previous one."""
    starts = [i + 1 for i, ln in enumerate(lines) if ln and not ln[0].isspace() and COMMAND_START.match(ln)]
    out = []
    for k, s in enumerate(starts):
        e = (starts[k + 1] - 1) if k + 1 < len(starts) else len(lines)
        out.append((s, e))
    # a docstring or attribute line belongs to the declaration after it: merge a `/--`/`@[` block into the next one
    merged, carry = [], None
    for s, e in out:
        first = lines[s - 1]
        if first.startswith(("/--", "@[")) and (s == e or not DECL_KW.match(first)) and not re.search(r"\b(?:theorem|lemma|def)\b", first):
            carry = s if carry is None else carry
            continue
        merged.append((carry if carry is not None else s, e))
        carry = None
    return merged


def rewrite(lines: list[str], block: tuple[int, int], tactics: list[str]) -> tuple[list[str], str] | None:
    s, e = block
    text = "\n".join(lines[s - 1 : e])
    # the declaration keyword may follow doc comments / attributes / modifiers
    m = re.search(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*(theorem|lemma)[ \t]+", text, re.M)
    if not m:
        return None
    he = header_end(text, m.start())
    if he < 0:
        return None
    body = text[he + 2 :].strip()
    if body.startswith("by") is False and "\n" not in body and len(body) > 200:
        return None
    new_proof = ":= by\n  first\n" + "\n".join(f"  | {t}" for t in tactics)
    head = text[:he].rstrip()
    trailing = len(text) - len(text.rstrip("\n"))
    new = head + " " + new_proof + ("\n" * trailing)
    return lines[: s - 1] + new.split("\n")[: -trailing or None] + ([""] * trailing if trailing else []) + lines[e:], text[he:].strip()


def apply(a: argparse.Namespace) -> None:
    lib = Path(a.lib)
    tactics = [t for t in a.tactics.split(",") if t]
    by_file: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
    for ln in Path(a.log).read_text(errors="replace").splitlines():
        m = ERROR.match(ln)
        if m:
            by_file[m.group(1)].append((int(m.group(2)), int(m.group(3)), m.group(4)))
    report = {"files": 0, "theorems_rewritten": 0, "skipped": defaultdict(int), "rewritten": []}
    for f, errs in sorted(by_file.items()):
        path = lib / f
        if not path.exists():
            continue
        lines = path.read_text().split("\n")
        bl = blocks(lines)
        per_block: dict[tuple[int, int], list[str]] = defaultdict(list)
        for line, _, msg in errs:
            b = next((b for b in bl if b[0] <= line <= b[1]), None)
            if b:
                per_block[b].append(msg)
            else:
                report["skipped"]["error_outside_a_declaration"] += 1
        edits = []
        for b, msgs in per_block.items():
            if not all(PROOF_ERROR.search(m) for m in msgs):
                report["skipped"]["not_a_proof_error"] += 1
                continue
            edits.append(b)
        changed = False
        for b in sorted(edits, reverse=True):  # bottom first: earlier line numbers stay valid
            r = rewrite(lines, b, tactics)
            if r is None:
                report["skipped"]["no_header_end_or_not_a_theorem"] += 1
                continue
            lines, old = r
            report["rewritten"].append({"file": f, "line": b[0], "old_proof": old[:300]})
            report["theorems_rewritten"] += 1
            changed = True
        if changed:
            path.write_text("\n".join(lines))
            report["files"] += 1
    report["skipped"] = dict(report["skipped"])
    Path(a.out).write_text(json.dumps(report, indent=1))
    print(json.dumps({k: v for k, v in report.items() if k != "rewritten"}))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("apply")
    for f in ("lib", "log", "out"):
        p.add_argument(f"--{f}", required=True)
    p.add_argument("--tactics", default=",".join(TACTICS))
    args = ap.parse_args()
    apply(args)
