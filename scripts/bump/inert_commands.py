#!/usr/bin/env python3
"""inert_commands.py — take out of a text the commands that say nothing about its theorems and that the tree's content lint refuses.

A source library's file is full of lines for its author: `#print axioms foo` after a theorem, `#check`, `#eval`, `set_option linter.unusedVariables false`. The tree refuses a record that
carries any of them (scripts/bump/lint/allowlist.py: "no # commands in a record", set_option only from the allow-list), so the mechanical pass used to send every entry of such a file
to the agent without compiling it (2026-10-27, stafford38-formal: 2,089 of 2,467 entries, 1,407 of them for `#print axioms` alone) although the theorem itself was fine.

What is removed, and why it cannot change what a theorem says:

  * a `#`-command that PRINTS, CHECKS or MEASURES (`#print`, `#check`, `#eval`, `#reduce`, `#synth`, `#find`, `#exit`, `#help`, `#lint`, `#time`, `#guard…`, `#adaptation_note`, …): it
    writes a message and declares nothing a theorem could name. Only a command that starts a line at column 0 is removed, with the indented lines that continue it; one in the middle of a
    line, or inside a proof, is left and the lint keeps refusing it (an honest refusal, never a guess).
  * `#guard_msgs … in` wraps the next command: only that line goes, not the command it wraps.
  * `set_option linter.X v` (a line of its own, or `set_option linter.X v in`) for an option that is NOT on the allow-list: a linter option decides which WARNINGS are printed. It does not
    change how anything elaborates. (An option that is on the allow-list stays, and so does every other `set_option`: `maxHeartbeats` and `autoImplicit` DO change what compiles.)

Everything else is left exactly as it was: the text is edited by whole lines (or, for `set_option … in`, that phrase), comments and strings are never read as code (lean_lex.code_only), and the
function reports each removal so that the record can say what was done. It decides nothing about whether the text is right: the compiler and Gate 2 do, on the edited bytes.

  repair(text, allowed_options) -> (new_text, [{"line": 12, "kind": "#print", "text": "#print axioms foo"}, …])
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "lint"))
from lean_lex import code_only  # noqa: E402

# Commands that only write a message. `#adaptation_note` records a note for the next Mathlib bump; `#guard_msgs in` wraps the next command and checks its messages.
INERT_HASH = (
    "print", "check", "check_failure", "eval", "reduce", "synth", "exit", "help", "find", "lint", "time", "guard", "guard_expr", "guard_msgs",
    "adaptation_note", "count_heartbeats", "explode", "leansearch", "loogle", "moogle", "min_imports", "long_names", "sample", "exec",
)
_HASH_LINE = re.compile(r"#(" + "|".join(INERT_HASH) + r")(?![\w'!?])")
_LINTER_SET = re.compile(r"set_option[ \t]+(linter\.[\w.]+)[ \t]+(?:true|false)\b")
_IN = re.compile(r"[ \t]+in\b")
_LINTER_IN = re.compile(r"set_option[ \t]+(linter\.[\w.]+)[ \t]+(?:true|false)[ \t]+in\b")


def repair(text: str, allowed_options: set[str]) -> tuple[str, list[dict]]:
    lines = text.split("\n")
    code = code_only(text).split("\n")
    if len(code) != len(lines):  # the lexer keeps every newline; if it ever did not, change nothing rather than guess
        return text, []
    out: list[str] = []
    removed: list[dict] = []
    i = 0
    while i < len(lines):
        line, cl = lines[i], code[i]
        m = _HASH_LINE.match(cl)
        if m:  # the pattern is anchored at column 0
            j = i + 1
            # `#guard_msgs … in` WRAPS the command after it: only the wrapper line goes, never what it wraps (an indented declaration below it is not its continuation)
            wrapper = m.group(1) == "guard_msgs" and cl.rstrip().endswith(" in")
            while not wrapper and j < len(lines) and lines[j][:1] in (" ", "\t") and code[j].strip():
                j += 1
            removed.append({"line": i + 1, "kind": "#" + m.group(1), "text": " ".join(s.strip() for s in lines[i:j])[:200]})
            i = j
            continue
        s = _LINTER_SET.match(cl.lstrip()) if cl.strip() else None
        if s and s.group(1) not in allowed_options:
            rest = cl.lstrip()[s.end():]
            if not rest.strip():  # the whole line is the option (a trailing comment is blank in `code`)
                removed.append({"line": i + 1, "kind": "set_option " + s.group(1), "text": line.strip()[:200]})
                i += 1
                continue
            if _IN.match(rest):
                # the phrase is FOUND in the code line (so that a look-alike in a comment is never taken for it) and cut out of the ORIGINAL line (the code line has its strings blanked, so what
                # follows the phrase must come from the original); the two must agree on what is at that place
                phrase = _LINTER_IN.search(cl)
                if phrase and phrase.group(1) == s.group(1) and line[phrase.start():phrase.end()] == phrase.group(0):
                    removed.append({"line": i + 1, "kind": "set_option " + s.group(1) + " in", "text": line.strip()[:200]})
                    keep = line[: phrase.start()] + line[phrase.end():].lstrip(" \t")
                    if keep.strip():
                        out.append(keep)
                    i += 1
                    continue
        out.append(line)
        i += 1
    return "\n".join(out), removed


if __name__ == "__main__":
    import json

    allowed = set(json.loads((HERE / "lint" / "allowed-options.json").read_text())["allowed"])
    new, rem = repair(sys.stdin.read(), allowed)
    json.dump({"text": new, "removed": rem}, sys.stdout)
