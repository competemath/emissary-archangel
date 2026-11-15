#!/usr/bin/env python3
"""p2m_util.py — expand the shortcuts of a library's own `P2M/Util.lean` into plain Lean, so that a module can go to the tree without running the library's code.

The library flt-anthropic (anthropics/fermats-last-theorem, Lean 4.33) has one file, `P2M/Util.lean` (127 lines), that adds about ten commands and one tactic with `elab`: they run the library's own code
while a module compiles, which the tree's content lint refuses (`elab` can reach IO). 59,022 of the library's 60,478 modules import it; 15,006 declarations that passed Gate 2 stayed out of the tree
because of it (bump run 43686274801, 15 Nov 2026; 10,867 of them under this one root). What the shortcuts do, and what stands in for each (counts: the pinned commit aa2d8b34, every .lean file):

  p2m_exact_reverting @S.solution    29,513 uses in 29,512 files: every `Theorems/Thm_X.lean` is `theorem X <binders> : <statement> := by p2m_exact_reverting @_root_.P2MW.S_X.solution`. It reverts every
                                     hypothesis and elaborates the term against the result: the proof is `@S.solution b1 … bn`. Written out: `by exact @S.solution b1 … bn`, with the names of the binders
                                     (`_` for an instance binder with no name): the same proof term, no tactic of the library.
  p2m_open "A B~x~y"                 37,090 uses: `OpenDecl.simple A []`, `OpenDecl.simple B [x, y]` and the scoped entries of both: that is `open A` and `open B hiding x y`. A word `scoped` (the translator wrote
                                     `open scoped A` as "scoped A") names no namespace and does nothing. With ` in` after it: `open … in`.
  p2m_open_scoped "A B" [in]         5,623 uses: the scoped entries of A and B are activated and no name is opened: `open scoped A B [in]`.
  p2m_export "N" "a b c"             38,433 uses: aliases `<current namespace>.a` for `N.a` (or its private form), skipping a name that does not exist: `export N (a b c)` (283 uses have no N: dropped, see export_command).
  p2m_reactivate "A B"               66,151 uses: after a `namespace A … end A` closed, the scoped notations and instances of A are switched on again: `open scoped A B`.
  #p2m_type_eq(_warn) a b            34 uses: compare two types and print a message; declares nothing: removed (the tree's lint refuses every `#` command, as for `#print`, strip_attrs.py).
Left as they are, so that the module is not rewritten at all (it stays behind the import of P2M.Util, as before): p2m_alias (556 uses in 233 files: an alias under an exact name), p2m_export_all, p2m_ns, and a
theorem whose binders cannot be read. The import of `P2M.Util` is removed from a module only when nothing of it is left.

What a declaration SAYS never changes: no statement is touched (only the proof of a Theorems/ module, and commands that open names). The only risk is a module that no longer compiles (a name `export`
cannot find, an `exact` that does not unify), and the tree's own build of the module finds that (bundle.py verify): the module is left out, as before. Only code is touched (adapters.code_mask).
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from adapters import code_mask  # noqa: E402

UTIL = "P2M.Util"
IMPORT_UTIL = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+P2M\.Util[ \t]*(?:\n|$)", re.M)
KEYWORD = re.compile(r"(?<![\w.#'])(#?p2m_[a-z_]+)\b")
STR = r'"((?:[^"\\\n]|\\.)*)"'
WS = r"[ \t\r\n]*"
UNSUPPORTED = ("p2m_alias", "p2m_export_all", "p2m_ns")
INERT = ("#p2m_type_eq", "#p2m_type_eq_warn")
SCOPED_WORD = "scoped"


def words(s: str) -> list[str]:
    return [w for w in s.split(" ") if w]


def open_commands(arg: str, in_: bool) -> str:
    """`p2m_open "A B~x~y"` as plain Lean: one `open` per word, on one line (no line is added or moved), each with `in` after it when the original had it."""
    out = []
    for w in words(arg):
        head, *hidden = w.split("~")
        if head == SCOPED_WORD and not hidden:
            continue
        hidden = [h for h in hidden if h]
        out.append(f"open {head}" + (" hiding " + " ".join(hidden) if hidden else "") + (" in" if in_ else ""))
    return " ".join(out)


def scoped_commands(arg: str, in_: bool) -> str:
    heads = [w.split("~")[0] for w in words(arg)]
    heads = [h for h in heads if h]
    return ("open scoped " + " ".join(heads) + (" in" if in_ else "")) if heads else ""


def export_command(ns: str, names: str) -> str:
    """`export N (a b)`. With no namespace (`p2m_export "" "A.b"`, 283 uses in 135 files: the full names are given) there is no plain command that makes the alias `<current namespace>.A.b` (an `export` inside
    `namespace <current>.A` would name the namespace `A` it is inside of), so nothing is written: the alias only changes what a name resolves to inside the file, and a module that needed it does not
    compile in the tree and stays out as before."""
    if not ns or not words(names):
        return ""
    return f"export {ns} ({' '.join(words(names))})"


# a binder group of a theorem header: ( … ) { … } [ … ] ⦃ … ⦄, nested brackets counted; strings and comments do not occur in the headers of the Theorems files
OPEN, CLOSE = "({[⦃", ")}]⦄"


def header_binders(text: str, name_end: int) -> tuple[list[str], int] | None:
    """The argument list for `@solution`: one entry per binder name (`_` for an instance binder with no name), and the index of the `:` that ends the binders. None when something here is not understood."""
    i, n = name_end, len(text)
    args: list[str] = []
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
        elif c == ":" and not text.startswith(":=", i):
            return args, i
        elif text.startswith(".{", i):  # universe parameters of the name
            j = text.find("}", i)
            if j < 0:
                return None
            i = j + 1
        elif c in OPEN:
            depth, j = 0, i
            colon = -1
            while j < n:
                d = text[j]
                if d in OPEN:
                    depth += 1
                elif d in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                elif d == ":" and depth == 1 and colon < 0 and not text.startswith(":=", j):
                    colon = j
                j += 1
            if j >= n:
                return None
            group = text[i + 1 : colon if colon >= 0 else j]
            if colon < 0:
                if c != "[":  # `(x)` or `{x}` with no type: not seen, not guessed
                    return None
                args.append("_")  # `[Foo α]`: an instance with no name
            else:
                names = group.split()
                if not names or any(not re.fullmatch(r"[^\s()\[\]{}⦃⦄:,.]+(?:\.[^\s()\[\]{}⦃⦄:,.]+)*", x) for x in names):
                    return None
                typ = " ".join(text[colon + 1 : j].split())
                if "_" in names and (c != "[" and ("‹" in typ or "›" in typ)):  # `‹T›` does not nest
                    return None
                # `(_ : T)`: a hypothesis with no name, found by its type (`‹T›`); an instance binder `[_ : C]` is found by instance search
                args.extend(("_" if c == "[" else f"‹{typ}›") if x == "_" else x for x in names)
            i = j + 1
        else:
            return None
    return None


THEOREM = re.compile(r"(?m)^[ \t]*(?:(?:private|protected|nonrec)[ \t]+)*theorem\s+([^\s:({\[⦃.]+(?:\.[^\s:({\[⦃.]+)*)")
EXACT = re.compile(r"\bby[ \t]+p2m_exact_reverting[ \t]+(@_root_\.P2MW\.[A-Za-z0-9_'.]+\.solution)[ \t]*$", re.M)


def expand_exact(text: str, mask: list[bool]) -> tuple[str, str]:
    """(`text` with the FIRST `by p2m_exact_reverting @…solution` that is code written out, "done"); (`text`, "none") when there is none; (`text`, "fail") when there is one that cannot be: no theorem header
    before it, or a binder this does not read. (A module with several theorems has several; a comment that names the tactic is not one.)"""
    m = next((x for x in EXACT.finditer(text) if mask[x.start()]), None)
    if m is None:
        return text, "none"
    heads = [h for h in THEOREM.finditer(text, 0, m.start()) if mask[h.start()]]
    if not heads:
        return text, "fail"
    parsed = header_binders(text, heads[-1].end())
    if parsed is None or parsed[1] > m.start():
        return text, "fail"
    args, _ = parsed
    return text[: m.start()] + "by exact " + m.group(1) + "".join(" " + a for a in args) + text[m.end() :], "done"


def rewrite_module(text: str) -> tuple[str, Counter, Counter]:
    """(the module with every shortcut it can expanded, what was expanded by kind, what is left by kind). The import of P2M.Util goes only when nothing is left."""
    done: Counter = Counter()
    left: Counter = Counter()
    if UTIL not in text and "p2m_" not in text:
        return text, done, left
    mask = code_mask(text)
    edits: list[tuple[int, int, str]] = []
    for m in KEYWORD.finditer(text):
        if not mask[m.start()]:
            continue
        kw = m.group(1)
        end = m.end()
        if kw == "p2m_exact_reverting":
            continue  # a tactic, expanded below
        if kw in UNSUPPORTED:
            left[kw] += 1
            continue
        if kw in INERT:
            line_end = text.find("\n", end)
            line_end = len(text) if line_end < 0 else line_end
            a = re.compile(rf"{WS}\S+{WS}\S+[ \t]*").match(text, end)
            if a is None or a.end() > line_end:
                left[kw] += 1
                continue
            start = m.start()
            ls = text.rfind("\n", 0, start) + 1
            stop = a.end()
            if text[ls:start].strip() == "" and text[stop:line_end].strip() == "":
                start, stop = ls, min(line_end + 1, len(text))  # the whole line goes
            edits.append((start, stop, ""))
            done[kw] += 1
            continue
        if kw in ("p2m_open", "p2m_open_scoped"):
            a = re.compile(rf"{WS}{STR}").match(text, end)
            if a is None:
                left[kw] += 1
                continue
            in_m = re.compile(r"[ \t]+in\b").match(text, a.end())
            in_ = in_m is not None
            new = (open_commands if kw == "p2m_open" else scoped_commands)(a.group(1), in_)
            edits.append((m.start(), in_m.end() if in_m else a.end(), new))
            done[kw] += 1
            continue
        if kw == "p2m_export":
            a = re.compile(rf"{WS}{STR}{WS}{STR}").match(text, end)
            if a is None:
                left[kw] += 1
                continue
            edits.append((m.start(), a.end(), export_command(a.group(1), a.group(2))))
            done[kw if a.group(1) else "p2m_export (no namespace, dropped)"] += 1
            continue
        if kw == "p2m_reactivate":
            a = re.compile(rf"{WS}{STR}").match(text, end)
            if a is None:
                left[kw] += 1
                continue
            edits.append((m.start(), a.end(), scoped_commands(a.group(1), False)))
            done[kw] += 1
            continue
        left[kw] += 1  # a p2m_ word this does not know
    out = text
    for s, e, new in sorted(edits, reverse=True):
        out = out[:s] + new + out[e:]
    while "p2m_exact_reverting" in out:
        out, status = expand_exact(out, code_mask(out))
        if status == "done":
            done["p2m_exact_reverting"] += 1
            continue
        if status == "fail":
            left["p2m_exact_reverting"] += 1
        break
    if any(k.group(1) == "p2m_exact_reverting" and code_mask(out)[k.start()] for k in KEYWORD.finditer(out)):  # a use of another shape: not guessed at
        left["p2m_exact_reverting"] += 1 if not left["p2m_exact_reverting"] else 0
    if left:  # something of the shortcuts cannot be written out: the module stays exactly as the library wrote it
        return text, Counter(), left
    return IMPORT_UTIL.sub("", out), done, left


def rewrite(texts: dict[str, str], imports: dict[str, list[str]]) -> tuple[dict[str, str], dict[str, list[str]], dict[str, int], dict[str, list[str]]]:
    """The pass compose makes (bundle.py, after grind_sets.rewrite): every module of `texts` written out (rewrite_module); what each changed module says about it, for its change notice; counts; and the
    imports of the modules that no longer import P2M.Util. The Util module itself leaves `texts` when no module imports it any more (it is the file the tree's lint refuses)."""
    out: dict[str, str] = {}
    changes: dict[str, list[str]] = {}
    stats: Counter = Counter()
    new_imports: dict[str, list[str]] = {}
    for mod, before in texts.items():
        after, done, left = rewrite_module(before)
        if left:
            stats["modules kept as they were"] += 1
        if after == before:
            out[mod] = before
            continue
        out[mod] = after
        stats["modules changed"] += 1
        n = sum(done.values())
        parts = [f"{v} `{k}`" for k, v in sorted(done.items())]
        dropped = bool(IMPORT_UTIL.search(before)) and not IMPORT_UTIL.search(after)
        if dropped:
            new_imports[mod] = [d for d in imports.get(mod, []) if d != UTIL]
        what = []
        if n:
            what.append(f"wrote out {n} shortcut(s) of the library's `{UTIL}` (it runs code when a module compiles) as plain Lean: " + ", ".join(parts))
        if dropped:
            what.append(f"removed the import of `{UTIL}`")
        changes[mod] = what
        stats["shortcuts written out"] += n
    if UTIL in out and not any(UTIL in (new_imports.get(m) if m in new_imports else imports.get(m, [])) for m in out if m != UTIL):
        del out[UTIL]
        stats["util module left out"] += 1
    return out, changes, dict(stats), new_imports


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if not args:
        print("usage: p2m_util.py FILE.lean …   (prints what each file would become)", file=sys.stderr)
        return 2
    tot: Counter = Counter()
    for f in args:
        text = Path(f).read_text(encoding="utf-8")
        new, done, left = rewrite_module(text)
        tot.update(done)
        print(f"{f}: expanded {dict(done)}; left {dict(left)}; import {'kept' if IMPORT_UTIL.search(new) else 'dropped'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
