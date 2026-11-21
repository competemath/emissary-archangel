#!/usr/bin/env python3
"""roots_tree.py — the declarations of the tree's libraries that sit in the root namespace get their library's namespace.

  roots_tree.py apply --tree CHECKOUT --roots DIR     # DIR/<Library>.txt: the `root: NAME` lines of tengoku-leakscan for that library (the root-inventory workflow's artifact)

The same transformation the factory applies to a bundle since emissary-archangel#179 (`scope_rewrite.py --qualify-roots`, whose code this file carries unchanged from `mask` to
`qualify_manifest`), applied to the libraries that arrived before it. For a library `L` with roots R:
  - a declaration named by a root of R, a `namespace r` block of a root r (with its `end`), and a dotted `r.x` declaration get `Tengoku.L.` in front;
  - an `open r` of a root namespace follows it;
  - a module that declares or still uses a root gets `namespace Tengoku.L end Tengoku.L open Tengoku.L` on its first body line (a bare use keeps resolving to the library's own name);
  - the manifest record (name and statement) of a renamed declaration follows.
Everything goes INSIDE existing lines (no line moves, so no position in a report or a docstring shifts), and each edited module ends with one generated comment. A root no module declares (the
name Lean gave an anonymous instance) is reported in `unresolved`: text cannot rename it.
The result is a function of the tree and the roots: running it twice changes nothing (an edited name no longer matches).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def _blank(segment: str) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in segment)


def _block_end(text: str, start: int) -> int:
    """the index just past the `-/` that closes the (nested) block comment opened at `start`; the end of the text if it never closes"""
    depth = 1
    for m in re.compile(r"/-|-/").finditer(text, start + 2):
        depth += 1 if m.group() == "/-" else -1
        if not depth:
            return m.end()
    return len(text)


def _string_end(text: str, start: int) -> int:
    """the index just past the closing quote of the string literal opened at `start` (a backslash escapes the next character); the end of the text if it never closes"""
    m = re.compile(r'(?:[^"\\]|\\.)*"', re.DOTALL).match(text, start + 1)
    return m.end() if m else len(text)


def mask(text: str) -> str:
    """the text with every comment (line, nested block, doc) and string literal blanked to spaces: same length and same columns, so a word
    found in the mask is code, and its position is the position in the text"""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            out.append(" " * (end - i))
        elif text.startswith("/-", i):
            end = _block_end(text, i)
            out.append(_blank(text[i:end]))
        elif text[i] == '"':
            end = _string_end(text, i)
            out.append(_blank(text[i:end]))
        else:
            out.append(text[i])
            end = i + 1
        i = end
    return "".join(out)


class Lines:
    """a file as lines, with the mask of each; an edit goes into both so that later edits find their columns"""

    def __init__(self, text: str):
        self.text, self.code = text.split("\n"), mask(text).split("\n")
        self.edited: list[int] = []  # the line of every insertion, in order

    def insert(self, i: int, col: int, word: str) -> None:
        self.edited.append(i)
        self.text[i] = self.text[i][:col] + word + self.text[i][col:]
        self.code[i] = self.code[i][:col] + word + self.code[i][col:]


NAMESPACE = re.compile(
    r"^\s*(?:(?:public|noncomputable)\s+)*namespace\s+((?:«[^»]*»|[^\s«»])+)\s*$"
)  # a «quoted» component may hold a space

OPENER = re.compile(r"^\s*(?:namespace\s+(?:«[^»]*»|[^\s«»])+|(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*section\b.*|mutual\s*)$")
CLOSER = re.compile(r"^\s*end\b")


SCOPE_NAME = re.compile(r"^\s*(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*(?:namespace|section)\s+((?:«[^»]*»|[^\s«»])+)\s*$")
END_SCOPES = re.compile(r"^\s*end\s+((?:«[^»]*»|[^\s«»])+)\s*$")
COMPONENT = re.compile(r"«[^»]*»|[^.«»\s]+")  # one component of a dotted name: a dot inside «quotes» is part of it


def scope_closers(code: list[str]) -> tuple[list[tuple[int, ...]], dict[int, tuple[int, int]]]:
    """For every line the openers (`namespace`, `section`, `mutual`) that enclose it, and for every opener (line of the `end` that closes its OUTERMOST scope, index of the component of
    that `end`'s name which closes it). Lean opens one scope per component of the name (`namespace A.B` opens two) and `end X.Y` closes as many scopes as its name has components, the
    last component first; a bare `end` closes one. So `namespace A` … `namespace B` … `end A.B` closes both, and the scope of `A` is closed by component 0 of that line."""
    stack: list[tuple[int, bool]] = []  # (opener line, whether this scope is the outermost one that line opened)
    open_at: list[tuple[int, ...]] = []
    closer: dict[int, tuple[int, int]] = {}
    for i, ln in enumerate(code):
        open_at.append(tuple(o for o, _ in stack))
        if OPENER.match(ln):
            named = SCOPE_NAME.match(ln)
            n = len(COMPONENT.findall(named.group(1))) if named else 1
            stack.extend((i, k == 0) for k in range(max(n, 1)))
        elif CLOSER.match(ln) and stack:
            named = END_SCOPES.match(ln)
            n = len(COMPONENT.findall(named.group(1))) if named else 1
            for k in range(max(n, 1) - 1, -1, -1):
                if not stack:
                    break
                opener, outermost = stack.pop()
                if outermost:
                    closer[opener] = (i, k)
    return open_at, closer


def scope_info(code: list[str]) -> tuple[list[tuple[int, ...]], dict[int, int]]:
    """for every line the openers (`namespace`, `section`, `mutual`) that enclose it, and for every opener the line of the `end` that closes it (see scope_closers)"""
    open_at, closer = scope_closers(code)
    return open_at, {opener: line for opener, (line, _) in closer.items()}


HEADER_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*(?:import\s|module\s*$|prelude\s*$)")
SECTION = re.compile(r"^\s*(?:@\[expose\]\s*)?(?:(?:public|noncomputable)\s+)*section\b")


def body_start(lines: list[str]) -> int:
    """the index of the first line after the header: blank lines, comments (line and block), `module`/`prelude` and imports are the header; a
    `section` line that opens the body is part of it (the inserted commands go inside it); a doc comment (`/--`) starts the body"""
    depth = 0
    for i, ln in enumerate(lines):
        s = ln.strip()
        if depth:
            depth = max(depth + s.count("/-") - s.count("-/"), 0)
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/--"):
            return i  # a doc comment belongs to the declaration after it: the inserted commands go in front of it, never between the two
        if s.startswith("/-"):
            depth = max(s.count("/-") - s.count("-/"), 0)
            continue
        if HEADER_LINE.match(ln):
            continue
        return i + 1 if SECTION.match(ln) else i
    return len(lines)


def _blank_before(lines: list[str], first: int) -> int | None:
    """The blank line nearest in front of the first body line that is outside a block comment and after the last import (or the `section` that opens the body) (`module`/`import` lines come first; a blank line in a
    `/- … -/` block is comment text). A line comment or a block comment between it and the declaration does not matter: it is the declaration's column that must stay where it is."""
    depth, last_import, blanks = 0, -1, []
    for i in range(min(first, len(lines))):
        s = lines[i].strip()
        if depth:
            depth = max(depth + s.count("/-") - s.count("-/"), 0)
        elif not s:
            blanks.append(i)
        elif s.startswith("/-"):
            depth = max(s.count("/-") - s.count("-/"), 0)
        elif HEADER_LINE.match(lines[i]) or SECTION.match(
            lines[i]
        ):  # the prelude goes inside a `section` that opens the body (see body_start)
            last_import = i
    after = [i for i in blanks if i > last_import]
    return after[-1] if after else None


def _ends_code_line(lines: list[str], i: int) -> bool:
    """Whether the commands can go on the end of line `i`: it is a code line (not a header line: an `import` is followed by nothing on its line, and `module` has no tail) and has no
    line comment, which would swallow what follows."""
    if i < 0 or i >= len(lines):
        return False
    line = lines[i]
    return bool(line.strip()) and not HEADER_LINE.match(line) and "--" not in line


QUOTED = r"«[^»]*»"
NAME_TOKEN = rf"(?:{QUOTED}|[^\s:({{\[⦃«»])+"
PLAIN = r"[^\W\d][\w'!?]*"  # a plain identifier component: a letter or `_`, then letters, digits, `_`, `'`, `!`, `?` (Unicode letters and subscripts included)
SIMPLE_NAME = re.compile(rf"(?:{QUOTED}|{PLAIN})(?:\.(?:{QUOTED}|{PLAIN}))*")
ROOT_LINE = re.compile(rf"(?m)^[ \t]*root:\s+((?:{QUOTED}|[^\s«»])+)[ \t]*$")  # leading blanks: `;` may be followed by a space


def head_of(name: str) -> str:
    """the first component of a dotted name, the quotes of a «quoted» one kept: `«a.b».c` -> `«a.b»`, `Foo.bar` -> `Foo`"""
    m = re.match(rf"{QUOTED}|[^.«»]+", name)
    return m.group(0) if m else name


ROOT_DECL = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable|nonrec|partial|unsafe)[ \t]+)*)"
    # `class abbrev X` and `class inductive X` declare X (as two words they read as a class named `abbrev`: merge of wave 4, Physlib/Units/Basic.lean:280, `class abbrev
    # CarriesDimension` kept its root name); `alias x := y` declares x (same file, line 276, `alias dim := HasDim.d`). `alias ⟨a, b⟩ := h` declares BOTH a and b: ALIAS_PAIR (below) qualifies them (lean-tnorms, 2026-11-21).
    r"(?:(?:local|scoped)[ \t]+)?(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class[ \t]+abbrev|class[ \t]+inductive|class|opaque|axiom|instance|alias)\s+"
    rf"(?:\(priority\s*:=[^)]*\)\s*)?(?P<name>{NAME_TOKEN})"
)
# `alias ⟨a, b⟩ := h` (an iff): the two names it declares, `_` for the one it does not. ROOT_DECL reads that line as an `alias` named `⟨a,` (no root), so the two names stayed in the
# root namespace: lean-tnorms `alias ⟨eq_one_of_one_le, _⟩ := le_one_iff_eq_one` and `alias ⟨_, lt_one_of_ne_one⟩ := lt_one_iff_ne_one` ejected #1012 from the merge queue (roots_gate).
ALIAS_PAIR = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*)alias\s*⟨\s*"
    rf"(?P<a>(?:{QUOTED}|[^\s,⟨⟩:({{\[⦃«»])+)\s*,\s*(?P<b>(?:{QUOTED}|[^\s,⟨⟩:({{\[⦃«»])+)\s*⟩"
)
NAMESPACE_NAME = re.compile(rf"^(?P<pre>\s*(?:(?:public|noncomputable)\s+)*namespace\s+)(?P<name>(?:{QUOTED}|[^\s«»])+)\s*$")
END_NAME = re.compile(rf"^(?P<pre>\s*end\s+)(?P<name>(?:{QUOTED}|[^\s«»])+)\s*$")
OPEN_MARK = "namespace {ns} end {ns} open {ns} "
ROOT_PREFIX = re.compile(r"(?<![\w.'«])_root_\.")  # an explicit root-namespace prefix
TOKEN_HEAD = re.compile(r"(?:«[^»]*»|[^\s.«»(){}\[\]⟨⟩,:;])+")  # the first component of the name that follows it
OPEN_HEADS = (  # `open scoped …` first; when that leaves no valid ending, `scoped` is an argument (the order a backtracking match would try)
    re.compile(r"^(?P<pre>\s*(?:@\[[^\]]*\]\s*)?open\s+scoped\s+)"),
    re.compile(r"^(?P<pre>\s*(?:@\[[^\]]*\]\s*)?open\s+)"),
)
OPEN_TAIL = (  # where the arguments of an `open` end: before `hiding`/`renaming`, before a trailing `in`, before a `(`, or at the end of the line
    re.compile(r"\s+(?:hiding|renaming)\b"),
    re.compile(r"\s+in\s*$"),
    re.compile(r"\s*\("),
    re.compile(r"\s*$"),
)


def open_args(code: str) -> tuple[int, str] | None:
    """(column, text) of the arguments of an `open` line, or None: the shortest arguments (no parenthesis in them) after which the line ends as an `open` line may end. The same as the
    regular expression with a lazy `[^()]*?` and an alternation of those endings (the factory's, emissary-archangel scope_rewrite.py OPEN_LINE) finds on every well-formed `open` line,
    without its backtracking (each candidate end is tried once); they differ only on lines that are no Lean (`open scoped  hiding)`), where the old one backtracked into the blanks."""
    for head_re in OPEN_HEADS:
        head = head_re.match(code)
        if not head:
            continue
        rest = code[head.end() :]
        for end in range(len(rest) + 1):
            if end and rest[end - 1] in "()":
                break  # the arguments cannot contain a parenthesis
            tail = rest[end:]
            if any(t.match(tail) for t in OPEN_TAIL):
                return head.end(), rest[:end]
    return None


def parse_roots(text: str) -> set[str]:
    """the `root: NAME` lines of a leak scan report (a declaration of the library whose name has one component)"""
    return {m.group(1) for m in ROOT_LINE.finditer(text.replace(";", "\n"))}


def _uses_roots(f: Lines, roots: set[str]) -> bool:
    """a bare use of a root name is left in the code (an edited token is preceded by `.`, so it no longer matches)"""
    if not roots:
        return False
    pat = re.compile(r"(?<![\w.'«])(?:" + "|".join(re.escape(r) for r in sorted(roots, key=len, reverse=True)) + r")(?![\w'»])")
    return any(pat.search(c) for c in f.code)


def head_of_token(text: str) -> str:
    """the first component of the name at the start of `text` (empty when there is none)"""
    m = TOKEN_HEAD.match(text)
    return m.group(0) if m else ""


def qualify_explicit_roots(f: Lines, heads: set[str], ns: str) -> dict:
    """`_root_.R…` spells a name from the root: it does not move with a namespace block, so the prefix is followed by `ns.` when R is a root that some module of the library actually renamed
    (`heads`: a root no text declares, an anonymous instance, keeps its name, and `_root_.R` must keep naming it). Code only (comments and strings are masked). A `def _root_.R.x` or
    `def _root_.R` is counted as the declaration it is; a use is not."""
    done: dict = {"declared": [], "dotted": 0, "heads": set()}
    if not heads:
        return done
    for i, code in enumerate(f.code):
        decl = ROOT_DECL.match(code)
        for t in reversed(list(ROOT_PREFIX.finditer(code))):
            head = head_of_token(code[t.end() :])
            if head not in heads:
                continue
            f.insert(i, t.end(), ns + ".")
            done["heads"].add(head)
            if decl and t.start() == decl.start("name"):
                if code[t.end() + len(head) : t.end() + len(head) + 1] == ".":
                    done["dotted"] += 1
                else:
                    done["declared"].append(head)
    return done


def qualify_roots_in_file(f: Lines, roots: set[str], ns: str, mark_open: bool = True, keep_body_namespace: bool = True) -> dict:
    """The edits of one module: a declaration whose name is a root of the library, a `namespace R` block of a root R (with its `end`), and a dotted `R.x` declaration get `<ns>.`
    in front; the first body line gets `namespace NS end NS open NS` when the module declares or still uses a root. All of it goes INSIDE existing lines (no line moves)."""
    done: dict = {
        "declared": [],
        "namespaces": 0,
        "dotted": 0,
        "opened": False,
        "heads": set(),
    }
    open_at, closer = scope_closers(f.code)
    for i, code in enumerate(f.code):
        spelled = ROOT_DECL.match(code)
        if spelled and spelled.group("name").startswith("_root_.") and head_of_token(spelled.group("name")[len("_root_.") :]) in roots:
            done["heads"].add(
                head_of_token(spelled.group("name")[len("_root_.") :])
            )  # declared from the root, wherever it stands: qualify_explicit_roots renames it
        if any(NAMESPACE.match(f.code[o]) for o in open_at[i]):
            continue  # inside a namespace a declaration is `N.x`, not a root; the block itself is handled at its own `namespace` line
        if m := NAMESPACE_NAME.match(code):
            head = head_of(m.group("name"))
            if head in roots:
                f.insert(i, m.start("name"), ns + ".")
                done["heads"].add(head)
                done["namespaces"] += 1
                # The `end` that closes the block names the scopes it closes, innermost last: `ns.` goes in front of the component that closes this namespace. That is the whole
                # name of `end R`, and the first component of `end R.Inner`, which closes a `namespace Inner` opened inside together with it (merge queue, wave 4:
                # Physlib/Units/Exponent.lean, `namespace Dimension` … `namespace Exponent` … `end Dimension.Exponent`: unrenamed it left `Tengoku.Physlib` open).
                at = closer.get(i)
                if at is not None and (e := END_NAME.match(f.code[at[0]])):
                    parts = list(COMPONENT.finditer(e.group("name")))
                    if at[1] < len(parts) and parts[at[1]].group(0) == head:
                        f.insert(at[0], e.start("name") + parts[at[1]].start(), ns + ".")
            continue
        if pair := ALIAS_PAIR.match(code):
            for g in ("b", "a"):  # right to left: an insertion shifts the columns after it
                nm = pair.group(g)
                if nm != "_" and head_of(nm) in roots:
                    f.insert(i, pair.start(g), ns + ".")
                    done["heads"].add(head_of(nm))
                    done["declared"].append(nm)
            continue
        m = ROOT_DECL.match(code)
        if not m:
            continue
        name = m.group("name")
        if head_of(name) in roots:
            dotted = len(re.findall(rf"{QUOTED}|[^.«»]+", name)) > 1  # a dot inside «quotes» is part of one component
            # `def NS.x` makes NS the namespace of the body, and a bare name there resolves to `NS.name` ONLY: it stops competing with an opened `Other.name` (overload), which the
            # root declaration did (merge queue, LeanPool OS3MixedRepInfra: `integral_const_mul` against MeasureTheory's). `def _root_.NS.x` keeps the body where it was. A dotted
            # `R.x` keeps the plain form: its body was in namespace R and its siblings are named from there.
            # An `alias` has no body (its target is resolved where the command stands), so it takes the plain form too.
            keep = keep_body_namespace and not dotted and m.group("kind") != "alias"
            f.insert(i, m.start("name"), ("_root_." if keep else "") + ns + ".")
            done["heads"].add(head_of(name))
            if dotted:
                done["dotted"] += 1
            else:
                done["declared"].append(name)
    for i, code in enumerate(
        f.code
    ):  # `open R` of a root namespace R: the namespace moved, so the `open` follows (right to left: an insertion shifts the columns after it)
        found = open_args(code) if "namespace" not in code else None
        if found:
            column, args = found
            for t in reversed(list(re.finditer(rf"(?:{QUOTED}|[^\s«»])+", args))):
                tok = t.group(0)
                if head_of(tok) in roots and not tok.startswith(ns):
                    f.insert(i, column + t.start(), ns + ".")
                    done["opens"] = done.get("opens", 0) + 1
    touched = bool(done["declared"] or done["namespaces"] or done["dotted"] or done.get("opens"))
    mark = OPEN_MARK.format(ns=ns)
    if mark_open and (touched or _uses_roots(f, roots)) and place_mark(f, mark):
        done["opened"] = True
    return done


def place_mark(f: Lines, mark: str) -> bool:
    """Put `mark` (`namespace NS end NS open NS`) at the place of the first body line that keeps the declaration's column; False when the module has no body or already has it."""
    first = body_start(f.text)
    if first >= len(f.text) or mark.strip() in "\n".join(f.text):
        return False
    if first > 0 and SECTION.match(f.text[first - 1]):
        # The section that opens the body ends before the module does: an `open` inside it stops at that `end`, and what follows would no longer see the renamed names the root
        # declaration showed everywhere (merge queue, wave 4: Leanslt/SLT/CoveringNumber.lean:207, `noncomputable section` … `end` at line 182, `section EuclideanBall` after it).
        # Then the commands go in front of the section, where they last to the end of the file.
        end = scope_info(f.code)[1].get(first - 1)
        if end is not None and any(c.strip() for c in f.code[end + 1 :]):
            first -= 1
    # On the blank line in front of the first body line when there is one: Lean keeps the column where a declaration starts (a doc comment, or `def`) and an application on a
    # LATER line must stand to the right of it, so `namespace … open … def x` / `… /-- doc -/` on one line breaks `(-1) ^ k * bernoulli (k + 1)` in a term body (merge queue,
    # PadicLFunctions/KubotaLeopoldt/ZetaValues.lean:20; Leak IV: same line fails, own line passes). Tactic blocks restart the column, which is why most modules never noticed.
    spot = _blank_before(f.text, first)
    if spot is not None:
        f.insert(spot, 0, mark.rstrip())
    elif not f.text[first].strip():
        f.insert(first, 0, mark)  # the line after a `section` that opens the body is blank: its own line
    elif _ends_code_line(f.text, first - 1):
        # No blank line: the end of the line before (`@[expose] public section`, an `open …`), so that the declaration stays where it is (merge queue, wave 4: FormalConjectures
        # …/Additive/Coset.lean:23, `public section` straight above `noncomputable def`, `sSup {…}` on the next line).
        f.insert(first - 1, len(f.text[first - 1]), " " + mark.rstrip())
    else:
        f.insert(first, 0, mark)
    return True


def qualify_manifest_text(text: str, roots: set[str], ns: str) -> tuple[str, int]:
    """The manifest lines (text) of a declaration whose name starts with a root that the module pass renamed (`roots` is that set: the declaration itself, a member of its namespace block, a dotted
    `R.x`) follow: the module now declares `<ns>.<name>`. A root no module pass renamed (an anonymous instance) leaves its record alone. Returns the new text and the count."""
    out, changed = [], 0
    for line in text.splitlines(keepends=True):
        rec = json.loads(line) if line.strip() else None
        if rec and head_of(rec.get("name", "")) in roots:
            f = Lines(rec["statement"])
            qualify_roots_in_file(
                f, roots, ns, mark_open=False, keep_body_namespace=False
            )  # a record's statement is the declaration alone: no header, no `open`, and no `_root_.` (the name is the whole declaration)
            rec["statement"] = "\n".join(f.text)
            rec["name"] = f"{ns}.{rec['name']}"
            line = json.dumps(rec, ensure_ascii=False) + "\n"
            changed += 1
        out.append(line)
    return "".join(out), changed


def valid_namespace(ns: str) -> str:
    """a namespace name as it goes into generated Lean (`namespace NS end NS open NS`, a declaration prefix): dotted components, plain or «quoted», nothing else: no newline, no command"""
    if not SIMPLE_NAME.fullmatch(ns) or "\n" in ns or "\r" in ns:
        raise argparse.ArgumentTypeError(f"not a Lean namespace name: {ns!r}")
    return ns


LIBRARY = re.compile(r"[A-Za-z][A-Za-z0-9]*")  # `Tengoku/<Library>/`: a plain identifier, never a path
MODULE_PATH = r"Tengoku/{lib}/.+\.lean"
MANIFEST_PATH = re.compile(r"data/intake/[^/]+/manifest\.jsonl")
NOTE = "-- Tengoku: root names of this library moved to {ns} so they do not collide with other libraries (generated)\n"


def manifest_namespace_text(text: str) -> str | None:
    """`Tengoku.<Library>` of an intake manifest: the first two components of the module of its first record"""
    for ln in text.splitlines():
        if ln.strip():
            parts = (json.loads(ln).get("module") or "").split(".")
            return ".".join(parts[:2]) if len(parts) > 2 and parts[0] == "Tengoku" else None
    return None


IMPORT_LINE = re.compile(r"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+(\S+)", re.M)
IDENT_HEAD = re.compile(r"(?<![\w.'«])(«[^»]*»|[^\W\d][\w'!?]*)")
ANY_MODULE = re.compile(r"Tengoku/([A-Za-z][A-Za-z0-9]*)(?:/.+)?\.lean")
NOTE_OPEN = "-- Tengoku: opens {ns}: its root names moved there, and this module uses them (generated)\n"


def dependents(files: dict[str, str], renamed_by_lib: dict[str, set[str]]) -> dict[str, list[str]]:
    """The modules of OTHER libraries that import (transitively) a module of a library whose roots were renamed and that mention one of those names: path -> the libraries to open. The
    old environment showed them those names as root names; after the rename they need `open Tengoku.<Library>` to see the same (merge queue, wave 3: LeanPool's FltRegular/…/UnitLemmas.lean
    uses `quotient_zero_sub_one_comp_aut`, a root name of the FltRegular library; 4 modules of LeanPool and 62 of NavierStokesEuler in the tree today). A library whose roots no text renamed
    has no dependents."""
    libs = sorted(lib for lib, names in renamed_by_lib.items() if names)
    if not libs:
        return {}
    bit = {lib: 1 << i for i, lib in enumerate(libs)}
    modules: dict[str, tuple[str, str]] = {}  # module name -> (path, library)
    for path in files:
        if m := ANY_MODULE.fullmatch(path):
            modules[path[:-5].replace("/", ".")] = (path, m.group(1))
    reach: dict[str, int] = {}

    def reaches(start: str) -> int:
        stack = [start]
        while stack:  # a post-order walk, with no recursion: the import graph is a DAG, a cycle only stops the walk
            n = stack[-1]
            if n in reach and reach[n] >= 0:
                stack.pop()
                continue
            if n not in reach:
                reach[n] = -1
                stack.extend(i for i in IMPORT_LINE.findall(files[modules[n][0]]) if i in modules and i not in reach)
                continue
            value = bit.get(modules[n][1], 0)
            for i in IMPORT_LINE.findall(files[modules[n][0]]):
                if i in modules and reach.get(i, 0) > 0:
                    value |= reach[i]
            reach[n] = value
            stack.pop()
        return reach[start]

    out: dict[str, list[str]] = {}
    for name in sorted(modules):
        path, lib = modules[name]
        value = reaches(name)
        wanted = [other for other in libs if other != lib and value & bit[other]]
        if not wanted:
            continue
        tokens = set(IDENT_HEAD.findall(mask(files[path])))
        need = [other for other in wanted if tokens & renamed_by_lib[other]]
        if need:
            out[path] = need
    return out


def qualify_files(files: dict[str, str], reports: dict[str, str]) -> tuple[dict[str, str], dict]:
    """The whole transformation on text, with no file system: `files` maps a repository path (`Tengoku/<Library>/….lean`, `data/intake/<key>/manifest.jsonl`) to its text, `reports` a library
    to its root report. Returns the files that change (path -> new text) and, per library, what was done."""
    changed: dict[str, str] = {}
    done: dict = {}
    manifests = sorted(p for p in files if MANIFEST_PATH.fullmatch(p))
    renamed_by_lib: dict[str, set[str]] = {}
    for lib in sorted(reports):
        roots = parse_roots(reports[lib]) if LIBRARY.fullmatch(lib) else set()
        modules = sorted(p for p in files if re.fullmatch(MODULE_PATH.format(lib=lib), p)) if roots else []
        if not modules:
            continue
        ns = f"Tengoku.{lib}"
        valid_namespace(ns)
        rep: dict = {"qualified": 0, "namespaces": 0, "dotted": 0, "modules_opened": 0, "unresolved": []}
        seen: set[str] = set()
        renamed: set[str] = set()
        edited: dict[str, tuple[Lines, dict]] = {}
        for path in modules:  # first the declarations and namespace blocks, over every module: which roots are renamed
            f = Lines(files[path])
            edited[path] = (f, qualify_roots_in_file(f, roots, ns))
            renamed |= edited[path][1]["heads"]
        for path, (f, d) in edited.items():  # then the names spelled from the root, for those roots only
            e = qualify_explicit_roots(f, renamed, ns)
            d["declared"] += e["declared"]
            d["dotted"] += e["dotted"]
            if not f.edited:
                continue
            new = "\n".join(f.text)
            if not new.endswith("\n"):
                new += "\n"
            # one footer per module: a module the script already edited (its footer is there) and edits again, because it learned a declaration form since, gets no second one
            note = NOTE.format(ns=ns)
            changed[path] = new if note in new else new + note
            rep["qualified"] += len(d["declared"])
            rep["namespaces"] += d["namespaces"]
            rep["dotted"] += d["dotted"]
            rep["modules_opened"] += 1 if d["opened"] else 0
            seen.update(d["declared"])
        rep["unresolved"] = sorted(roots - seen)
        rep["renamed"] = sorted(renamed)  # the roots the module pass renamed: what the manifest follows
        for path in manifests:
            text = changed.get(path, files[path])
            if manifest_namespace_text(text) == ns:
                new, count = qualify_manifest_text(text, renamed, ns)
                rep["manifest_records"] = count
                if count:
                    changed[path] = new
        done[lib] = rep
        renamed_by_lib[lib] = renamed
    for path, wanted in dependents(files, renamed_by_lib).items():  # the modules of other libraries that use the renamed names
        text = changed.get(path, files[path])
        f = Lines(text)
        opened = [lib for lib in wanted if place_mark(f, OPEN_MARK.format(ns=f"Tengoku.{lib}"))]
        if opened:
            new = "\n".join(f.text)
            if not new.endswith("\n"):
                new += "\n"
            changed[path] = new + "".join(NOTE_OPEN.format(ns=f"Tengoku.{lib}") for lib in opened)
            for lib in opened:
                done[lib]["dependents_opened"] = done[lib].get("dependents_opened", 0) + 1
    return changed, done


def apply(tree: Path, roots_dir: Path) -> dict:
    """qualify_files on a checkout: reads the reports of `roots_dir` and every module of the tree, writes the files that change"""
    reports = {rep.stem: rep.read_text(encoding="utf-8", errors="replace") for rep in sorted(roots_dir.glob("*.txt"))}
    files: dict[str, str] = {}
    if any(
        LIBRARY.fullmatch(lib) for lib in reports
    ):  # every module of the tree: the modules of other libraries that use the renamed names open them too (dependents)
        for path in sorted((tree / "Tengoku").rglob("*.lean")):
            files[path.relative_to(tree).as_posix()] = path.read_text(encoding="utf-8")
    for path in sorted((tree / "data" / "intake").glob("*/manifest.jsonl")):
        files[path.relative_to(tree).as_posix()] = path.read_text(encoding="utf-8")
    changed, done = qualify_files(files, reports)
    for rel, text in changed.items():
        (tree / rel).write_text(text, encoding="utf-8")
    return done


def main(argv: list[str] | None = None) -> int:
    """`roots_tree.py apply`, run in a checkout: every report under `data/roots/<id>/<Library>.txt` of the working directory is applied, the ids in order (a report already applied
    changes nothing). No path is taken from the command line: the tree is the working directory."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("cmd", choices=["apply"])
    ap.parse_args(argv)
    tree = Path.cwd()
    report = {d.name: apply(tree, d) for d in sorted((tree / "data" / "roots").glob("*")) if d.is_dir()}
    print(json.dumps(report, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
