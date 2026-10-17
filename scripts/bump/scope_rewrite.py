#!/usr/bin/env python3
"""scope_rewrite.py — make what a library registers for other libraries' types local to the module that registers it.

Once the tree is imported as one, a GLOBAL instance or simp lemma that mentions nothing of its own library changes how every other
library's statements elaborate (formal-mathfin's `attribute [instance] Matrix.linftyOpNormedAddCommGroup` makes the norm of every matrix
the L-infinity operator norm; compfiles' `Coe (ℕ × ℕ) (ℤ × ℤ)` is a silent coercion everywhere). The merge queue's `tengoku-leakscan` lists
them, with positions, from the compiled environment:

    leak: instance Imo1977P2.instCoeForallIntForallReal registered in Tengoku.Compfiles.Compfiles.Imo1977P2 (declared at line 34)
    leak: instance Matrix.linftyOpNormedAddCommGroup registered in Tengoku.X.Y (declared in Tengoku.Analysis.Matrix.Normed: an `attribute` command ...)
    leak: simp Imo1979P6.Walk.take_append registered in Tengoku.Compfiles.Compfiles.Imo1979P6 (declared at line 62)

A third kind is NOTATION (`leak: notation LO.Modal.Formula.«term-_» registered in Tengoku.… (declared at line 24)`): a global `prefix:80 "-" => complement` is a second
reading of every `-(…)` in the tree ("Ambiguous term" on a real number), and a global `notation "v" => …` or `elab "superpose" …` makes `v`, `superpose` reserved words in every
file. The command is made `scoped` (inside a namespace; `open scoped N` after the block that closes N and in the library's own importers) or, in the root namespace, `local`
(the command is declared again, `local`, in the importers).

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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import autonames  # noqa: E402
import tolerant_build as tb  # noqa: E402

LEAK = re.compile(
    r"leak:\s+(?P<kind>instance|simp|notation)\s+(?P<name>(?:«[^»]*»|[^\s;«»])+)\s+registered in\s+(?P<mod>[^\s;]+)"
    r"(?:\s+\(priority (?P<prio>\d+)\))?"
    r"(?:\s+\(declared at line (?P<line>\d+)\)|\s+\(declared in (?P<other>\S+?):)?"
)
ATTR_CMD = re.compile(r"^\s*attribute\s*\[")


def parse(text: str) -> list[dict]:
    # every `leak:` entry of the text, whatever separates them (newlines, `;`, or the single line a log flattens them to)
    return [
        {"kind": m["kind"], "name": m["name"], "mod": m["mod"], "line": int(m["line"]) if m["line"] else None, "prio": int(m["prio"]) if m["prio"] else None}
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
        self.edited: list[int] = []  # the line of every insertion, in order

    def insert(self, i: int, col: int, word: str) -> None:
        self.edited.append(i)
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


NAMESPACE = re.compile(r"^\s*(?:(?:public|noncomputable)\s+)*namespace\s+(\S+)\s*$")
NAMED_INSTANCE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public)[ \t]+)*(?:local[ \t]+|scoped[ \t]+)?instance\s+(?:\(priority\s*:=[^)]*\)\s*)?([^\s:({\[]+)"
)
NAMED_THEOREM = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public)[ \t]+)*(?:theorem|lemma|def|abbrev)\s+([^\s:({\[]+)"
)


def edit_named_declaration(f: Lines, name: str, kind: str) -> str:
    """A leak line without a position (`leak: instance X registered in M`, written by hand for a module whose text is not known yet, as in a recut): the DECLARATION whose
    full name is `name` in this module, `instance NAME` (after attributes and modifiers) or `@[…simp…] theorem|lemma|def|abbrev NAME`, made local. The full name is the
    declared name under the `namespace`/`section`/`end` blocks that enclose it (`_root_.` aside), so `A.foo` and `B.foo` are different declarations. Only that declaration's
    own line (instance) or attribute lines (simp: the `@[…]` on its line and on the lines right above it) are edited, never a neighbour's. Auto-generated names have no
    declaration to find. Same answers as edit_declaration: "edited", "already", "missing"."""
    decl = NAMED_INSTANCE if kind == "instance" else NAMED_THEOREM
    blocks: list[list[str]] = []  # one entry per open namespace / section / mutual; a namespace holds its name's components
    seen = "missing"
    for i, code in enumerate(f.code):
        if m := NAMESPACE.match(code):
            blocks.append(m.group(1).split("."))
            continue
        if OPENER.match(code):
            blocks.append([])
            continue
        if CLOSER.match(code):
            if blocks:
                blocks.pop()
            continue
        dm = decl.match(code)
        if not dm:
            continue
        declared = dm.group(1)
        full = declared[len("_root_.") :] if declared.startswith("_root_.") else ".".join([c for blk in blocks for c in blk] + [declared])
        if full != name:
            continue
        if kind == "instance":
            if re.search(r"\b(?:local|scoped)\s+instance\b", code):
                seen = "already"
                continue
            m = re.search(rf"(?<![\w.]){NOT_LOCAL}\binstance\b", code)
            if m:
                f.insert(i, m.start(), "local ")
                return "edited"
            continue
        start = i
        while start > 0 and f.code[start - 1].strip().startswith("@["):
            start -= 1
        for k in range(start, i + 1):  # the attributes of this declaration only
            for attrs in re.finditer(r"@\[([^\]]*)\]", f.code[k]):
                if re.search(r"\b(?:local|scoped)\s+simp\b", attrs.group(1)):
                    seen = "already"
                    continue
                hit = re.search(rf"(?<![\w.]){NOT_LOCAL}\bsimp\b", attrs.group(1))
                if hit:
                    f.insert(k, attrs.start(1) + hit.start(), "local ")
                    return "edited"
    return seen


NOTATION_KW = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*)(?P<mod>(?:local|scoped)[ \t]+)?"
    r"(?P<kw>prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab)(?![\w'.])"
)


def namespace_at(code: list[str], i: int) -> str:
    """the namespace the line `i` (0-based) is in: the `namespace` blocks that enclose it, joined (sections add nothing)"""
    blocks: list[list[str]] = []
    for ln in code[:i]:
        if m := NAMESPACE.match(ln):
            blocks.append(m.group(1).split("."))
        elif OPENER.match(ln):
            blocks.append([])
        elif CLOSER.match(ln) and blocks:
            blocks.pop()
    return ".".join(c for blk in blocks for c in blk)


def code_end(text: str) -> int:
    """the column where the code of this line ends: before a `--` comment that is not inside a string literal"""
    inside, i = False, 0
    while i < len(text):
        c = text[i]
        if inside:
            if c == "\\":
                i += 2
                continue
            inside = c != '"'
        elif c == '"':
            inside = True
        elif text.startswith("--", i):
            return len(text[:i].rstrip())
        i += 1
    return len(text.rstrip())


OPEN_CMD = re.compile(r"^\s*open\b(?!.*\bin\s*$)")  # `open X in` applies to the next command only
FORBIDDEN_NS: set[str] = set()  # namespaces a notation may not be scoped to (--forbid-namespaces): core's and Mathlib's own scoped entries live there


def open_before(code: list[str], i: int) -> bool:
    """an `open …` command above line `i` that is still in effect there: in the block of the line or in one around it (or at the top of the file)"""
    blocks = [False]
    for ln in code[:i]:
        if NAMESPACE.match(ln) or OPENER.match(ln):
            blocks.append(False)
        elif CLOSER.match(ln) and len(blocks) > 1:
            blocks.pop()
        elif OPEN_CMD.match(ln):
            blocks[-1] = True
    return any(blocks)


def reopen_needed(f: Lines, i: int) -> bool:
    """some block around line `i` has code after its `end` (more than the `end`s of the blocks around it): a scoped notation would have to be activated again there"""
    open_at, end_of = scope_info(f.code)
    return any(
        (end := end_of.get(op)) is not None and any(ln.strip() and not CLOSER.match(ln) for ln in f.code[end + 1 :]) for op in open_at[i]
    )


def edit_notation(f: Lines, line: int, has_importers: bool = True) -> tuple[str, dict | None]:
    """The notation / syntax / macro / elab command of the declaration that starts at `line` (1-based; the range includes its doc comment and attributes), made `scoped`
    when it sits in a namespace and `local` in the root namespace. ("edited", info), ("already", None) when it is local or scoped already, ("missing", None), or
    ("unsupported", {"why"}) when it cannot be made scoped or local without changing what the library means:
      - `scoped` to a namespace in which core or Mathlib have scoped entries too, when an `open scoped N` would be needed (code after the namespace in the same file, or an importer
        in the library): `open scoped N` would turn those on as well;
      - `local` in the root namespace, which the importers get as the same command again: not when the command goes on over several lines, and not when an `open` is in effect
        where it stands (the names of its right-hand side are read where the command is elaborated, and the importer has no such `open`).
    `info`: mode, ns (the namespace it is scoped to), cmd (the command from its keyword, without a trailing comment: what an importer declares again when it is local), line (0-based)."""
    for i in range(max(0, line - 1), min(len(f.text), line + 14)):
        m = NOTATION_KW.match(f.code[i])
        if not m:
            continue
        if m.group("mod"):
            return "already", None
        ns = namespace_at(f.code, i)
        if ns in FORBIDDEN_NS and (has_importers or reopen_needed(f, i)):
            return "unsupported", {"why": f"`scoped` would put it in `{ns}`, a namespace in which core or Mathlib have scoped entries, and `open scoped {ns}` would be needed"}
        if not ns:
            nxt = f.code[i + 1] if i + 1 < len(f.code) else ""
            if nxt.strip() and nxt[:1] in " \t":
                return "unsupported", {"why": "a root-namespace command of several lines cannot be declared again, local, in the importers"}
            if open_before(f.code, i):
                return "unsupported", {"why": "a root-namespace command after an `open` cannot be declared again in the importers (they do not have the `open`)"}
        col = m.start("kw")
        cmd = f.text[i][col : code_end(f.text[i])]
        f.insert(i, col, "scoped " if ns else "local ")
        return "edited", {"mode": "scoped" if ns else "local", "ns": ns, "cmd": cmd, "line": i}
    return "missing", None


def activation_lines(infos: list[dict]) -> list[str]:
    """what makes the notations of `infos` active again: one `open scoped N …` for the scoped ones, the command again (`local …`) for the local ones"""
    ns = sorted({x["ns"] for x in infos if x["mode"] == "scoped"})
    cmds: list[str] = []
    for x in sorted(infos, key=lambda x: x["line"]):
        if x["mode"] == "local" and x["cmd"] not in cmds:
            cmds.append(x["cmd"])
    return (["open scoped " + " ".join(ns)] if ns else []) + ["local " + c for c in cmds]


def notation_reopens(f: Lines, notes: list[tuple[int, dict]]) -> dict[int, list[str]]:
    """A `scoped` notation is active inside its namespace, a `local` one until the end of the block it sits in; what follows that block in the same file used to see it.
    For every enclosing block that has code after its `end` (more than the `end`s of the blocks around it), the notation is activated again right after that `end`."""
    open_at, end_of = scope_info(f.code)
    by_end: dict[int, list[dict]] = {}
    for i, info in notes:
        for opener in open_at[i]:
            end = end_of.get(opener)
            if end is not None and any(ln.strip() and not CLOSER.match(ln) for ln in f.code[end + 1 :]):
                by_end.setdefault(end, []).append(info)
    return {end: activation_lines(infos) for end, infos in by_end.items()}


OPENER = re.compile(r"^\s*(?:namespace\s+\S+|(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*section\b.*|mutual\s*)$")
CLOSER = re.compile(r"^\s*end\b")


def scope_info(code: list[str]) -> tuple[list[tuple[int, ...]], dict[int, int]]:
    """for every line the openers (`namespace`, `section`, `mutual`) that enclose it, and for every opener the line of its `end`"""
    stack: list[int] = []
    open_at, end_of = [], {}
    for i, ln in enumerate(code):
        open_at.append(tuple(stack))
        if OPENER.match(ln):
            stack.append(i)
        elif CLOSER.match(ln) and stack:
            end_of[stack.pop()] = i
    return open_at, end_of


def reregistrations(f: Lines, edits: list[tuple[int, dict]]) -> dict[int, dict[tuple[str, int | None], set[str]]]:
    """A `local` registration ends where the namespace or section it sits in ends; what follows in the same file used to see it. For every enclosing
    block that has code after its `end`, the registration is made again right after that `end` (outermost last): line -> (kind, priority) -> names."""
    open_at, end_of = scope_info(f.code)
    out: dict[int, dict[tuple[str, int | None], set[str]]] = {}
    for i, lk in edits:
        if not nameable(lk["name"]):
            continue
        for opener in open_at[i]:
            end = end_of.get(opener)
            if end is not None and any(ln.strip() for ln in f.code[end + 1 :]):
                prio = lk.get("prio") if lk["kind"] == "instance" else None
                out.setdefault(end, {}).setdefault((lk["kind"], prio), set()).add(lk["name"])
    return out


def attribute_lines(groups: dict[tuple[str, int | None], set[str]]) -> list[str]:
    lines = []
    for (kind, prio), names in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1] or 0)):
        attr = f"local {'instance' if kind == 'instance' else 'simp'}" + (f" {prio}" if prio not in (None, 1000) else "")
        uniq = sorted(names)
        lines += [f"attribute [{attr}] " + " ".join(uniq[k : k + 6]) for k in range(0, len(uniq), 6)]
    return lines


NOTATION_EDITS: dict[str, list[dict]] = {}  # leak module name -> what was done to its notations (reexport gives the importers the same activation)


def rewrite_file(path: Path, leaks: list[dict], mod: str | None = None, has_importers: bool = True) -> tuple[int, list[str]]:
    text = path.read_text()
    f = Lines(text)
    done, skipped = 0, []
    edits: list[tuple[int, dict]] = []
    notes: list[tuple[int, dict]] = []
    for lk in sorted(leaks, key=lambda x: -(x["line"] or 0)):
        before = len(f.edited)
        if lk["kind"] == "notation":
            r, info = edit_notation(f, lk["line"], has_importers) if lk["line"] else ("missing", None)
            if r == "edited":
                notes.append((info["line"], info))
            elif r == "missing":
                skipped.append(f"notation {lk['name']}")
            elif r == "unsupported":
                skipped.append(f"notation {lk['name']}: {info['why']}")
            continue
        if lk["line"]:
            r = edit_declaration(f, lk["line"], lk["kind"])
        else:
            r = edit_attribute_command(f, lk["name"], lk["kind"])
            if r == "missing":
                r = edit_named_declaration(f, lk["name"], lk["kind"])
        if r == "edited":
            done += 1
            edits.append((f.edited[before], lk))
        elif r == "missing":
            skipped.append(f"{lk['kind']} {lk['name']}")
    if done or notes:
        adds: dict[int, list[str]] = {}
        for end, groups in reregistrations(f, edits).items():
            adds.setdefault(end, []).extend(attribute_lines(groups))
        for end, lines in notation_reopens(f, notes).items():
            adds.setdefault(end, []).extend(lines)
        for end, lines in sorted(adds.items(), reverse=True):  # bottom first: a line inserted below never moves one above
            f.text[end + 1 : end + 1] = lines
        new = "\n".join(f.text)
        if not new.endswith("\n"):
            new += "\n"
        if done:
            new += f"-- Tengoku: {done} registration(s) of this module made local so they do not change other libraries (generated)\n"
        if notes:
            kinds = "scoped" if all(i["mode"] == "scoped" for _, i in notes) else "local" if all(i["mode"] == "local" for _, i in notes) else "scoped or local"
            new += f"-- Tengoku: {len(notes)} notation(s) of this module made {kinds} so they do not change other libraries (generated)\n"
        path.write_text(new)
        if notes and mod:
            NOTATION_EDITS[mod] = [i for _, i in notes]
    return done + len(notes), skipped


def apply_bundle(root: Path, leaks: list[dict], skip: int = 0) -> dict:
    NOTATION_EDITS.clear()
    by_mod: dict[str, list[dict]] = {}
    for lk in leaks:
        by_mod.setdefault(lk["mod"], []).append(lk)
    report = {"rewritten": 0, "skipped": [], "missing_modules": []}
    files = native_names(root, skip)
    imported = {m for deps in import_graph(files, skip).values() for m in deps} if files else set()
    for mod, ls in sorted(by_mod.items()):
        f = module_file(root, mod, skip)
        if not f:
            report["missing_modules"].append(mod)  # a leak of a module this bundle does not carry (the other bundle: strict vs proposed)
            continue
        parts = parts_of(mod)
        native = ".".join(parts[2:]) if parts and len(parts) > 2 else mod
        done, skipped = rewrite_file(f, ls, mod, native in imported or not files)
        report["rewritten"] += done
        report["skipped"] += [f"{mod}: {s}" for s in skipped]
    return report



HEADER_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*(?:import\s|module\s*$|prelude\s*$)")
SECTION = re.compile(r"^\s*(?:@\[expose\]\s*)?(?:(?:public|noncomputable)\s+)*section\b")


def body_start(lines: list[str]) -> int:
    """the index of the first line after the header: blank lines, comments (line and block), `module`/`prelude` and imports are the header; a
    `section` line that opens the body is part of it (the inserted commands go inside it)"""
    depth = 0
    for i, ln in enumerate(lines):
        s = ln.strip()
        if depth:
            depth = max(depth + s.count("/-") - s.count("-/"), 0)
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            depth = max(s.count("/-") - s.count("-/"), 0)
            continue
        if HEADER_LINE.match(ln):
            continue
        return i + 1 if SECTION.match(ln) else i
    return len(lines)


def nameable(n: str) -> bool:
    """a declaration name an `attribute` command can say: not private, not a hygienic or auxiliary name"""
    return not (n.startswith("_private") or "_@" in n or "._hyg" in n or n.startswith("_"))


def native_names(root: Path, skip: int) -> dict[str, Path]:
    """module (the library's own name) -> file, for a bundle directory (`Tengoku/<Library>/…`, skip=0) or the library's layout (skip=2)"""
    base = root
    if skip == 0:
        libs = [d for d in (root / "Tengoku").iterdir() if d.is_dir()] if (root / "Tengoku").is_dir() else []
        if len(libs) != 1:
            return {}
        base = libs[0]
    out = {}
    for f in base.rglob("*.lean"):
        if f.is_symlink() or f.name == "Deps.lean":
            continue
        out[".".join(f.relative_to(base).with_suffix("").parts)] = f
    return out


def import_graph(files: dict[str, Path], skip: int) -> dict[str, list[str]]:
    """module (the library's own name) -> the library's modules it imports directly"""
    imports: dict[str, list[str]] = {}
    for mod, f in files.items():
        imports[mod] = []
        for imp in tb.header_imports(f.read_text()):
            parts = parts_of(imp)
            if not parts:
                continue
            cand = ".".join(parts[2:]) if (skip == 0 and parts[:1] == ["Tengoku"] and len(parts) > 2) else ".".join(parts)
            if cand in files:
                imports[mod].append(cand)
    return imports


def reexport(root: Path, leaks: list[dict], skip: int = 0) -> dict:
    """What a module of the library registered globally, the library's OTHER modules saw as given: every module that imports (even
    indirectly) a module with a flagged registration gets `attribute [local instance] X` / `[local simp] X` for it, so inside the library nothing
    changes while the tree outside sees none of it. A module's own registrations are local already (rewrite_file)."""
    files = native_names(root, skip)
    if not files:
        return {"reexported": 0, "modules": 0}
    own_leaks: dict[str, list[dict]] = {}
    own_notes: dict[str, list[dict]] = {}
    for lk in leaks:
        parts = parts_of(lk["mod"])
        if parts and len(parts) > 2 and lk["kind"] != "notation" and nameable(lk["name"]):
            own_leaks.setdefault(".".join(parts[2:]), []).append(lk)
    for modname, infos in NOTATION_EDITS.items():
        parts = parts_of(modname)
        if parts and len(parts) > 2:
            own_notes[".".join(parts[2:])] = infos
    imports = import_graph(files, skip)

    def closure(mod: str) -> set[str]:
        seen, stack = set(), list(imports[mod])
        while stack:
            m = stack.pop()
            if m not in seen:
                seen.add(m)
                stack.extend(imports[m])
        return seen

    patched = names_total = 0
    for mod, f in sorted(files.items()):
        inherited: list[dict] = []
        inherited_notes: list[dict] = []
        for dep in sorted(closure(mod) - {mod}):
            inherited += own_leaks.get(dep, [])
            inherited_notes += own_notes.get(dep, [])
        if not inherited and not inherited_notes:
            continue
        lines = f.read_text().split("\n")
        groups: dict[tuple[str, int | None], list[str]] = {}
        for lk in inherited:
            groups.setdefault((lk["kind"], lk.get("prio") if lk["kind"] == "instance" else None), []).append(lk["name"])
        ins = []
        for (kind, prio), ns in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1] or 0)):
            word = "instance" if kind == "instance" else "simp"
            attr = f"local {word}" + (f" {prio}" if prio not in (None, 1000) else "")
            uniq = sorted(set(ns))
            for k in range(0, len(uniq), 6):
                ins.append(f"attribute [{attr}] " + " ".join(uniq[k : k + 6]))
            names_total += len(uniq)
        ins = activation_lines(inherited_notes) + ins
        at = body_start(lines)
        lines[at:at] = ins + [""]
        f.write_text("\n".join(lines))
        patched += 1
    return {"reexported": names_total, "modules": patched}


def rewrite_manifest(root: Path, leaks: list[dict]) -> int:
    """The `statement` of a manifest record whose simp lemma was made local keeps the upstream `@[simp]` unless it is changed too: the module says `@[local simp]`, the record
    said otherwise (P1 in tengoku#418: zflean `ZFSet.prod_empty_left`, `pair_union`, `pair_minus`). `root/manifest.jsonl` is rewritten in place, in the compose format; the
    records of other declarations and the instance leaks (no record is an instance) are left as they are. Returns how many statements changed."""
    path = root / "manifest.jsonl"
    if not path.is_file():
        return 0
    want = {(lk["mod"], lk["name"]) for lk in leaks if lk["kind"] == "simp"}
    out, changed = [], 0
    for line in path.read_text(encoding="utf-8").splitlines(keepends=True):
        rec = json.loads(line) if line.strip() else None
        if rec and (rec.get("module"), rec.get("name")) in want:
            f = Lines(rec["statement"])
            if edit_declaration(f, 1, "simp") == "edited":
                rec["statement"] = "\n".join(f.text)
                line = json.dumps(rec, ensure_ascii=False) + "\n"
                changed += 1
        out.append(line)
    path.write_text("".join(out), encoding="utf-8")
    return changed


def for_tree(leaks: list[dict]) -> list[dict]:
    """The leaks as the tree names them. The leak scan runs on the library's own build, where Lean's auto-generated instance names carry the library's suffix
    (`instFoo_prismriver`); in the bundle they carry the tree's (`instFoo_tengoku`, autonames.py), and every line this script writes into a bundle must use those:
    the `attribute [local instance] …` lines it inserts, and the lookup of an `attribute` command of the library. The library's own layout (`--pruned`) keeps the
    library's names: that is the environment the factory verified."""
    out = []
    for lk in leaks:
        parts = parts_of(lk["mod"])
        out.append({**lk, "name": autonames.rewrite(lk["name"], parts[2])[0]} if parts and len(parts) > 2 and lk["kind"] != "notation" else lk)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", action="append", default=[], help="a bundle directory (Tengoku/<Library>/… inside)")
    ap.add_argument("--pruned", action="append", default=[], help="a directory of the library's own layout (the factory's pruned sources)")
    ap.add_argument("--leaks", required=True)
    ap.add_argument("--reexport", action="store_true", help="also give every module that imports a flagged module the same registrations, local to it")
    ap.add_argument("--forbid-namespaces", help="a file, one namespace per line: a notation there is not made scoped (core and Mathlib have scoped entries in it); it stays as it is and is reported")
    a = ap.parse_args()
    leaks = parse(a.leaks)
    if a.forbid_namespaces:
        FORBIDDEN_NS.update(x.strip() for x in Path(a.forbid_namespaces).read_text().splitlines() if x.strip())
    if not leaks:
        print(json.dumps({"rewritten": 0, "note": "no leak lines"}))
        return
    for dirs, skip in ((a.bundle, 0), (a.pruned, 2)):
        for b in dirs:
            if Path(b).exists():
                use = for_tree(leaks) if skip == 0 else leaks
                rep = apply_bundle(Path(b), use, skip)
                if skip == 0:
                    rep["manifest_statements"] = rewrite_manifest(Path(b), use)
                if a.reexport:
                    rep.update(reexport(Path(b), use, skip))
                print(b, json.dumps(rep))


if __name__ == "__main__":
    main()
