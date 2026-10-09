#!/usr/bin/env python3
"""records.py — staging records for the declarations of a bumped library that passed the batched Gate 2.

The per-theorem pipeline builds each record's `context` by pruning the library's source with heuristics and then compiles
the result once per theorem. Here the library was built whole, so the environment says exactly which of the library's own
declarations a theorem is made of (every constant in the closure of its type and proof), and the source says where each
one lives (`findDeclarationRanges?`). The context of a record is then

    set_option linter.all false -- [Emissary] lints are not drift; the kernel decides
    -- [Emissary prelude] <Module> — verbatim (imports stripped)       one block per library module the theorem imports,
    <module text: glue + the declarations the theorem needs>           in import order
    -- [Emissary] <file>, everything before line N (...)               the theorem's own file up to the theorem
    <file text: glue + the declarations the theorem needs>

where GLUE is everything outside a pruneable declaration (namespaces, opens, variables, notations, macros, tactics,
comments): kept whole, so scope is exactly as in the file; and a pruneable declaration (theorem, lemma, def, abbrev,
instance, structure, class, inductive, opaque, axiom) is kept only if the theorem uses it. The marker lines are the ones
tengoku's scripts/generate.py parses. Whether a record then builds is decided where it always was: the tree's build gate.

  records.py lean    --lib DIR --names passed.json --out records-deps.lean
  records.py compose --lib DIR --log records-deps.log --meta setup.ci.json --out composed.jsonl [--lines old-lines.json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

LEAN = r'''
open Lean Elab Command Meta

def recParse (s : String) : Name := (s.splitOn ".").foldl (fun n part => Name.mkStr n part) Name.anonymous

def recModOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- For each name: its module, and every library constant (module, name) in the closure of its type and value (proofs
included: the record has to compile). Where those constants are in the source is in the `.ranges.json` next to each olean.
One command for all the names: the direct library dependencies of a constant are read out of its (large) proof term ONCE and
shared by every closure that reaches it. -/
elab "#records_deps " names:str " in " libs:str : command => do
  let libMods : NameSet := (libs.getString.splitOn ",").foldl (fun s x => if x == "" then s else s.insert (recParse x)) {}
  let direct ← IO.mkRef (({} : Std.HashMap Name (Array Name)))
  for s in (names.getString.splitOn ",").filter (· != "") do
    let n := recParse s
    let j ← liftTermElabM do
      let env ← getEnv
      let isOwn (c : Name) : Bool := match recModOf env c with | some m => libMods.contains m | none => false
      let mut seen : NameSet := {}
      let mut stack : List Name := [n]
      let mut consts : Array Json := #[]
      while !stack.isEmpty do
        match stack with
        | [] => pure ()
        | c :: rest =>
          stack := rest
          if seen.contains c then continue
          seen := seen.insert c
          let deps ← match (← direct.get)[c]? with
            | some d => pure d
            | none =>
              let d := match env.find? c with
                | some ci => (ci.getUsedConstantsAsSet.toList.filter isOwn).toArray
                | none => #[]
              direct.modify (·.insert c d)
              pure d
          for u in deps do
            unless seen.contains u do stack := u :: stack
          if let some m := recModOf env c then
            consts := consts.push (Json.arr #[toJson m.toString, toJson c.toString])
      let some m := recModOf env n | return Json.mkObj [("name", toJson s), ("error", toJson "not in an imported module")]
      return Json.mkObj [("name", toJson s), ("module", toJson m.toString), ("consts", Json.arr consts)]
    logInfo m!"REC_DEPS {j.compress} REC_END"
'''


def lean_file(a: argparse.Namespace) -> None:
    names = json.loads(Path(a.names).read_text())  # {module: [declaration names]}
    modules = sorted(names)
    lines = ["import Lean", "import Mathlib"] + [f"import {m}" for m in modules] + [LEAN]
    allmods = ",".join(modules)
    every = [n for m in modules for n in names[m]]
    lines.append(f'#records_deps "{",".join(every)}" in "{allmods}"')
    Path(a.out).write_text("\n".join(lines) + "\n")
    print(f"{sum(len(v) for v in names.values())} names in {len(modules)} modules")


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*|/--.*?-/\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b",
    re.S,
)
# a block that defines how the SOURCE is read or run (tactics, notations, elaborators, initializers) is glue whatever the closure says
CODE_ATTR = re.compile(r"@\[[^\]]*\b(?:tactic|command_elab|term_elab|macro|elab|delab|app_unexpander|parser|builtin\w*|init|initialize|simproc|dsimproc|norm_num|positivity|push_cast|ext|aesop)\b")
IMPORT_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s")
KEYWORD_LINE = re.compile(r"^\s*(?:module|prelude)\s*$")
IN_PREFIX = re.compile(r"^\s*(?:open|set_option|attribute|local|universe|variable|namespace|section|include|omit)\b.*\bin\s*$")
DECL_LINE = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|meta)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b")


def merge_ranges(rs: list[tuple[int, int]]) -> list[tuple[int, int]]:
    """Outermost ranges only (a structure's range contains its fields')."""
    out: list[tuple[int, int]] = []
    for s, e in sorted(set(rs), key=lambda r: (r[0], -r[1])):
        if out and s <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], e))
        else:
            out.append((s, e))
    return out


def strip_block_comments_in_doc(text: str) -> str:
    return text


LEAD_IN = re.compile(r"^(?:/--|@\[)")  # a docstring or attribute line: it belongs to the declaration below it
ATTR_INLINE = re.compile(r"^(?:@\[[^\]]*\]\s*)+")  # the attributes at the start of a line (`@[simp] theorem …`)
DECL_NAME = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|meta)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|instance)\s+([^\s:({\[⦃]+)")
# commands that cannot take a docstring or an attribute: one of these right after one means its declaration is gone
NO_LEAD_IN = re.compile(r"^(?:end\b|namespace\b|section\b|variable\b|universe\b|import\b|open\b(?!.*\bin\s*$))")


def attrs_end(text: str) -> int:
    """Where the attributes at the start of `text` end: the index just after the last one, 0 when `text` does not start with an attribute, -1 when one is still open
    (`@[deprecated X` and the closing `]` is on a later line). Attributes are `@[simp]`, several in a row, or one spread over lines (`@[deprecated X` /
    `(since := "…")]`): brackets balance across lines, and a bracket inside a string does not count."""
    i, n, end = 0, len(text), 0
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        if not text.startswith("@[", i):
            break
        depth, in_str = 0, False
        while i < n:
            c = text[i]
            if in_str:
                if c == "\\":
                    i += 1
                elif c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == "[":
                depth += 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            i += 1
        else:
            return -1  # a bracket never closed
        end = i
    return end


def attrs_only(text: str) -> bool:
    """Whether `text` is attributes and nothing else."""
    end = attrs_end(text)
    return end > 0 and not text[end:].strip()


class Module:
    """A module's text as glue plus declaration blocks. A block is a declaration Lean can prune: its lead-in lines (`open Foo in` /
    `set_option … in`, docstrings, attributes, comments) and the declaration itself, up to the next column-0 command. Lean's declaration
    ranges (`*.olean.ranges.json`, one per declaration that reached the environment) are mapped onto the blocks: a block with no range is
    text Lean never elaborated (it errored, or came after an error) and is always cut; a ranged block is kept when a kept range names it;
    a ranged block carrying a code attribute (`@[simp]`, `@[ext]`, …) is glue that stays, since the attribute registers it for the proofs
    that are kept. Everything else is glue and stays. (complexitylib part 1, 2026-10-07: a theorem under `open scoped Classical in`, one
    whose docstring and keyword had comment lines between them, and theorems that never elaborated all survived the old pruning, and the
    module did not build.)"""

    def __init__(self, lib: Path, mod: str, ranges: list[tuple[int, int]]):
        path = lib / (mod.replace(".", "/") + ".lean")
        self.path = path
        self.lines = path.read_text(errors="replace").split("\n")
        n = len(self.lines)
        self.blocks: list[tuple[int, int]] = []
        self.code_attr: set[tuple[int, int]] = set()
        lead: int | None = None
        for s, e in segments(self.lines):
            while e > s and not self.lines[e - 1].strip():
                e -= 1  # a block ends at its last line of text, not at the blank lines before the next command
            first = self.lines[s - 1].lstrip()
            core = decl_core(self.lines, s, e)
            if core and DECL_LINE.match(core):
                b = (lead if lead is not None else s, e)
                self.blocks.append(b)
                if any(CODE_ATTR.search(self.lines[i - 1]) for i in range(b[0], s + 1)):
                    self.code_attr.add(b)
                lead = None
            elif IN_PREFIX.match(first) or first.startswith("/--") or (first.startswith("@[") and attrs_only("\n".join(self.lines[s - 1 : e]))):
                lead = s if lead is None else lead  # a docstring, attributes of their own (on one line or several) or an `… in` line: they belong to the declaration below
            else:
                lead = None  # glue, `@[expose] public section` included: an attribute on a command that is no declaration
        self.blocks.sort()
        self.ranged: set[tuple[int, int]] = set()
        for rs, re_ in merge_ranges(ranges):
            if 1 <= rs <= n and (b := self.block_of(rs)):
                self.ranged.add(b)

    def with_prefix(self, s: int) -> int:
        """The first line of the block whose declaration starts at line `s`: the lead-in lines above it (`open Foo in`, docstrings, attributes,
        comments) belong to it and go when it goes."""
        b = self.block_of(s)
        return b[0] if b else s

    def kept_blocks(self, keep: set[tuple[int, int]]) -> set[tuple[int, int]]:
        """The blocks that `keep` names: by their own bounds, or by the range Lean reported for the declaration (which starts at its docstring or
        keyword, inside the block, never at the `open … in` prefix line the block begins with)."""
        return {b for b in (self.block_of(s) for s, _ in keep) if b}

    def stays(self, block: tuple[int, int], kept: set[tuple[int, int]]) -> bool:
        """Whether a block is in the pruned text: Lean built it (it has a range) and it is kept, or it is glue that an attribute registers.
        A block without a range never stays, whatever names it: Lean never elaborated that text."""
        return block in self.ranged and (block in kept or block in self.code_attr)

    def block_of(self, line: int) -> tuple[int, int] | None:
        for s, e in self.blocks:
            if s <= line <= e:
                return (s, e)
        return None

    def text(self, keep: set[tuple[int, int]], before: int | None = None, strip_imports: bool = True) -> str:
        """The file with every block that does not stay removed, imports stripped (unless asked not to), up to line `before` (exclusive)."""
        out, i, n = [], 1, len(self.lines) if before is None else before - 1
        starts = {s: e for s, e in self.blocks}
        kept = self.kept_blocks(keep)
        while i <= n:
            if i in starts:
                s, e = i, starts[i]
                if self.stays((s, e), kept):
                    out.extend(self.lines[s - 1 : min(e, n)])
                i = e + 1
                continue
            ln = self.lines[i - 1]
            if not strip_imports or (not IMPORT_LINE.match(ln) and not KEYWORD_LINE.match(ln)):
                out.append(ln)
            i += 1
        text = re.sub(r"\n{3,}", "\n\n", "\n".join(out)).strip("\n")
        return text

    def leaks(self, text: str, keep: set[tuple[int, int]]) -> list[str]:
        """What survived pruning that should not have: every declaration in `text` (the pruned module) whose keyword line is not that of a block
        that stays, and every `… in` prefix that no declaration follows. Empty when the pruned text is glue plus whole blocks that stay. compose
        refuses a bundle on which this is not empty: a declaration that escapes pruning is unverified text, and once what it calls is cut the
        module does not build. Only column-0 command lines outside comments count, so prose in a module docstring that starts with "theorem"
        is not a declaration, and a `--` line inside a proof does not end it."""
        kept = self.kept_blocks(keep)
        allowed = {decl_core(self.lines, s, e).split("\n")[0].strip() for s, e in self.blocks if self.stays((s, e), kept)}
        tlines = text.split("\n")
        cmds = command_lines(tlines)
        out: list[str] = []
        for k, (no, ln) in enumerate(cmds):
            if IN_PREFIX.match(ln):
                nxt = cmds[k + 1][1] if k + 1 < len(cmds) else ""
                if not (IN_PREFIX.match(nxt) or LEAD_IN.match(nxt) or DECL_LINE.match(nxt)):
                    out.append(f"line {no}: dangling prefix: {ln.strip()[:80]}")
            else:
                core = ATTR_INLINE.sub("", ln).strip()  # `@[simp] theorem …`: the keyword line is what comes after the attribute
                if ln.lstrip().startswith("@["):
                    seg = "\n".join(tlines[no - 1 : cmds[k + 1][0] - 1 if k + 1 < len(cmds) else len(tlines)])
                    if (closed := attrs_end(seg)) > 0:
                        core = seg[closed:].strip().split("\n")[0].strip()  # an attribute over several lines: the keyword line follows its closing bracket
                if DECL_LINE.match(core) and core not in allowed:
                    out.append(f"line {no}: a declaration that is not a kept block: {core[:80]}")
                elif LEAD_IN.match(ln) and (ln.startswith("/--") or not core or core == ln.strip()):  # a docstring, or attributes on their own (not `@[expose] public section`)
                    nxt = cmds[k + 1][1] if k + 1 < len(cmds) else ""
                    if not nxt or NO_LEAD_IN.match(nxt):
                        out.append(f"line {no}: a docstring or attribute with no declaration after it: {ln.strip()[:80]}")
        return out

    def dangling(self, text: str, keep: set[tuple[int, int]]) -> list[str]:
        """Names the pruning removed that the pruned text still uses. A kept theorem can lean on a declaration (a `private theorem` in the same module, usually) that
        the closure did not reach, and then the module does not build on the tree. Only code counts (comments and strings are blanked), a name that another kept
        declaration also bears is not reported. Whole identifiers only, not after a `.`. A name is reported whatever its length (a short private helper that
        is called is as much a break as a long one), and so is one that kept code binds locally under the same name: the module is left out, which is the safe
        side (one module of yield; a module that cannot build is an ejection from the queue)."""
        from adapters import code_mask

        kept = self.kept_blocks(keep)
        gone: dict[str, int] = {}
        here: set[str] = set()
        for s, e in self.blocks:
            m = DECL_NAME.match(decl_core(self.lines, s, e))
            if not m:
                continue
            if self.stays((s, e), kept):
                here.add(m.group(1))
            else:
                gone.setdefault(m.group(1), s)
        mask = code_mask(text)
        code = "".join(c if k else (" " if c != "\n" else "\n") for c, k in zip(text, mask))
        return sorted(
            n for n in gone if n not in here and re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", code)
        )


def decl_core(lines: list[str], s: int, e: int) -> str:
    """The text of the declaration in lines s..e (1-based, inclusive) from its keyword line on: the `… in` prefix lines, docstrings, attribute
    and `--` comment lines before it are skipped. Empty when no keyword line is found."""
    i = s - 1
    while i < e:
        ln = lines[i].lstrip()
        if ln.startswith("@["):
            rest = ATTR_INLINE.sub("", ln).strip()
            if rest and rest != ln.strip():  # `@[simp] theorem …`: the declaration starts on this line, after the attribute
                return "\n".join([rest, *lines[i + 1 : e]]).strip()
            j, closed = i, 0
            while rest and j < e:  # an attribute that goes on over the next lines
                joined = "\n".join(lines[i : j + 1])
                closed = attrs_end(joined)
                if closed > 0:
                    if joined[closed:].strip():  # `(since := "…")] theorem kept …`: the declaration starts after the closing bracket
                        return "\n".join([joined[closed:].strip(), *lines[j + 1 : e]]).strip()
                    break
                j += 1
            i = j + 1
        elif not ln or IN_PREFIX.match(ln) or ln.startswith("--"):
            i += 1
        elif ln.startswith("/--") or ln.startswith("/-!"):
            while i < e and "-/" not in lines[i]:
                i += 1
            i += 1
        else:
            break
    return "\n".join(lines[i:e]).strip() if i < e else ""


def command_lines(lines: list[str]) -> list[tuple[int, str]]:
    """(1-based line, text) of every column-0 line outside block comments that starts a command (portfolio.COMMAND_START: a keyword, a
    docstring, an attribute, an `open`…; not a `|` alternative, not a `--` line). `/- … -/` nests; a docstring (`/--`, `/-!`) is a block
    comment too, except that its opening line is reported (it leads into a declaration)."""
    import portfolio

    out, depth = [], 0
    for no, ln in enumerate(lines, 1):
        if depth == 0 and ln and not ln[0].isspace() and not ln.startswith("--") and portfolio.COMMAND_START.match(ln):
            out.append((no, ln))
        i = 0
        while i < len(ln) - 1:
            two = ln[i : i + 2]
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/" and depth:
                depth -= 1
                i += 2
            elif depth == 0 and two == "--":
                break
            else:
                i += 1
    return out


def segments(lines: list[str]) -> list[tuple[int, int]]:
    """(first, last) lines of every top-level command: from a command line (command_lines) to the line before the next one."""
    starts = [no for no, _ in command_lines(lines)]
    return [(s, (starts[k + 1] - 1) if k + 1 < len(starts) else len(lines)) for k, s in enumerate(starts)]


def library_imports(lib: Path, mod: str, mods: set[str]) -> list[str]:
    path = lib / (mod.replace(".", "/") + ".lean")
    if not path.exists():
        return []
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import tolerant_build as tb

    return [d for d in tb.header_imports(path.read_text(errors="replace")) if d in mods]


def topo(mods: list[str], lib: Path, universe: set[str]) -> list[str]:
    """Dependency-first order of `mods` over the library's import graph (indirect imports count)."""
    out, seen = [], set()

    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        for d in library_imports(lib, m, universe):
            visit(d)
        if m in mods:
            out.append(m)

    for m in mods:
        visit(m)
    return out


def closure(lib: Path, mod: str, universe: set[str], memo: dict[str, set[str]]) -> set[str]:
    if mod not in memo:
        memo[mod] = set()
        s = {mod}
        for d in library_imports(lib, mod, universe):
            s |= closure(lib, d, universe, memo)
        memo[mod] = s
    return memo[mod]


def compose(a: argparse.Namespace) -> None:
    lib = Path(a.lib)
    log = Path(a.log).read_text(errors="replace")
    meta = json.loads(Path(a.meta).read_text())
    old_lines = json.loads(Path(a.lines).read_text()) if a.lines else {}
    deps = {}
    for m in re.finditer(r"REC_DEPS (\{.*?\}) REC_END", log, re.S):
        j = json.loads(re.sub(r"\s*\n\s*", "", m.group(1)))
        deps[j["name"]] = j
    # the source ranges Lean recorded while it built each module (TolerantBuild.lean): name -> (first line, last line)
    sidecars = {}
    for f in (lib / ".lake" / "build" / "lib" / "lean").rglob("*.olean.ranges.json"):
        rel = f.relative_to(lib / ".lake" / "build" / "lib" / "lean")
        mod = ".".join(rel.parts)[: -len(".olean.ranges.json")]
        sidecars[mod] = {n: (s, e) for n, s, e in json.loads(f.read_text())}
    universe = set(sidecars)
    modules = {m: Module(lib, m, list(sidecars[m].values())) for m in sidecars if (lib / (m.replace(".", "/") + ".lean")).exists()}

    def source_of(mod: str, const: str):
        """The range of a constant's source: its own, or the nearest prefix of its name that has one (auxiliary definitions,
        matchers, recursors, projections live in their parent's source)."""
        names = sidecars.get(mod, {})
        parts = const.split(".")
        while parts:
            r = names.get(".".join(parts))
            if r:
                return r
            parts.pop()
        return None

    memo: dict[str, set[str]] = {}
    repo = meta["repo"].rstrip("/").removesuffix(".git")
    out, stats = [], defaultdict(int)
    for name, j in deps.items():
        if "error" in j:
            stats["no_dependency_info"] += 1
            continue
        mod = j["module"]
        own = modules.get(mod)
        if own is None:
            stats["no_source_file"] += 1
            continue
        blocks = defaultdict(set)
        for m, c in j["consts"]:
            r = source_of(m, c)
            if r:
                blocks[m].add(tuple(r))
        # the theorem's own block: the one among its blocks that contains no other declaration's start before it ends... use the name
        theorem_block = None
        for s, e in sorted(blocks.get(mod, ()), key=lambda b: (b[1] - b[0])):
            seg = "\n".join(own.lines[s - 1 : e])
            bare = name.split(".")[-1]
            if re.search(r"(?:theorem|lemma)\s+(?:\S*\.)?" + re.escape(bare) + r"(?![\w'])", seg):
                theorem_block = (s, e)
                break
        if theorem_block is None:
            stats["theorem_block_not_found"] += 1
            continue
        ts, te = theorem_block
        keep_own = {b for b in blocks.get(mod, ()) if b[1] < ts}
        mods_needed = closure(lib, mod, universe, memo) - {mod}
        prelude = []
        for x in topo(sorted(mods_needed), lib, universe):
            if x not in modules:
                continue
            body = modules[x].text(blocks.get(x, set()))
            # a module with ANY text left (a declaration the theorem uses, or glue: `scoped[Indicator] notation`, an `open`, a
            # namespace) is part of the environment the statement is read in; a module that is only comments is not
            if re.sub(r"/-.*?-/|--[^\n]*", "", body, flags=re.S).strip():
                prelude.append(f"-- [Emissary prelude] {x} — verbatim (imports stripped)\n{body}\n")
        prefix = own.text(keep_own, before=ts)
        src = str(own.path.relative_to(lib))
        line = old_lines.get(name, ts)
        theorem = "\n".join(own.lines[ts - 1 : te])
        theorem = re.sub(r"^\s*/--.*?-/\s*", "", theorem, count=1, flags=re.S)  # a docstring belongs to the source, not the statement
        full = (
            "set_option linter.all false -- [Emissary] lints are not drift; the kernel decides\n\n"
            + "\n".join(prelude)
            + f"\n-- [Emissary] {src}, everything before line {line} (imports stripped; sibling theorems the target does not use omitted)\n"
            + prefix
            + "\n\n"
            + theorem
            + "\n"
        )
        out.append({"name": name, "sourcePath": src, "sourceUrl": f"{repo}/blob/{meta['commit']}/{src}", "proof": full})
        stats["composed"] += 1
    Path(a.out).write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in out))
    print(json.dumps(dict(stats)))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    l = sub.add_parser("lean")
    for f in ("lib", "names", "out"):
        l.add_argument(f"--{f}", required=True)
    c = sub.add_parser("compose")
    for f in ("lib", "log", "meta", "out"):
        c.add_argument(f"--{f}", required=True)
    c.add_argument("--names", default="")
    c.add_argument("--lines", default="")
    a = ap.parse_args()
    lean_file(a) if a.cmd == "lean" else compose(a)
