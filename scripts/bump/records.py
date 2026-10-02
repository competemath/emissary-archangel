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

  records.py lean    --lib DIR --names names.json --modules M,M --out records-deps.lean
  records.py compose --lib DIR --log records-deps.log --names names.json --meta setup.ci.json --out composed.jsonl [--lines old-lines.json]
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

/-- Where a constant's source is: itself, or the nearest prefix of its name that has declaration ranges
(auxiliary definitions, matchers, recursors, projections live in their parent's source). -/
partial def recSource (n : Name) : MetaM (Option DeclarationRanges) := do
  if let some r ← findDeclarationRanges? n then return some r
  match n with
  | .str p _ | .num p _ => recSource p
  | .anonymous => return none

/-- Every declaration range of a module: what the source file's pruneable blocks are. -/
elab "#records_modules " mods:str : command => do
  for m in (mods.getString.splitOn ",").filter (· != "") do
    let mn := recParse m
    let ranges ← liftTermElabM do
      let env ← getEnv
      let some idx := env.getModuleIdx? mn | return #[]
      let mut out : Array Json := #[]
      for c in env.header.moduleData[idx.toNat]!.constNames do
        if let some r ← recSource c then
          out := out.push (Json.arr #[toJson r.range.pos.line, toJson r.range.endPos.line])
      return out
    logInfo m!"REC_MOD {(Json.mkObj [("module", toJson m), ("ranges", Json.arr ranges)]).compress} REC_END"

/-- For each name: its module, and the source blocks (module, first line, last line) of every library declaration in the
closure of its type and value (proofs included: the record has to compile). -/
elab "#records_deps " names:str " in " libs:str : command => do
  let libMods : NameSet := (libs.getString.splitOn ",").foldl (fun s x => if x == "" then s else s.insert (recParse x)) {}
  for s in (names.getString.splitOn ",").filter (· != "") do
    let n := recParse s
    let j ← liftTermElabM do
      let env ← getEnv
      let isOwn (c : Name) : Bool := match recModOf env c with | some m => libMods.contains m | none => false
      let mut seen : NameSet := {}
      let mut stack : List Name := [n]
      let mut blocks : Array Json := #[]
      let mut keys : Std.HashSet (Name × Nat × Nat) := {}
      while !stack.isEmpty do
        match stack with
        | [] => pure ()
        | c :: rest =>
          stack := rest
          if seen.contains c then continue
          seen := seen.insert c
          let some ci := env.find? c | continue
          for u in ci.getUsedConstantsAsSet.toList do
            if isOwn u && !seen.contains u then stack := u :: stack
          if let some m := recModOf env c then
            if let some r ← recSource c then
              let key := (m, r.range.pos.line, r.range.endPos.line)
              unless keys.contains key do
                keys := keys.insert key
                blocks := blocks.push (Json.arr #[toJson m.toString, toJson r.range.pos.line, toJson r.range.endPos.line])
      let some m := recModOf env n | return Json.mkObj [("name", toJson s), ("error", toJson "not in an imported module")]
      return Json.mkObj [("name", toJson s), ("module", toJson m.toString), ("blocks", Json.arr blocks)]
    logInfo m!"REC_DEPS {j.compress} REC_END"
'''


def lean_file(a: argparse.Namespace) -> None:
    names = json.loads(Path(a.names).read_text())  # {module: [declaration names]}
    modules = sorted(names)
    lines = ["import Lean", "import Mathlib"] + [f"import {m}" for m in modules] + [LEAN]
    lines.append(f'#records_modules "{",".join(modules)}"')
    allmods = ",".join(modules)
    for m in modules:
        ns = names[m]
        for i in range(0, len(ns), 25):
            lines.append(f'#records_deps "{",".join(ns[i:i + 25])}" in "{allmods}"')
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
NOTATION = re.compile(r"^\s*(?:scoped\s+|local\s+)?(?:notation|infix[lr]?|prefix|postfix|macro|macro_rules|syntax|elab|declare_syntax_cat)\b", re.M)
IN_PREFIX = re.compile(r"^\s*(?:open|set_option|attribute|local|universe|variable|namespace|section)\b.*\bin\s*$")


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


class Module:
    def __init__(self, lib: Path, mod: str, ranges: list[tuple[int, int]]):
        path = lib / (mod.replace(".", "/") + ".lean")
        self.path = path
        self.lines = path.read_text(errors="replace").split("\n")
        self.blocks: list[tuple[int, int]] = []
        for s, e in merge_ranges(ranges):
            s0 = s
            # `open Foo in` / `set_option … in` lines directly above a declaration belong to it
            while s0 > 1 and IN_PREFIX.match(self.lines[s0 - 2]):
                s0 -= 1
            text = "\n".join(self.lines[s0 - 1 : e])
            if DECL.match(text.lstrip()) and not CODE_ATTR.match(text.lstrip()):
                self.blocks.append((s0, e))
        self.blocks.sort()

    def block_of(self, line: int) -> tuple[int, int] | None:
        for s, e in self.blocks:
            if s <= line <= e:
                return (s, e)
        return None

    def text(self, keep: set[tuple[int, int]], before: int | None = None) -> str:
        """The file with every pruneable block outside `keep` removed, imports stripped, up to line `before` (exclusive)."""
        out, i, n = [], 1, len(self.lines) if before is None else before - 1
        starts = {s: e for s, e in self.blocks}
        while i <= n:
            if i in starts:
                s, e = i, starts[i]
                if (s, e) in keep:
                    out.extend(self.lines[s - 1 : min(e, n)])
                i = e + 1
                continue
            ln = self.lines[i - 1]
            if not IMPORT_LINE.match(ln) and not KEYWORD_LINE.match(ln):
                out.append(ln)
            i += 1
        text = re.sub(r"\n{3,}", "\n\n", "\n".join(out)).strip("\n")
        return text


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
    mod_ranges: dict[str, list[tuple[int, int]]] = {}
    for m in re.finditer(r"REC_MOD (\{.*?\}) REC_END", log, re.S):
        j = json.loads(m.group(1))
        mod_ranges[j["module"]] = [tuple(r) for r in j["ranges"]]
    deps = {}
    for m in re.finditer(r"REC_DEPS (\{.*?\}) REC_END", log, re.S):
        j = json.loads(re.sub(r"\s*\n\s*", "", m.group(1)))
        deps[j["name"]] = j
    universe = set(mod_ranges)
    modules = {m: Module(lib, m, mod_ranges[m]) for m in mod_ranges if (lib / (m.replace(".", "/") + ".lean")).exists()}
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
        for m, s, e in j["blocks"]:
            blocks[m].add((s, e))
        mine = [b for b in blocks.get(mod, ()) if own.block_of(b[0]) == b or True]
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
            if blocks.get(x) or NOTATION.search(body):
                if body.strip():
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
