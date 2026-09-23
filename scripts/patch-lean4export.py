#!/usr/bin/env python3
"""patch-lean4export.py <lean4export checkout> — two small changes, each idempotent.

1. `--only-listed`: stock lean4export dumps every constant the listed ones reach,
   transitively — for a Carleson module that is 49,000 Mathlib theorems and a
   467 MB file per module, which Gate 2 would re-parse on every call. Gate 2
   resolves Mathlib and core names natively (its environment is the tree), so the
   export only needs the constants named on the command line — the corpus-side
   closure the bridge computes — with everything else left as a name.
2. Listed names are decoded with `Syntax.decodeNameLit … |>.get!` in newer
   commits, which panics on the hygienic names a closure contains
   (`wrapped._@.Carleson.Defs.2925746003._hygCtx._hyg.2`); fall back to
   `String.toName`.

Anchors are the same in every lean4export commit from v4.15 on;
build-lean4export.sh runs this after checking out the commit for a toolchain.
"""

import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
export, main = root / "Export.lean", root / "Main.lean"
et, mt = export.read_text(encoding="utf-8"), main.read_text(encoding="utf-8")
done = []

FIELDS = """structure State where
  /-- `--only-listed`: dump only the constants named on the command line; what they
  reference stays a name, for a reader that resolves the rest natively (Tengoku's Gate 2). -/
  onlyListed : Bool := false
  listed : NameHashSet := {}
"""
GATE_ANCHOR = "modify fun st => { st with visitedConstants := st.visitedConstants.insert c }"
GATE_RE = re.compile(r"^([ \t]*)" + re.escape(GATE_ANCHOR) + r"[ \t]*$", re.M)
GATE = r"\1if (← get).onlyListed && !(← get).listed.contains c then return" + "\n" + r"\1" + GATE_ANCHOR
MAIN_ANCHOR = "    let _ ← initState env opts\n"
MAIN = MAIN_ANCHOR + """    if opts.contains "--only-listed" then
      modify fun st => { st with onlyListed := true, listed := constants.foldl (·.insert ·) {} }
"""
# In --only-listed mode a theorem's proof term is never read (Gate 2 replays
# theorems as axioms), and Sendov-style computational proofs run to hundreds of
# MB: a placeholder stands in for the value, so only the type is dumped.
THM_OLD = """  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("thm", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),"""
THM_NEW = """  | .thmInfo val => do
    dumpDeps val.type
    let value := if (← get).onlyListed then Expr.const ``True.intro [] else val.value
    if !(← get).onlyListed then dumpDeps val.value
    dumpObj [
      ("thm", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr value),"""
DECODE_OLDS = ['Syntax.decodeNameLit ("`" ++ c) |>.get!', '(Syntax.decodeNameLit ("`" ++ c)).getD c.toName']
DECODE_NEW = "decodeClosureName c"
DECODER = '''/-- A listed constant as `Name.toString` printed it. A hygienic name
(`wrapped._@.Carleson.Defs.2925746003._hygCtx._hyg.2`, an `irreducible_def`'s
internals) is no name literal and `String.toName` gives up on it; its printed
components are still exactly its components, so rebuild it from them. -/
def decodeClosureName (s : String) : Name :=
  (Syntax.decodeNameLit ("`" ++ s)).getD <|
    (s.splitOn ".").foldl (fun n p => if p.isNat then .num n p.toNat! else .str n p) .anonymous

def main (args : List String) : IO Unit := do'''

if "onlyListed : Bool" not in et:
    if et.count("structure State where\n") != 1:
        sys.exit("lean4export: `structure State where` not found exactly once — the patch needs updating for this commit")
    et = et.replace("structure State where\n", FIELDS, 1)
    done.append("State fields")
if "(← get).onlyListed" not in et:
    # Every place a constant `c` is marked visited is a place it is about to be dumped: gate them
    # all, each at its own indentation (the inductive case sits deeper than dumpConstant's head).
    if not GATE_RE.search(et):
        sys.exit("lean4export: dumpConstant anchor not found — the patch needs updating for this commit")
    et = GATE_RE.sub(GATE, et)
    done.append("dumpConstant gate")
if '"--only-listed"' not in mt:
    if mt.count(MAIN_ANCHOR) != 1 or "for c in constants do" not in mt:
        sys.exit("lean4export: Main.lean anchors not found — the patch needs updating for this commit")
    mt = mt.replace(MAIN_ANCHOR, MAIN, 1)
    done.append("--only-listed option")
for old in DECODE_OLDS:
    if old in mt:
        mt = mt.replace(old, DECODE_NEW)
        done.append("name decoding")
if "def decodeClosureName" not in mt:
    if mt.count("def main (args : List String) : IO Unit := do") != 1:
        sys.exit("lean4export: `def main` not found exactly once — the patch needs updating for this commit")
    mt = mt.replace("def main (args : List String) : IO Unit := do", DECODER, 1)
    done.append("decodeClosureName")

# 3. `--batch=<file>`: one import for many modules. Importing the environment is the whole
# cost of an export (tnlean: ~110 s per module for a dump of a few seconds), so a batch
# imports the union of its modules once and dumps each module's listed constants, from a
# fresh exporter state, into its own file. Each line of the file: module, output path, names,
# tab-separated. The single-module command line is unchanged.
BATCH = '''/-- `--batch=<file>`: import the union of the listed modules once and dump each module's
listed constants, with a fresh exporter state, into its own file (see patch-lean4export.py). -/
def runBatch (file : String) (opts : List String) : IO Unit := do
  let lines ← IO.FS.lines file
  let groups := lines.toList.filterMap fun l =>
    match l.splitOn "\\t" with
    | mod :: out :: names => if mod.isEmpty || out.isEmpty then none else some (mod, out, names.filter (· ≠ ""))
    | _ => none
  let env ← importModules (groups.map fun (mod, _, _) => { module := decodeClosureName mod }).toArray {}
  for (_, out, names) in groups do
    let h ← IO.FS.Handle.mk out .write
    let prev ← IO.setStdout (IO.FS.Stream.ofHandle h)
    try
      M.run env do
        let _ ← initState env opts
        let constants := names.map decodeClosureName
        modify fun st => { st with onlyListed := true, listed := constants.foldl (·.insert ·) {} }
        dumpMetadata
        for c in constants do
          modify (fun st => { st with noMDataExprs := {} })
          dumpConstant c
    finally
      h.flush
      let _ ← IO.setStdout prev

def main (args : List String) : IO Unit := do'''
BATCH_DISPATCH_ANCHOR = "  let (opts, args) := args.partition (fun s => s.startsWith \"--\" && s.length ≥ 3)\n"
BATCH_DISPATCH = BATCH_DISPATCH_ANCHOR + '''  if let some b := opts.find? (·.startsWith "--batch=") then
    return ← runBatch (String.mk (b.toList.drop 8)) opts
'''
if "--batch=" not in mt:
    if mt.count("def main (args : List String) : IO Unit := do") != 1 or mt.count(BATCH_DISPATCH_ANCHOR) != 1:
        sys.exit("lean4export: batch anchors not found — the patch needs updating for this commit")
    mt = mt.replace("def main (args : List String) : IO Unit := do", BATCH, 1)
    mt = mt.replace(BATCH_DISPATCH_ANCHOR, BATCH_DISPATCH, 1)
    done.append("--batch mode")

if THM_OLD in et:
    et = et.replace(THM_OLD, THM_NEW, 1)
    done.append("theorem values elided under --only-listed")
elif "let value := if (← get).onlyListed" not in et:
    sys.exit("lean4export: thmInfo anchor not found — the patch needs updating for this commit")
export.write_text(et, encoding="utf-8")
main.write_text(mt, encoding="utf-8")
print("lean4export: " + (", ".join(done) if done else "already patched"))
