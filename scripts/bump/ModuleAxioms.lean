/-
ModuleAxioms — the merge queue's axiom check (the tree's TengokuAxioms.lean), with the module of every offender in its output, so that the module can be dropped.

  lake env lean --run scripts/bump/ModuleAxioms.lean modules.txt        (in the tree, after the build; scripts/bump/tree_verify.py writes modules.txt)
  modules.txt: one module per line, exact names, without guillemets (`Tengoku.Lib.Foo.A-B`): the declarations of exactly these modules are checked
  prints, for every declaration that rests on an axiom other than propext, Classical.choice, Quot.sound:
      AXIOM <TAB> module <TAB> declaration <TAB> the axioms, separated by spaces
  and last:   axioms: N declarations checked, M with non-standard axioms
  The exit status says only that the program ran (0): the offenders are in the output, and a log that has no `axioms:` line is a run that did not finish.

Gate 2 checks theorems; the tree checks every declaration (an instance made by `deriving Repr` on a Finset product rests on `lcProof`: lean-pool part 10, 2026-10-12).
The loop is TengokuAxioms.lean's, so the two agree on what is checked: every constant that is not internal and has no macro scopes.
-/
import Lean

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def check (mods : NameSet) : CoreM UInt32 := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let mut bad := 0
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := moduleNames[idx.toNat]? | continue
    if !mods.contains m then continue
    if n.isInternal || n.hasMacroScopes then continue
    let axioms ← collectAxioms n
    checked := checked + 1
    let extra := axioms.filter (!allowed.contains ·)
    if !extra.isEmpty then
      bad := bad + 1
      IO.println s!"AXIOM\t{m}\t{n}\t{" ".intercalate (extra.toList.map toString)}"
  IO.println s!"axioms: {checked} declarations checked, {bad} with non-standard axioms"
  return 0

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let [file] := argv | IO.eprintln "usage: ModuleAxioms.lean <modules.txt>"; return 2
  let names := ((← IO.FS.lines file).toList.map String.trim).filter (· != "") |>.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (names.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<ModuleAxioms>", fileMap := default, maxHeartbeats := 0 }
  let (code, _) ← (check (names.foldl (fun s m => s.insert m) {})).toIO ctx { env }
  return code
