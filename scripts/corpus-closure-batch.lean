-- Corpus-side closure for MANY modules in one process (scripts/setup-source.mjs).
-- Same output per module as the bridge's single-module corpus-closure program
-- (public/local-claude-bridge.mjs, CORPUS_CLOSURE_LEAN), one section each:
--   == <module>
--   <name>\t<module>\t<corpus deps, comma-separated>
-- Importing every module once is what makes setting up a 400-module library
-- take minutes instead of hours: the environment load (all of Mathlib) is
-- paid once, not once per module.
--   lake env lean --run corpus-closure-batch.lean <corpus-module-prefix> <module>...
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let pfx :: mods := args | throw (IO.userError "usage: corpus-closure-batch <corpus-module-prefix> <module>...")
  initSearchPath (← findSysroot)
  let modNames := mods.map String.toName
  let env ← importModules (modNames.map fun m => { module := m }).toArray {}
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind fun idx => env.header.moduleNames[idx]?
  let isCorpus (n : Name) : Bool :=
    match moduleOf n with
    | some m => m.toString.startsWith pfx
    | none => false
  -- Constants grouped by defining module, computed once.
  let mut byModule : Std.HashMap Name (List Name) := {}
  for (n, _) in env.constants.toList do
    if let some m := moduleOf n then
      if modNames.contains m then
        byModule := byModule.insert m (n :: (byModule.getD m []))
  for modName in modNames do
    IO.println s!"== {modName}"
    let mut stack : List Name := byModule.getD modName []
    let mut visited : NameSet := {}
    let mut out : Array Name := #[]
    while true do
      match stack with
      | [] => break
      | n :: rest =>
        stack := rest
        if visited.contains n then continue
        visited := visited.insert n
        if !isCorpus n then continue
        match env.find? n with
        | none => continue
        | some ci =>
          out := out.push n
          for d in ci.getUsedConstantsAsSet.toList do
            if !visited.contains d then stack := d :: stack
    for n in out do
      let m := (moduleOf n).map toString |>.getD ""
      let deps := match env.find? n with
        | some ci => ci.getUsedConstantsAsSet.toList.filter isCorpus |>.map toString
        | none => []
      IO.println s!"{n}\t{m}\t{String.intercalate "," deps}"
