import Lean

/-!
Cross-toolchain constant transfer, rewritten to run in `CoreM` and add declarations via
`Lean.addDecl` (the same primitive normal command elaboration uses) rather than manually
threading a bare `Kernel.Environment`. The original `lean4checker` `Environment.replay'`
(vendored in `Vendor/Replay.lean`) adds declarations to the kernel's constant map directly,
which the *kernel* accepts correctly, but does not update the newer async-elaboration
`VisibilityMap` that Lean's own name resolution consults — so a kernel-only replay is
kernel-sound but not citable by ordinary syntax afterward. Going through `Lean.addDecl`
keeps both in sync, because it's the actual code path every real declaration goes through.
-/

namespace TengokuImport

open Lean

structure ReplayState where
  remaining             : NameSet := {}
  pending               : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors    : NameSet := {}

abbrev ReplayM := ReaderT (Std.HashMap Name ConstantInfo) <| StateRefT ReplayState CoreM

def isTodo (name : Name) : ReplayM Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

mutual

partial def replayConstant (name : Name) : ReplayM Unit := do
  if ← isTodo name then
    let newConstants ← read
    let some ci := newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo info =>
        Lean.addDecl (Declaration.defnDecl info)
      | .thmInfo info =>
        let env ← getEnv
        let mut skip := false
        if let some (.thmInfo info') := env.find? ci.name then
          if info.name == info'.name && info.type == info'.type &&
             info.levelParams == info'.levelParams && info.all == info'.all then
            skip := true
        if !skip then
          Lean.addDecl (Declaration.thmDecl info)
      | .axiomInfo info =>
        Lean.addDecl (Declaration.axiomDecl info)
      | .opaqueInfo info =>
        Lean.addDecl (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do
          let some ci := newConstants[n]? | unreachable!
          pure ci
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          let ctors ← ci.inductiveVal!.ctors.mapM fun n => do
            let some c := newConstants[n]? | unreachable!
            pure c
          pure (ci, ctors)
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun (ci, ctors) =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        Lean.addDecl (Declaration.inductDecl lparams nparams types false)
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        replayConstant `Eq
        Lean.addDecl Declaration.quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : ReplayM Unit := do
  for n in names do replayConstant n

end

def checkPostponedConstructors : ReplayM Unit := do
  let env ← getEnv
  let newConstants ← read
  for ctor in (← get).postponedConstructors do
    match env.find? ctor, newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if !(info == info') then throwError "Invalid constructor {ctor}"
    | _, _ => throwError "No such constructor {ctor}"

def checkPostponedRecursors : ReplayM Unit := do
  let env ← getEnv
  let newConstants ← read
  for ctor in (← get).postponedRecursors do
    match env.find? ctor, newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !(info == info') then throwError "Invalid recursor {ctor}"
    | _, _ => throwError "No such recursor {ctor}"

/-- Replay `newConstants` directly into the ambient `CoreM` environment via `Lean.addDecl`,
so the result is citable by ordinary elaboration immediately afterward. -/
def replayIntoCoreEnv (newConstants : Std.HashMap Name ConstantInfo) : CoreM Unit := do
  let mut remaining : NameSet := {}
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let go : ReplayM Unit := do
    for n in remaining do
      replayConstant n
    checkPostponedConstructors
    checkPostponedRecursors
  let _ ← StateRefT'.run (s := ({ remaining } : ReplayState)) (ReaderT.run go newConstants)

end TengokuImport
