/-
Leak scan for the merge queue: what a library changes for everybody else.

A global instance or simp lemma whose statement mentions only constants of OTHER libraries (Mathlib, core, a sibling library) changes how
every statement of every other library elaborates once the tree is imported as one: `attribute [instance] Matrix.linftyOpNormedAddCommGroup`
made `‖A‖` the L∞ operator norm on every matrix in the tree (Mathlib keeps it `scoped` on purpose). An instance or simp lemma about the
library's own types can never fire elsewhere and is harmless. This reads the compiled environment (not the text): every global entry that
the library's modules registered in the instance and simp extensions, and whether its statement mentions a constant of the library.

One more shape is a leak although the statement does mention the library: an instance of ANOTHER library's class that has outParams, whose input
arguments and hypotheses mention nothing of the library (`instance : HMul R G (FreeModule R G)` for all `R G`, lean-pool GroupRing, 2026-10-16). The result
of `HMul` is an outParam, so instance search for `HMul ℝ ℝ ?γ` finds it and every product of reals in the tree becomes a group-ring element: `positivity`
and `linarith` fail with `failed to synthesize HAdd (ℝ[ℝ]) ℝ ℝ`. An instance of the library's own class, or one with a hypothesis about the library, is
not a leak (nothing else asks for that class, or the hypothesis cannot be met elsewhere).

And one more through the library's OWN class: a class that `extends HDiv P P I` has the global instance `Torsor.toHDiv : [Torsor P I] → HDiv P P I`, which
is harmless until the library declares `instance : Torsor Pitch Interval` with `abbrev Pitch := Int`, `abbrev Interval := Int` (prismriver, 2026-10-16): that is
`Torsor Int Int`, so `HDiv ℤ ℤ ?γ` finds `Torsor.toHDiv` before `Int.instHDiv` and `omega` fails with `Application type mismatch … Prismriver.EqualTemp.Interval`.
An instance of a class that has such a projection, whose arguments (after unfolding reducible definitions) mention nothing of the library, is a leak.

  lake build tengoku-leakscan
  lake env .lake/build/bin/tengoku-leakscan --module Tengoku.Lib [--prefix Tengoku.Lib …] [--tree-prefix Tengoku.Lib] [--strict]

Report only unless `--strict` (then exit 1 when anything leaks). `--prefix` defaults to the modules named. `--tree-prefix` is put in front
of every module name in the report: the factory scans the library under its own module names, and the report is read in the tree's
(`Tengoku.<Library>.<module>`, scripts/bump/scope_rewrite.py).
-/
import Lean
open Lean Meta

/-- one global registration whose statement mentions nothing of its own library -/
structure Leak where
  kind : String
  name : Name
  registeredIn : Name
  /-- where it is declared, when that is a module of the library (an `attribute` command registers a declaration of ANOTHER library) -/
  line : Option Nat
  declaredIn : Option Name
  /-- an instance's priority when it is not the default (1000): a local re-registration must keep it -/
  prio : Option Nat := none

structure Counts where
  inst : Nat := 0
  instScoped : Nat := 0
  simp : Nat := 0
  simpScoped : Nat := 0
  /-- declarations of the library whose name has one component: nothing in the name says which library they belong to -/
  roots : Array Name := #[]

def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | e => e

/-- the part of a simp lemma's statement that triggers it: the left-hand side of `=`/`↔`, else the statement -/
def trigger (ty : Expr) : Expr :=
  let b := stripForall ty
  match b.eq? with
  | some (_, l, _) => l
  | none => match b.iff? with
    | some (l, _) => l
    | none => b

/-- the conclusion of an instance type, and the types of its binders -/
def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

def binderTypes : Expr → List Expr
  | .forallE _ d b _ => d :: binderTypes b
  | _ => []

/-- an instance of a class of ANOTHER library, with outParams, whose input arguments and hypotheses mention nothing of this library: it fires for every input of
that shape, whatever its result type says (the result of `HMul`, `HAdd`, `HSMul`, `GetElem`, `Membership` is an outParam, so the result type does not pin it) -/
def unpinned (env : Environment) (ty : Expr) (own : Name → Bool) : Bool :=
  let concl := conclusion ty
  match concl.getAppFn.constName? with
  | none => false
  | some cls =>
    match getOutParamPositions? env cls with
    | none => false
    | some outs =>
      if outs.isEmpty || own cls then false else
      let args := concl.getAppArgs
      let ins := ((List.range args.size).filter fun i => !outs.contains i).map fun i => args[i]!
      !(ins.any (·.getUsedConstants.any own) || (binderTypes ty).any (·.getUsedConstants.any own))

/-- the head class of each hypothesis of an instance type that is a class of this library -/
def ownHypClasses (env : Environment) (ty : Expr) (own : Name → Bool) : List Name :=
  (binderTypes ty).filterMap fun b => (conclusion b).getAppFn.constName?
    |>.filter fun c => own c && isClass env c

/-- an instance of a class that has a projection into another library's class with outParams (`Torsor.toHDiv`), at arguments that mention nothing of the
library once reducible definitions are unfolded (`Torsor Pitch Interval` with `abbrev Pitch := Int` is `Torsor Int Int`) -/
def pinnedToForeign (reach : NameSet) (ty : Expr) (own : Name → Bool) : MetaM Bool := do
  let some cls := (conclusion ty).getAppFn.constName? | return false
  unless reach.contains cls do return false
  forallTelescope ty fun xs concl => do
    let tys ← xs.mapM inferType
    let all := tys ++ concl.getAppArgs
    let red ← all.mapM fun a => withReducible (reduce a (explicitOnly := false) (skipTypes := false) (skipProofs := false))
    return !red.any (·.getUsedConstants.any own)

def scan (pfxs : List Name) : CoreM (Array Leak × Counts) := do
  let env ← getEnv
  let idxs := (List.range env.header.moduleNames.size).filter fun i => pfxs.any (·.isPrefixOf env.header.moduleNames[i]!)
  -- ownership is per library: a registration of library A that mentions only constants of another selected library B touches nothing of A
  let ownBy (p : Name) (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some m => p.isPrefixOf env.header.moduleNames[m]!
    | none => false
  -- the classes of the library through which a global instance of another library's class with outParams is reachable, directly (`Torsor.toHDiv`) or through
  -- a projection into such a class of the library (`Scale.toTorsor`)
  let mut reach : NameSet := {}
  let mut edges : Array (Name × List Name) := #[]
  for i in idxs do
    let modName := env.header.moduleNames[i]!
    let some libPfx := pfxs.find? (·.isPrefixOf modName) | continue
    let own := ownBy libPfx
    for e in instanceExtension.ext.getModuleEntries env i do
      if let .global ie := e then
        let n := ie.globalName?.getD (ie.val.constName?.getD `_)
        let ty := ((env.find? n).map (·.type)).getD (.sort .zero)
        let hyps := ownHypClasses env ty own
        if hyps.isEmpty then continue
        let concl := conclusion ty
        if let some cls := concl.getAppFn.constName? then
          -- an edge that mentions a constant of the library is about the library's type (`[C α] → D (Lib.Wrap α)` is about `Lib.Wrap α`, not about `α`); one that is
          -- foreign all through still reaches the foreign type (`[C α] → D (List α)` makes `D (List Int)` of `C Int`)
          if own cls then
            if concl.getAppArgs.any (·.getUsedConstants.any own) then pure () else edges := edges.push (cls, hyps)
          else if let some outs := getOutParamPositions? env cls then
            let args := concl.getAppArgs
            let ins := ((List.range args.size).filter fun j => !outs.contains j).map fun j => args[j]!
            unless outs.isEmpty || ins.any (·.getUsedConstants.any own) do
              for c in hyps do reach := reach.insert c
  for _ in [0:edges.size + 1] do  -- until a round adds nothing (a chain has at most as many links as there are edges)
    let mut grew := false
    for (d, cs) in edges do
      if reach.contains d then
        for c in cs do
          unless reach.contains c do
            reach := reach.insert c
            grew := true
    unless grew do break
  let mut leaks : Array Leak := #[]
  let mut counts : Counts := {}
  for i in idxs do
    let modName := env.header.moduleNames[i]!
    let some libPfx := pfxs.find? (·.isPrefixOf modName) | continue
    let own := ownBy libPfx
    for e in instanceExtension.ext.getModuleEntries env i do
      match e with
      | .scoped _ _ => counts := { counts with instScoped := counts.instScoped + 1 }
      | .global ie =>
        counts := { counts with inst := counts.inst + 1 }
        let n := ie.globalName?.getD (ie.val.constName?.getD `_)
        let ty := ((env.find? n).map (·.type)).getD (.sort .zero)
        let viaOwnClass ← (pinnedToForeign reach ty own).run'
        unless ty.getUsedConstants.any own && !unpinned env ty own && !viaOwnClass do
          let r ← findDeclarationRanges? n
          let dm := (env.getModuleIdxFor? n).bind fun m => env.header.moduleNames[m]?
          leaks := leaks.push { kind := "instance", name := n, registeredIn := modName, declaredIn := dm,
                                line := if dm == some modName then r.map (·.range.pos.line) else none,
                                prio := if ie.priority == 1000 then none else some ie.priority }
    for e in simpExtension.ext.getModuleEntries env i do
      match e with
      | .scoped _ _ => counts := { counts with simpScoped := counts.simpScoped + 1 }
      | .global (.thm t) =>
        counts := { counts with simp := counts.simp + 1 }
        let n := t.origin.key
        let rule := t.proof.constName?.getD n  -- an auxiliary or reversed rule has its own type; `n` stays the name reported
        let ty := ((env.find? rule).map (·.type)).getD (.sort .zero)
        unless (trigger ty).getUsedConstants.any own do
          let r ← findDeclarationRanges? n
          let dm := (env.getModuleIdxFor? n).bind fun m => env.header.moduleNames[m]?
          leaks := leaks.push { kind := "simp", name := n, registeredIn := modName, declaredIn := dm,
                                line := if dm == some modName then r.map (·.range.pos.line) else none }
      | .global _ => pure ()
  for (n, _) in env.constants.map₁.toList do
    if let some m := env.getModuleIdxFor? n then
      if idxs.contains m && n.isAtomic && !n.isInternal && !n.hasMacroScopes then
        counts := { counts with roots := counts.roots.push n }
  return (leaks, counts)

def report (treePrefix : Name) (leaks : Array Leak) (c : Counts) : List String :=
  let rows := leaks.toList.map fun l =>
    s!"leak: {l.kind} {l.name} registered in {treePrefix ++ l.registeredIn}" ++
      (match l.prio with | some p => s!" (priority {p})" | none => "") ++
      (match l.line, l.declaredIn with
       | some n, _ => s!" (declared at line {n})"
       | none, some m => s!" (declared in {m}: an `attribute` command of the library turns it on)"
       | none, none => "")
  -- the totals come first (a report cut to its first lines keeps them), then every leak, then every root-level name
  [s!"leakscan: {c.inst} global instances ({(leaks.filter (·.kind == "instance")).size} can fire outside the library), {c.instScoped} scoped; " ++
    s!"{c.simp} global simp lemmas ({(leaks.filter (·.kind == "simp")).size} trigger on nothing of the library), {c.simpScoped} scoped",
   s!"roots: {c.roots.size} declarations of the library are in the root namespace (nothing in their names tells libraries apart; a second library declaring one fails to import)"]
    ++ rows ++ c.roots.toList.map fun n => s!"root: {n}"

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let flag (f : String) := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == f then some b.toName else none
  let treePrefix := (flag "--tree-prefix").headD .anonymous
  let mods := flag "--module"
  let pfxs := if (flag "--prefix").isEmpty then mods else flag "--prefix"
  if mods.isEmpty then
    IO.eprintln "usage: tengoku-leakscan --module <M> [--module <M>…] [--prefix <P>…] [--tree-prefix <P>] [--strict]"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<tengoku-leakscan>", fileMap := default, maxHeartbeats := 0 }
  let ((leaks, counts), _) ← (scan pfxs).toIO ctx { env }
  for ln in report treePrefix leaks counts do IO.println ln
  return (if argv.contains "--strict" && !leaks.isEmpty then 1 else 0)
