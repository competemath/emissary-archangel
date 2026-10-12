/-
BundleKeep — which library constants a bundle must keep (scripts/bump/bundle.py compose reads the line this prints).

  lake env lean --run scripts/bump/BundleKeep.lean bundle-keep.json     (in the library, after its build; bundle.py keep-input writes the json)
  { "imports": [modules to load], "names": [passed theorems], "libs": [the library's own modules] }
  prints:  BUNDLE_KEEP [["Module", "const"], ...] BUNDLE_END
           BUNDLE_GRAPH {"nodes": [["Module", "const"], ...], "edges": [[i, [j, ...]], ...], "tainted": [i, ...]} BUNDLE_END
  The graph is of every library constant that is NOT kept: nodes are numbered by their place in `nodes`; an edge `[i, [j, ...]]` says that constant i uses constants j (own, not kept, anything
  kept is already in the bundle); `tainted` are the nodes that stand on `sorryAx`, directly or through another library constant. bundle.py compose follows it from every declaration that
  is kept only because TEXT names it (glue, a `simp` attribute line, a name in a proof): such a declaration has no term in the keep step, so what its term uses was never kept.

The keep set is the closure of the types, values and proofs of the passed theorems AND of every library constant that is not a theorem and stands on nothing
failed (definitions, structures, classes, instances: glue such as `variable [MyClass F]` or a notation names them without any theorem using them, so cutting
one breaks what is left). Theorems stay only where something that stays needs them, and clean simp lemmas (`simp` uses them without the proof term saying so).

This is a program of its own that imports only Lean, and it loads the library at RUN time. It used to be a script compiled in a file that imported the library, so every
token and command the library defines was live while the script was parsed: lean-pool defines `]!` (xs[i]! stopped parsing), and then something else in two more shards
broke the `#bundle_keep` command line itself; either way a whole shard's theorems silently left the bundle. Nothing a library defines can reach this file.
-/
import Lean

open Lean

namespace BundleKeep

/-- The module a constant is in. `moduleNames` is `env.header.moduleNames`, taken once by the caller: reading `env.header` inside a loop is what made a run of this kind
take minutes instead of seconds. -/
def modOf (env : Environment) (moduleNames : Array Name) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => moduleNames[i.toNat]?

/-- Does the constant stand on `sorryAx`, directly or through a library constant? (a failed proof, or anything built on one) -/
partial def tainted (env : Environment) (isOwn : Name → Bool) (memo : IO.Ref (Std.HashMap Name Bool)) (c : Name) : IO Bool := do
  if let some b := (← memo.get)[c]? then return b
  memo.modify (·.insert c false)  -- in progress: a cycle does not taint itself
  let some ci := env.find? c | return false
  let used := ci.getUsedConstantsAsSet
  let mut t := used.contains ``sorryAx
  unless t do
    for u in used.toList do
      if isOwn u && (← tainted env isOwn memo u) then
        t := true
        break
  memo.modify (·.insert c t)
  return t

/-- Every library constant (module, name) that must stay, and the graph of the ones that do not (see the header). -/
def keep (env : Environment) (names libs : Array String) : CoreM (Json × Json) := do
  let hdr := env.header
  let moduleNames := hdr.moduleNames
  let libMods : NameSet := libs.foldl (fun s x => if x == "" then s else s.insert x.toName) {}
  let isOwn (c : Name) : Bool := match modOf env moduleNames c with | some m => libMods.contains m | none => false
  let taint ← IO.mkRef (({} : Std.HashMap Name Bool))
  let mut seeds : List Name := (names.filter (· != "")).toList.map String.toName
  -- `simp` (and `dsimp`) use the simp lemmas of the environment; a `rfl` lemma leaves nothing of itself in the proof term, so the closure of the passed theorems never
  -- sees it, yet the proofs that `simp` closed with it do not close without it
  let simpNames : NameSet := (← Meta.getSimpTheorems).lemmaNames.fold (init := {}) fun s o =>
    match o with
    | .decl n _ _ => s.insert n
    | _ => s
  -- a theorem's own auxiliary definitions (`foo.match_1`, ...) are not seeds: their source range is the theorem's block, and a seed keeps the block: a failed theorem
  -- would come back through its matcher
  let isAuxOfTheorem (c : Name) : Bool := Id.run do
    let mut p := c.getPrefix
    while !p.isAnonymous do
      if (env.find? p).any (·.isTheorem) then return true
      p := p.getPrefix
    return false
  for m in libMods.toList do
    let some idx := env.getModuleIdx? m | continue
    for c in hdr.moduleData[idx.toNat]!.constNames do
      if let some ci := env.find? c then
        if ci.isTheorem then
          if simpNames.contains c && !(← tainted env isOwn taint c) then seeds := c :: seeds
        else if !isAuxOfTheorem c && !(← tainted env isOwn taint c) then seeds := c :: seeds
  let mut seen : NameSet := {}
  let mut stack : List Name := seeds
  let mut consts : Array Json := #[]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        for u in ci.getUsedConstantsAsSet.toList do
          if isOwn u && !seen.contains u then stack := u :: stack
        if let some m := modOf env moduleNames c then
          consts := consts.push (Json.arr #[toJson m.toString, toJson c.toString])
  -- the constants that are not kept, and what each uses among them (the keep set is closed: a kept constant uses only kept ones)
  let mut nodes : Array Json := #[]
  let mut order : Array Name := #[]
  let mut index : Std.HashMap Name Nat := {}
  for m in libMods.toList do
    let some idx := env.getModuleIdx? m | continue
    for c in hdr.moduleData[idx.toNat]!.constNames do
      if seen.contains c then continue
      index := index.insert c order.size
      order := order.push c
      nodes := nodes.push (Json.arr #[toJson m.toString, toJson c.toString])
  let mut edges : Array Json := #[]
  let mut taints : Array Json := #[]
  for i in [0:order.size] do
    let c := order[i]!
    let some ci := env.find? c | continue
    let deps : List Nat := ci.getUsedConstantsAsSet.toList.filterMap fun u => index[u]?
    if !deps.isEmpty then edges := edges.push (Json.arr #[toJson i, toJson deps])
    if (← tainted env isOwn taint c) then taints := taints.push (toJson i)
  return (Json.arr consts, Json.mkObj [("nodes", Json.arr nodes), ("edges", Json.arr edges), ("tainted", Json.arr taints)])

end BundleKeep

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let some path := argv.head? | do
    IO.eprintln "usage: lean --run BundleKeep.lean bundle-keep.json"
    return 2
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let strings (k : String) : IO (Array String) := IO.ofExcept (j.getObjValAs? (Array String) k)
  let imports ← strings "imports"
  let names ← strings "names"
  let libs ← strings "libs"
  initSearchPath (← findSysroot)
  let env ← importModules (imports.map fun m => { module := m.toName }) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<bundle-keep>", fileMap := default, maxHeartbeats := 0 }
  let ((kept, graph), _) ← (BundleKeep.keep env names libs).toIO ctx { env }
  IO.println s!"BUNDLE_KEEP {kept.compress} BUNDLE_END"
  IO.println s!"BUNDLE_GRAPH {graph.compress} BUNDLE_END"
  return 0
