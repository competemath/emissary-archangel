/-
ModuleClashes — the names that two modules of the tree both declare: what `import Tengoku.All` stops at ("import A failed, environment already contains 'N' from B").

  lake env lean --run scripts/bump/ModuleClashes.lean OLEAN_ROOT modules.txt PREFIX      (in the tree, after the build)
  OLEAN_ROOT: where the oleans are (`.lake/build/lib/lean`); PREFIX: only modules under it are read (`Tengoku`)
  modules.txt: the NEW modules, one per line, exact names without guillemets (`Tengoku.Lib.Foo.A-B`); tree_verify.py writes it
  prints, for every pair of modules that declare a common name where at least one of the two is new:
      CLASH <TAB> module <TAB> other module <TAB> how many names <TAB> the first of them
  and last:   clashes: P module pair(s), N name(s)
  The exit status says only that the program ran (0); a log without the `clashes:` line is a run that did not finish.

The factory builds a library in its own environment and the verify job builds each new module in the tree, but no module imports two libraries at once, so a library that vendors a
copy of another (lean-pool's PFR/AddCombi/... against the tree's AddCombi) was first found by the merge queue, one part at a time (lean-pool part 10, 2026-10-12: the notation
`Indicator.«term𝟭_[_]»` is declared by both). Reading the declared names of every module (ModuleData.constNames, no import: an import stops at the first clash) finds every clash at once.
Not every duplicate is an error: `importModules` (Lean.Environment, `subsumesInfo`) lets two modules declare a constant of the same name when the two have the same type and universe
parameters and are both theorems (their proofs need not match), or a theorem and the axiom a theorem becomes. Lean makes such duplicates itself: `f.eq_1` and `f.congr_simp` are generated
where they are first used, so two modules that do not import each other each hold one. This program applies the same rule (the first run of the check, on lean-pool, flagged 155 modules,
most of them over those); every other duplicate (a definition, an instance, a notation, a structure, a theorem with another type) is what stops the import.
-/
import Lean

open Lean

/-- Lean's own rule for a constant that two modules declare (`subsumesInfo` in Lean/Environment.lean, v4.34): the same name, type and universe parameters, and theorem/theorem, or
theorem/axiom. Two axioms are NOT tolerated here: the real rule accepts them only when their type is a proposition (`isPropCheap`, which needs the type of the head constant: the theorems that
the module system realizes as axioms), and the tree's modules are not module-system builds, so a pair of axioms is a pair of `axiom` declarations, which Lean refuses (CodeRabbit, emissary#41). -/
def subsumes (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
    match a, b with
    | .thmInfo x, .thmInfo y => x.all == y.all
    | .thmInfo x, .axiomInfo y => x.all == [y.name] && !y.isUnsafe
    | _, _ => false

partial def oleans (rootLen : Nat) (dir : System.FilePath) (acc : Array (Name × System.FilePath)) : IO (Array (Name × System.FilePath)) := do
  let mut acc := acc
  for e in (← dir.readDir) do
    let p := e.path
    if (← p.isDir) then
      acc ← oleans rootLen p acc
    else if p.extension == some "olean" then
      let some stem := p.fileStem | continue
      -- the module is the path below the root: its directories, then the file's stem (no string slicing: those functions changed between Lean versions)
      let dirs := ((p.parent.getD (System.FilePath.mk ".")).components).drop rootLen
      acc := acc.push ((dirs ++ [stem]).foldl (fun n c => Name.mkStr n c) Name.anonymous, p)
  return acc

def main (argv : List String) : IO UInt32 := do
  let [root, file, pre] := argv | IO.eprintln "usage: ModuleClashes.lean OLEAN_ROOT modules.txt PREFIX"; return 2
  let newMods : NameSet := ((← IO.FS.lines file).toList.map String.trim).filter (· != "") |>.foldl (fun s m => s.insert m.toName) {}
  let prefixName := pre.toName
  let rootPath := System.FilePath.mk root
  let all ← oleans rootPath.components.length rootPath #[]
  let files := all.filter fun (m, _) => prefixName.isPrefixOf m
  let mut owner : Std.HashMap Name (Nat × ConstantInfo) := {}
  -- (earlier module, later module) -> (how many names, the first)
  let mut pairs : Std.HashMap (Nat × Nat) (Nat × Name) := {}
  for i in [0:files.size] do
    let (data, _) ← readModuleData files[i]!.2
    for n in data.constNames, ci in data.constants do
      match owner[n]? with
      | some (j, prev) =>
        if i != j && !(subsumes ci prev || subsumes prev ci) && (newMods.contains files[i]!.1 || newMods.contains files[j]!.1) then
          pairs := pairs.insert (j, i) (match pairs[(j, i)]? with | some (c, f) => (c + 1, f) | none => (1, n))
      | none => owner := owner.insert n (i, ci)
  let mut names := 0
  for ((j, i), (c, f)) in pairs.toList do
    names := names + c
    IO.println s!"CLASH\t{files[i]!.1}\t{files[j]!.1}\t{c}\t{f}"
  IO.println s!"clashes: {pairs.size} module pair(s), {names} name(s)"
  return 0
