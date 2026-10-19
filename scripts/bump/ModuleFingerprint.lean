/-
ModuleFingerprint — a deep fingerprint of every declaration of some modules, to say whether a declaration in one environment is the same declaration as one in another.

  lake env lean --run scripts/bump/ModuleFingerprint.lean modules.txt [whole.txt]        (in the tree, after the build; scripts/bump/tree_dups.py writes both)
  modules.txt: one module per line, exact names, without guillemets (`Tengoku.Lib.Foo.A-B`): the declarations of exactly these modules are fingerprinted
  whole.txt (optional, same format): modules of the tree's seed that are compared whole, like the library's own, wherever they are reached from. Every comparison that is to agree with another
             must be given the same list (a seed module is otherwise a leaf: counted by name and type, see below).
  prints, for every declaration of these modules that is not internal (no `_private`, no `_aux…`, no macro scopes):
      FP <TAB> module <TAB> declaration <TAB> kind <TAB> 32 hex digits
  and last:   fingerprints: N declarations
  The exit status says only that the program ran (0): a log that has no `fingerprints:` line is a run that did not finish.

What the fingerprint is. For a declaration it covers: its kind, its universe parameters, its TYPE, and, for everything but a theorem, its VALUE (a definition, an instance, an abbrev, an
opaque constant); for an inductive type, the types of its constructors (a mutual family is one unit); and, recursively, the same for every constant its type or value mentions, except the
constants of Lean core, Std and the tree's seed (`Tengoku.Seed`, `Tengoku`), unless the module is listed in either file: those are the same objects in every comparison made inside one tree, so they
count by name and type only.
Names count as written, except that a private name loses the module it is mangled with. The hash is 128 bits: two independent 64-bit chains.

What equal fingerprints let you say (two declarations, in the same tree, or in two environments that share the seed): they have the same statement, and every definition below that statement,
down to the seed, is the same term; up to a 128-bit collision, which nobody controls here (the proofs are still checked by Lean's kernel; this program never decides truth).

What they do NOT say: that the PROOFS are the same (a theorem's proof is not read: a statement does not depend on it), or that the same attributes, instances, simp lemmas or notation are registered
(those are not part of a declaration: a statement that elaborates differently because of them has another type, and so another fingerprint, but a registration nothing here elaborates against is not seen).

What different fingerprints say: nothing about which one is right. They say the two declarations are not provably the same, and the caller must not treat them as the same.
-/
import Lean

open Lean

/-- a 128-bit fingerprint: two independent 64-bit mixing chains -/
abbrev H := UInt64 × UInt64

def mix1 (h x : UInt64) : UInt64 :=
  let h := (h ^^^ x) * 0x100000001b3
  h ^^^ (h >>> 29)

def mix2 (h x : UInt64) : UInt64 :=
  let h := h + x + 0x9e3779b97f4a7c15
  let h := (h ^^^ (h >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

def tag (t : Nat) : H := (mix1 0xcbf29ce484222325 t.toUInt64, mix2 0x84222325cbf29ce4 t.toUInt64)

def comb (a b : H) : H := (mix1 a.1 b.1, mix2 a.2 b.2)

def strH (s : String) : H := s.foldl (fun h c => comb h (tag c.toNat)) (tag 0)

def hlt (a b : H) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

partial def levelH : Level → H
  | .zero => tag 20
  | .succ l => comb (tag 21) (levelH l)
  | .max a b => comb (comb (tag 22) (levelH a)) (levelH b)
  | .imax a b => comb (comb (tag 23) (levelH a)) (levelH b)
  | .param n => comb (tag 24) (strH n.toString)
  | .mvar _ => tag 25

/-- a private name without the module it is mangled with: the same private helper in two modules is the same name -/
def canon (n : Name) : Name :=
  match privateToUserName? n with
  | some u => u
  | none => n

def binderCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

structure Ctx where
  env : Environment
  whole : NameSet
  exprMemo : IO.Ref (Std.HashMap USize H)
  nameMemo : IO.Ref (Std.HashMap Name H)
  constMemo : IO.Ref (Std.HashMap Name H)

def nameH (c : Ctx) (n : Name) : IO H := do
  if let some h := (← c.nameMemo.get)[n]? then return h
  let h := strH (canon n).toString
  c.nameMemo.modify (·.insert n h)
  return h

/-- a constant of Lean core, Std or the tree's seed: the same object in every comparison made inside one tree -/
def leafModule (m : Name) : Bool :=
  (match m.getRoot with
    | .str _ s => s == "Init" || s == "Std" || s == "Lean" || s == "Lake"
    | _ => false) || m == `Tengoku || (`Tengoku.Seed).isPrefixOf m

def isLeaf (c : Ctx) (n : Name) : Bool :=
  match c.env.getModuleIdxFor? n with
  | some idx =>
    match c.env.header.moduleNames[idx.toNat]? with
    | some m => leafModule m && !c.whole.contains m
    | none => true
  | none => true

/-- the structural hash of a term: binder names and the proofs inside it do not matter, binder annotations and every constant name do. Shared subterms are hashed once (by address). -/
unsafe def exprH (c : Ctx) (e : Expr) : IO H := do
  let key := ptrAddrUnsafe e
  if let some h := (← c.exprMemo.get)[key]? then return h
  let h ← match e with
    | .bvar i => pure (comb (tag 1) (tag i))
    | .fvar _ => pure (tag 2)
    | .mvar _ => pure (tag 3)
    | .sort l => pure (comb (tag 4) (levelH l))
    | .const n ls => do
      let mut h := comb (tag 5) (← nameH c n)
      for l in ls do h := comb h (levelH l)
      pure h
    | .app f a => do pure (comb (comb (tag 6) (← exprH c f)) (← exprH c a))
    | .lam _ t b bi => do pure (comb (comb (comb (tag 7) (tag (binderCode bi))) (← exprH c t)) (← exprH c b))
    | .forallE _ t b bi => do pure (comb (comb (comb (tag 8) (tag (binderCode bi))) (← exprH c t)) (← exprH c b))
    | .letE _ t v b nd => do pure (comb (comb (comb (comb (tag 9) (tag (if nd then 1 else 0))) (← exprH c t)) (← exprH c v)) (← exprH c b))
    | .lit (.natVal n) => pure (comb (tag 10) (strH (toString n)))
    | .lit (.strVal s) => pure (comb (tag 11) (strH s))
    | .mdata _ e => exprH c e
    | .proj s i e => do pure (comb (comb (comb (tag 12) (← nameH c s)) (tag i)) (← exprH c e))
  c.exprMemo.modify (·.insert key h)
  return h

def kindTag : ConstantInfo → Nat
  | .axiomInfo _ => 30
  | .defnInfo _ => 31
  | .thmInfo _ => 32
  | .opaqueInfo _ => 33
  | .quotInfo _ => 34
  | .inductInfo _ => 35
  | .ctorInfo _ => 36
  | .recInfo _ => 37

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- the members of a (mutual) inductive family and their constructors: they are one unit, so that the hash of a family does not depend on which member it is entered from -/
def familyOf (env : Environment) (v : InductiveVal) : List ConstantInfo :=
  v.all.foldl (fun acc n =>
    match env.find? n with
    | some (.inductInfo iv) => acc ++ [ConstantInfo.inductInfo iv] ++ (iv.ctors.filterMap fun k => env.find? k)
    | _ => acc) []

/-- what a declaration is, apart from the constants it mentions: kind, universe parameters, type, and value unless it is a theorem. A leaf counts by name and type only. -/
unsafe def shallow (c : Ctx) (ci : ConstantInfo) (full : Bool) : IO H := do
  let cv := ci.toConstantVal
  let mut h := tag (kindTag ci)
  h := comb h (← nameH c cv.name)
  h := comb h (strH (toString cv.levelParams))
  h := comb h (← exprH c cv.type)
  if !full then return h
  match ci with
  | .defnInfo v =>
    h := comb h (← exprH c v.value)
    h := comb h (tag (match v.hints with | .opaque => 0 | .abbrev => 1 | .regular _ => 2))
    h := comb h (tag (match v.safety with | .unsafe => 0 | .safe => 1 | .partial => 2))
  | .opaqueInfo v =>
    h := comb h (← exprH c v.value)
    h := comb h (tag (if v.isUnsafe then 1 else 0))
  | .axiomInfo v => h := comb h (tag (if v.isUnsafe then 1 else 0))
  | .inductInfo v =>
    -- the whole family: each member's type, and each constructor's name and type
    let mut parts : Array H := #[]
    for m in familyOf c.env v do
      let mv := m.toConstantVal
      parts := parts.push (comb (comb (tag (kindTag m)) (← nameH c mv.name)) (← exprH c mv.type))
    parts := parts.qsort hlt
    for p in parts do h := comb h p
    h := comb h (tag v.numParams)
    h := comb h (tag v.numIndices)
    h := comb h (tag (if v.isRec then 1 else 0))
  | .ctorInfo v =>
    h := comb h (← nameH c v.induct)
    h := comb h (tag v.cidx)
    h := comb h (tag v.numParams)
    h := comb h (tag v.numFields)
  | .recInfo v =>
    h := comb h (tag v.numParams)
    h := comb h (tag v.numIndices)
    h := comb h (tag v.numMotives)
    h := comb h (tag v.numMinors)
    for r in v.rules do
      h := comb h (comb (← nameH c r.ctor) (comb (tag r.nfields) (← exprH c r.rhs)))
  | _ => pure ()
  return h

/-- the constants a declaration stands on, other than itself (and, for an inductive family, other than its members and constructors) -/
def depsOf (env : Environment) (ci : ConstantInfo) : Array Name :=
  let own : NameSet := match ci with
    | .inductInfo v => (familyOf env v).foldl (fun s m => s.insert m.name) {}
    | _ => ({} : NameSet).insert ci.name
  let used : Array Name := match ci with
    | .defnInfo v => ci.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => ci.type.getUsedConstants ++ v.value.getUsedConstants
    | .inductInfo v => (familyOf env v).foldl (fun acc m => acc ++ m.type.getUsedConstants) #[]
    | .ctorInfo v => ci.type.getUsedConstants ++ #[v.induct]
    | .recInfo v => v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants ++ #[r.ctor]) ci.type.getUsedConstants
    | _ => ci.type.getUsedConstants
  let seen : NameSet := used.foldl (fun s n => s.insert n) {}
  (seen.toList.filter fun n => !own.contains n).toArray

/-- the deep fingerprint of a constant: its own (`shallow`) and those of every constant it stands on, below the leaves -/
unsafe def deep (c : Ctx) (n : Name) : IO H := do
  if let some h := (← c.constMemo.get)[n]? then return h
  let some ci := c.env.find? n | return comb (tag 99) (← nameH c n)
  c.constMemo.modify (·.insert n (tag 98)) -- an edge back into what is being computed (there is none in a Lean environment, but a hash must not loop)
  let leaf := isLeaf c n
  let mut h ← shallow c ci (!leaf)
  if !leaf then
    let mut parts : Array H := #[]
    for d in depsOf c.env ci do
      parts := parts.push (comb (← nameH c d) (← deep c d))
    parts := parts.qsort hlt
    for p in parts do h := comb h p
  c.constMemo.modify (·.insert n h)
  return h

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

unsafe def run (names whole : List Name) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (names.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let wholeSet : NameSet := (names ++ whole).foldl (fun s m => s.insert m) {}
  let c : Ctx := { env, whole := wholeSet, exprMemo := ← IO.mkRef {}, nameMemo := ← IO.mkRef {}, constMemo := ← IO.mkRef {} }
  let mut count := 0
  for m in names do
    let some idx := env.getModuleIdx? m | IO.eprintln s!"not imported: {m}"; return 3
    for n in env.header.moduleData[idx.toNat]!.constNames do
      if n.isInternal || n.hasMacroScopes then continue
      let some ci := env.find? n | continue
      let h ← deep c n
      IO.println s!"FP\t{m}\t{canon n}\t{kindName ci}\t{hex16 h.1}{hex16 h.2}"
      count := count + 1
  IO.println s!"fingerprints: {count} declarations"
  return 0

def readModules (file : String) : IO (List Name) := do
  return ((← IO.FS.lines file).toList.map fun l => l.trimAscii.toString).filter (· != "") |>.map String.toName

unsafe def main (argv : List String) : IO UInt32 := do
  match argv with
  | [file] => run (← readModules file) []
  | [file, whole] => run (← readModules file) (← readModules whole)
  | _ => IO.eprintln "usage: ModuleFingerprint.lean <modules.txt> [<whole.txt>]"; return 2
