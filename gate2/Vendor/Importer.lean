import Lean

open Lean

namespace TengokuImport

/-- Known cross-toolchain renames of equation-compiler-generated per-constructor helpers
(`.below`, and potentially siblings like `.brecOn`), where the underlying constructor itself
was renamed between the source and target toolchain but no `@[deprecated]` alias covers the
auto-generated name tied to the OLD constructor spelling — only the constructor's own
top-level name gets a deprecated alias, not its `.below` sibling. Confirmed via Leak IV probe:
`List.Sublist.below.cons₂` is genuinely absent in v4.34.0-rc2 (Lean core renamed the
`Sublist.cons₂` constructor to `Sublist.cons_cons` on 2026-02-26), while
`List.Sublist.below.cons_cons` exists and type-checks fine — this is a pure rename, not a
structural change, and accounted for 74/189 (39%) of step-3 replay failures in the first
232-theorem run. Applied at name-interning time (`handleName` below) so every downstream
`Expr.const` reference is transparently redirected; the renamed target already exists natively
in the destination environment, so the closure walk in the driver correctly excludes it from
`delta` instead of trying to replay a dead name. -/
def renameTable : Std.HashMap Name Name :=
  Std.HashMap.ofList [
    (`List.Sublist.below.cons₂, `List.Sublist.below.cons_cons)
  ]

def applyRename (n : Name) : Name :=
  renameTable.getD n n

structure ImportState where
  names   : Array Name := #[Name.anonymous]
  levels  : Array Level := #[Level.zero]
  exprs   : Array Expr := #[]
  decls   : Std.HashMap Name ConstantInfo := {}

abbrev ImportM := StateT ImportState (Except String)

def getName (i : Nat) : ImportM Name := do
  let s ← get
  match s.names[i]? with
  | some n => pure n
  | none => throw s!"name index {i} out of range"

def getLevel (i : Nat) : ImportM Level := do
  let s ← get
  match s.levels[i]? with
  | some l => pure l
  | none => throw s!"level index {i} out of range"

def getExpr (i : Nat) : ImportM Expr := do
  let s ← get
  match s.exprs[i]? with
  | some e => pure e
  | none => throw s!"expr index {i} out of range"

def pushName (n : Name) : ImportM Unit :=
  modify fun s => { s with names := s.names.push n }

def pushLevel (l : Level) : ImportM Unit :=
  modify fun s => { s with levels := s.levels.push l }

def pushExpr (e : Expr) : ImportM Unit :=
  modify fun s => { s with exprs := s.exprs.push e }

def addDeclEntry (n : Name) (ci : ConstantInfo) : ImportM Unit :=
  modify fun s => { s with decls := s.decls.insert n ci }

def parseBinderInfo (s : String) : ImportM BinderInfo :=
  match s with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | _ => throw s!"unknown binderInfo {s}"

def parseQuotKind (s : String) : ImportM QuotKind :=
  match s with
  | "type" => pure .type
  | "ctor" => pure .ctor
  | "lift" => pure .lift
  | "ind" => pure .ind
  | _ => throw s!"unknown quotKind {s}"

def objVal (j : Json) (k : String) : ImportM Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw e

def asNat (j : Json) : ImportM Nat :=
  match j.getNat? with
  | .ok v => pure v
  | .error e => throw e

def asStr (j : Json) : ImportM String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throw e

def asBool (j : Json) : ImportM Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throw e

def asArr (j : Json) : ImportM (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throw e

def natField (j : Json) (k : String) : ImportM Nat := do asNat (← objVal j k)
def strField (j : Json) (k : String) : ImportM String := do asStr (← objVal j k)
def boolField (j : Json) (k : String) : ImportM Bool := do asBool (← objVal j k)
def arrField (j : Json) (k : String) : ImportM (Array Json) := do asArr (← objVal j k)

def nameArrField (j : Json) (k : String) : ImportM (Array Name) := do
  let arr ← arrField j k
  arr.mapM fun x => do getName (← asNat x)

def levelArrField (j : Json) (k : String) : ImportM (Array Level) := do
  let arr ← arrField j k
  arr.mapM fun x => do getLevel (← asNat x)

/-- Build a `ConstantVal` from the common `name`/`levelParams`/`type` fields. -/
def constVal (j : Json) : ImportM ConstantVal := do
  let name ← getName (← natField j "name")
  let lp ← nameArrField j "levelParams"
  let typ ← getExpr (← natField j "type")
  pure { name := name, levelParams := lp.toList, type := typ }

def handleName (j : Json) (idx : Nat) : ImportM Unit := do
  if let .ok o := j.getObjVal? "str" then
    let pre ← getName (← natField o "pre")
    let str ← strField o "str"
    pushName (applyRename (Name.str pre str))
  else if let .ok o := j.getObjVal? "num" then
    let pre ← getName (← natField o "pre")
    let i ← natField o "i"
    pushName (Name.num pre i)
  else
    throw s!"unrecognized name entry at {idx}"

def handleLevel (j : Json) (idx : Nat) : ImportM Unit := do
  if let .ok v := j.getObjValAs? Nat "succ" then
    pushLevel (Level.succ (← getLevel v))
  else if let .ok arr := j.getObjValAs? (Array Nat) "max" then
    pushLevel (Level.max (← getLevel arr[0]!) (← getLevel arr[1]!))
  else if let .ok arr := j.getObjValAs? (Array Nat) "imax" then
    pushLevel (Level.imax (← getLevel arr[0]!) (← getLevel arr[1]!))
  else if let .ok v := j.getObjValAs? Nat "param" then
    pushLevel (Level.param (← getName v))
  else
    throw s!"unrecognized level entry at {idx}"

def handleExpr (j : Json) (idx : Nat) : ImportM Unit := do
  if let .ok v := j.getObjValAs? Nat "bvar" then
    pushExpr (Expr.bvar v)
  else if let .ok v := j.getObjValAs? Nat "sort" then
    pushExpr (Expr.sort (← getLevel v))
  else if let .ok o := j.getObjVal? "const" then
    let n ← getName (← natField o "name")
    let usArr ← levelArrField o "us"
    pushExpr (Expr.const n usArr.toList)
  else if let .ok o := j.getObjVal? "app" then
    let fn ← getExpr (← natField o "fn")
    let arg ← getExpr (← natField o "arg")
    pushExpr (Expr.app fn arg)
  else if let .ok o := j.getObjVal? "lam" then
    let n ← getName (← natField o "name")
    let typ ← getExpr (← natField o "type")
    let body ← getExpr (← natField o "body")
    let bi ← parseBinderInfo (← strField o "binderInfo")
    pushExpr (Expr.lam n typ body bi)
  else if let .ok o := j.getObjVal? "forallE" then
    let n ← getName (← natField o "name")
    let typ ← getExpr (← natField o "type")
    let body ← getExpr (← natField o "body")
    let bi ← parseBinderInfo (← strField o "binderInfo")
    pushExpr (Expr.forallE n typ body bi)
  else if let .ok o := j.getObjVal? "letE" then
    let n ← getName (← natField o "name")
    let typ ← getExpr (← natField o "type")
    let val ← getExpr (← natField o "value")
    let body ← getExpr (← natField o "body")
    let nondep ← boolField o "nondep"
    pushExpr (Expr.letE n typ val body nondep)
  else if let .ok o := j.getObjVal? "proj" then
    let tn ← getName (← natField o "typeName")
    let i ← natField o "idx"
    let st ← getExpr (← natField o "struct")
    pushExpr (Expr.proj tn i st)
  else if let .ok v := j.getObjValAs? String "natVal" then
    match v.toNat? with
    | some n => pushExpr (Expr.lit (Literal.natVal n))
    | none => throw s!"bad natVal {v}"
  else if let .ok v := j.getObjValAs? String "strVal" then
    pushExpr (Expr.lit (Literal.strVal v))
  else if let .ok o := j.getObjVal? "mdata" then
    let e ← getExpr (← natField o "expr")
    pushExpr e
  else
    throw s!"unrecognized expr entry at {idx}"

def parseHints (j : Json) : ImportM ReducibilityHints := do
  match j.getStr? with
  | .ok "opaque" => pure .opaque
  | .ok "abbrev" => pure .abbrev
  | .ok _ => throw "unrecognized hints string"
  | .error _ =>
    let r ← natField j "regular"
    pure (.regular r.toUInt32)

def parseSafety (s : String) : ImportM DefinitionSafety :=
  match s with
  | "unsafe" => pure .unsafe
  | "safe" => pure .safe
  | "partial" => pure .partial
  | _ => throw s!"unknown safety {s}"

def handleInductiveVal (j : Json) : ImportM InductiveVal := do
  let cv ← constVal j
  let numParams ← natField j "numParams"
  let numIndices ← natField j "numIndices"
  let all ← nameArrField j "all"
  let ctors ← nameArrField j "ctors"
  let numNested ← natField j "numNested"
  let isRec ← boolField j "isRec"
  let isUnsafe ← boolField j "isUnsafe"
  let isReflexive ← boolField j "isReflexive"
  pure { toConstantVal := cv, numParams := numParams, numIndices := numIndices, all := all.toList, ctors := ctors.toList, numNested := numNested, isRec := isRec, isUnsafe := isUnsafe, isReflexive := isReflexive }

def handleConstructorVal (j : Json) : ImportM ConstructorVal := do
  let cv ← constVal j
  let induct ← getName (← natField j "induct")
  let cidx ← natField j "cidx"
  let numParams ← natField j "numParams"
  let numFields ← natField j "numFields"
  let isUnsafe ← boolField j "isUnsafe"
  pure { toConstantVal := cv, induct := induct, cidx := cidx, numParams := numParams, numFields := numFields, isUnsafe := isUnsafe }

def handleRecursorRule (j : Json) : ImportM RecursorRule := do
  let ctor ← getName (← natField j "ctor")
  let nfields ← natField j "nfields"
  let rhs ← getExpr (← natField j "rhs")
  pure { ctor, nfields, rhs }

def handleRecursorVal (j : Json) : ImportM RecursorVal := do
  let cv ← constVal j
  let all ← nameArrField j "all"
  let numParams ← natField j "numParams"
  let numIndices ← natField j "numIndices"
  let numMotives ← natField j "numMotives"
  let numMinors ← natField j "numMinors"
  let rulesArr ← arrField j "rules"
  let rules ← rulesArr.mapM handleRecursorRule
  let k ← boolField j "k"
  let isUnsafe ← boolField j "isUnsafe"
  pure { toConstantVal := cv, all := all.toList, numParams := numParams, numIndices := numIndices, numMotives := numMotives, numMinors := numMinors, rules := rules.toList, k := k, isUnsafe := isUnsafe }

def handleDecl (j : Json) : ImportM Unit := do
  if let .ok o := j.getObjVal? "axiom" then
    let cv ← constVal o
    let isUnsafe ← boolField o "isUnsafe"
    addDeclEntry cv.name (.axiomInfo { toConstantVal := cv, isUnsafe := isUnsafe })
  else if let .ok o := j.getObjVal? "def" then
    let cv ← constVal o
    let value ← getExpr (← natField o "value")
    let hints ← parseHints (← objVal o "hints")
    let safety ← parseSafety (← strField o "safety")
    let all ← nameArrField o "all"
    addDeclEntry cv.name (.defnInfo { toConstantVal := cv, value := value, hints := hints, safety := safety, all := all.toList })
  else if let .ok o := j.getObjVal? "opaque" then
    let cv ← constVal o
    let value ← getExpr (← natField o "value")
    let isUnsafe ← boolField o "isUnsafe"
    let all ← nameArrField o "all"
    addDeclEntry cv.name (.opaqueInfo { toConstantVal := cv, value := value, isUnsafe := isUnsafe, all := all.toList })
  else if let .ok o := j.getObjVal? "thm" then
    let cv ← constVal o
    let value ← getExpr (← natField o "value")
    let all ← nameArrField o "all"
    addDeclEntry cv.name (.thmInfo { toConstantVal := cv, value := value, all := all.toList })
  else if let .ok o := j.getObjVal? "quot" then
    let cv ← constVal o
    let kind ← parseQuotKind (← strField o "kind")
    addDeclEntry cv.name (.quotInfo { toConstantVal := cv, kind := kind })
  else if let .ok o := j.getObjVal? "inductive" then
    let typesArr ← arrField o "types"
    let ctorsArr ← arrField o "ctors"
    let recsArr ← arrField o "recs"
    for t in typesArr do
      let iv ← handleInductiveVal t
      addDeclEntry iv.name (.inductInfo iv)
    for c in ctorsArr do
      let cv ← handleConstructorVal c
      addDeclEntry cv.name (.ctorInfo cv)
    for r in recsArr do
      let rv ← handleRecursorVal r
      addDeclEntry rv.name (.recInfo rv)
  else
    throw "unrecognized declaration entry"

def handleLine (line : String) : ImportM Unit := do
  if line.trim.isEmpty then pure () else
  match Json.parse line with
  | .error e => throw s!"json parse error: {e}"
  | .ok j =>
    if let .ok _ := j.getObjVal? "meta" then
      pure ()
    else if let .ok idx := j.getObjValAs? Nat "in" then
      handleName j idx
    else if let .ok idx := j.getObjValAs? Nat "il" then
      handleLevel j idx
    else if let .ok idx := j.getObjValAs? Nat "ie" then
      handleExpr j idx
    else
      handleDecl j

def runImport (contents : String) : Except String (Std.HashMap Name ConstantInfo) := do
  let lines := contents.splitOn "\n"
  let go : ImportM Unit := do
    for line in lines do
      handleLine line
  let (_, s) ← go.run {}
  pure s.decls

end TengokuImport
