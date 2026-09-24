module

public meta import Foundation.Meta.Lit
public meta import Foundation.Meta.TwoSided
public import Foundation.Meta.Lit
public import Foundation.Meta.TwoSided


-- @@ L8-12 verbatim
/-!
# Proof automation based on the proof search on (modified) $\mathbf{LJpm}^*$

main reference: Grigori Mints, A Short Introduction to Intuitionistic Logic [Min00]
-/


-- @@ L14-14 verbatim
public meta section


-- @@ L16-16 verbatim
namespace FFL.Meta


-- @@ L18-18 verbatim
open Mathlib Qq Lean Elab Meta Tactic


-- @@ L20-20 verbatim
namespace IntProver


-- @@ L22-22 verbatim
namespace Theorems


-- @@ L24-24 verbatim
open Entailment TwoSided Tableaux FiniteContext


-- @@ L26-26 verbatim
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] {S : Type*} [Entailment S F] {𝓢 : S} [Entailment.Int 𝓢]


-- @@ L28-28 verbatim
local notation Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ


-- @@ L30-30 verbatim
scoped notation:0 Γ:45 " ⟶ " Δ:46 => Tableaux.Sequent.mk Γ Δ


-- @@ L32-41 verbatim
set_option linter.unusedSectionVars false in
lemma to_twoSided {Γ Δ} (h : Valid 𝓢 [Γ ⟶ Δ]) : Γ ⟹ Δ := by
  rcases h
  · assumption
  · simp_all

-- `DecidableEq F` is not referenced in the proof term itself, but the ambient
-- instance is needed for elaboration to disambiguate `TwoSided.to_provable`'s
-- own `DecidableEq F`-dependent notation; omitting it (as the `unusedSectionVars`
-- linter suggests) breaks elaboration, so the false-positive warning is suppressed.

-- @@ L42-53 verbatim
set_option linter.unusedSectionVars false in
lemma to_provable {φ} (h : Valid 𝓢 [[] ⟶ [φ]]) : 𝓢 ⊢ φ := by
  rcases h
  · exact TwoSided.to_provable <| by assumption
  · simp_all

lemma add_hyp {𝒯 : S} (s : 𝒯 ⪯ 𝓢) {Γ Δ φ} (hφ : 𝒯 ⊢ φ)  : Valid 𝓢 [φ :: Γ ⟶ Δ] → Valid 𝓢 [Γ ⟶ Δ] :=
  Valid.of_single_uppercedent <| TwoSided.add_hyp hφ

lemma right_closed {T Γ Δ φ} (h : φ ∈ Γ) : Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := Valid.right_closed h

lemma left_closed {T Γ Δ φ} (h : φ ∈ Δ) : Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := Valid.left_closed h


-- @@ L55-56 verbatim
set_option linter.unusedSectionVars false in
lemma remove {T Γ Δ} : Valid 𝓢 T → Valid 𝓢 ((Γ ⟶ Δ) :: T) := Valid.of_subset


-- @@ L58-100 verbatim
set_option linter.unusedSectionVars false in
lemma rotate {T Γ Δ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ Δ) :: T) := Valid.of_subset


lemma remove_right {T Γ Δ φ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := fun h ↦
  Valid.remove_right (rotate h)

lemma rotate_right {T Γ Δ φ} : Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ]]) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := fun h ↦
  Valid.rotate_right (rotate h)

lemma verum_right {T Γ Δ} : Valid 𝓢 ((Γ ⟶ ⊤ :: Δ) :: T) := Valid.verum_right

lemma falsum_right {T Γ Δ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ ⊥ :: Δ) :: T) := fun h ↦
  Valid.falsum_right (rotate h)

lemma and_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ]]) → Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [ψ]]) → Valid 𝓢 ((Γ ⟶ φ ⋏ ψ :: Δ) :: T) := fun h₁ h₂ ↦
  Valid.and_right (rotate h₁) (rotate h₂)

lemma or_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ, ψ]]) → Valid 𝓢 ((Γ ⟶ φ ⋎ ψ :: Δ) :: T) := fun h ↦
  Valid.or_right (rotate h)

lemma neg_right {T Γ Δ φ} :
    Valid 𝓢 (T ++ [Γ ++ [φ] ⟶ []] ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := fun h ↦
  Valid.neg_right' <| rotate <| rotate h

lemma imply_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ++ [φ] ⟶ [ψ]] ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ (φ 🡒 ψ) :: Δ) :: T) := fun h ↦
  Valid.imply_right' <| rotate <| rotate h

lemma iff_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ 🡒 ψ]]) → Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [ψ 🡒 φ]]) → Valid 𝓢 ((Γ ⟶ (φ 🡘 ψ) :: Δ) :: T) := fun h₁ h₂ ↦
  Valid.and_right (rotate h₁) (rotate h₂)


lemma remove_left {T Γ Δ φ} : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  Valid.remove_left

lemma rotate_left {T Γ Δ φ} : Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  Valid.rotate_left

lemma verum_left {T Γ Δ} : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((⊤ :: Γ ⟶ Δ) :: T) := Valid.verum_left


-- @@ L102-123 verbatim
set_option linter.unusedSectionVars false in
lemma falsum_left {T Γ Δ} : Valid 𝓢 ((⊥ :: Γ ⟶ Δ) :: T) := Valid.falsum_left

lemma or_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋎ ψ :: Γ ⟶ Δ) :: T) :=
  Valid.or_left

lemma and_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ, ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋏ ψ :: Γ ⟶ Δ) :: T) :=
  Valid.and_left

lemma neg_left {T Γ Δ φ} :
    Valid 𝓢 ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((∼φ :: Γ ⟶ Δ) :: T) :=
  Valid.neg_left

lemma imply_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ 🡒 ψ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 (((φ 🡒 ψ) :: Γ ⟶ Δ) :: T) :=
  Valid.imply_left

lemma iff_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ 🡒 ψ, ψ 🡒 φ] ⟶ Δ) :: T) → Valid 𝓢 (((φ 🡘 ψ) :: Γ ⟶ Δ) :: T) :=
  Valid.and_left


-- @@ L125-125 verbatim
end Theorems


-- @@ L127-127 verbatim
initialize registerTraceClass `int_prover

-- @@ L128-128 verbatim
initialize registerTraceClass `int_prover.detail


-- @@ L130-141 verbatim
structure Context where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  instLC : Q(LogicalConnective $F)
  instLN : Q(LogicalNeutral $F)
  instDE : Q(DecidableEq $F)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $S $F)
  𝓢 : Q($S)
  instInt : Q(Entailment.Int $𝓢)


-- @@ L143-143 verbatim
open Mathlib Qq Lean Elab Meta Tactic


-- @@ L145-146 verbatim
/-- The monad for `int_prover` contains. -/
abbrev M := ReaderT Context AtomM


-- @@ L148-153 verbatim
/-- Apply the function
  `n : ∀ {F} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] {S} [Entailment S F] {𝓢} [Entailment.Int 𝓢], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) : Array Expr → Expr :=
  mkAppN <| @Expr.const n [c.levelF, c.levelS, c.levelE]
    |>.app c.F |>.app c.instLC |>.app c.instLN |>.app c.instDE |>.app c.S |>.app c.E |>.app c.𝓢 |>.app c.instInt


-- @@ L155-157 verbatim
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n xs


-- @@ L159-167 verbatim
def getGoalTwoSided (e : Q(Prop)) : MetaM ((c : Context) × List Q($c.F) × List Q($c.F)) := do
  let ~q(@Entailment.TwoSided $F $instLC $instLN $S $E $𝓢 $p $q) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some instDE ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some instInt ← trySynthInstanceQ q(Entailment.Int $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  let Γ ← Qq.ofQList p
  let Δ ← Qq.ofQList q
  return ⟨⟨_, _, _, F, instLC, instLN, instDE, S, E, 𝓢, instInt⟩, Γ, Δ⟩


-- @@ L169-179 verbatim
def getGoalProvable (e : Q(Prop)) : MetaM ((c : Context) × Q($c.F)) := do
  let ~q(@Entailment.Provable $F $S $E $𝓢 $p) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some instDE ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some instLC ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some instLN ← trySynthInstanceQ q(LogicalNeutral $F)
    | throwError m! "error: failed to find instance LogicalNeutral {F}"
  let .some instInt ← trySynthInstanceQ q(Entailment.Int $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  return ⟨⟨_, _, _, F, instLC, instLN, instDE, S, E, 𝓢, instInt⟩, p⟩


-- @@ L181-181 verbatim
abbrev Sequent := List Lit


-- @@ L183-183 verbatim
abbrev Tableaux := Entailment.Tableaux Lit


-- @@ L185-185 verbatim
scoped notation:0 Γ:45 " ⟶ " Δ:46 => Entailment.Tableaux.Sequent.mk Γ Δ


-- @@ L187-189 verbatim
def litToExpr (φ : Lit) : M Expr := do
  let c ← read
  return Litform.toExpr c.instLC c.instLN φ


-- @@ L191-193 verbatim
def exprToLit (e : Expr) : M Lit := do
  let c ← read
  Litform.denote c.instLC c.instLN e


-- @@ L195-197 verbatim
def Sequent.toExprList (Γ : Sequent) : M (List Expr) := do
  let c ← read
  return Γ.map (Litform.toExpr c.instLC c.instLN)


-- @@ L199-201 verbatim
def exprListToLitList (l : List Expr) : M (List Lit) := do
  let c ← read
  l.mapM (m := MetaM) (Litform.denote c.instLC c.instLN)


-- @@ L203-205 verbatim
def Sequent.toExpr (Γ : Sequent) : M Expr := do
  let c ← read
  return toQList <| Γ.map (Litform.toExpr c.instLC c.instLN)


-- @@ L207-208 verbatim
def mkTableauSequentQ (F : Q(Type*)) (Γ Δ : Q(List $F)) : Q(Entailment.Tableaux.Sequent $F) :=
  q($Γ ⟶ $Δ)


-- @@ L210-217 verbatim
def Tableaux.toExpr (T : Tableaux) : M Expr := do
  let c ← read
  let m ← T.mapM fun ⟨Γ, Δ⟩ ↦ do
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let e := mkTableauSequentQ c.F Γ Δ
    return e
  return toQList (u := c.levelF) m


-- @@ L219-223 verbatim
def remove (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.remove #[T, Γ, Δ, e]


-- @@ L225-233 verbatim
def tryRightClose (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Γ.toExprList) with
  |   .none => return none
  | .some e => do
    let T ← T.toExpr
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let φ ← litToExpr φ
    return some <| ← iapp ``FFL.Meta.IntProver.Theorems.right_closed #[T, Γ, Δ, φ, e]


-- @@ L235-243 verbatim
def tryLeftClose (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Δ.toExprList) with
  |   .none => return none
  | .some e => do
    let T ← T.toExpr
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let φ ← litToExpr φ
    return some <| ← iapp ``FFL.Meta.IntProver.Theorems.left_closed #[T, Γ, Δ, φ, e]


-- @@ L245-250 verbatim
def removeRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.remove_right #[T, Γ, Δ, φ, e]


-- @@ L252-257 verbatim
def removeLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.remove_left #[T, Γ, Δ, φ, e]


-- @@ L259-264 verbatim
def rotateRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.rotate_right #[T, Γ, Δ, φ, e]


-- @@ L266-271 verbatim
def rotateLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.rotate_left #[T, Γ, Δ, φ, e]


-- @@ L273-277 verbatim
def verumRight (T : Tableaux) (Γ Δ : Sequent) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.verum_right #[T, Γ, Δ]


-- @@ L279-283 verbatim
def falsumRight (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.falsum_right #[T, Γ, Δ, e]


-- @@ L285-291 verbatim
def andRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.and_right #[T, Γ, Δ, φ, ψ, e₁, e₂]


-- @@ L293-299 verbatim
def orRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.or_right #[T, Γ, Δ, φ, ψ, e]


-- @@ L301-306 verbatim
def negRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.neg_right #[T, Γ, Δ, φ, e]


-- @@ L308-314 verbatim
def implyRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.imply_right #[T, Γ, Δ, φ, ψ, e]


-- @@ L316-322 verbatim
def iffRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.iff_right #[T, Γ, Δ, φ, ψ, e₁, e₂]


-- @@ L324-328 verbatim
def rotate (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.rotate #[T, Γ, Δ, e]


-- @@ L330-334 verbatim
def verumLeft (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.verum_left #[T, Γ, Δ, e]


-- @@ L336-340 verbatim
def falsumLeft (T : Tableaux) (Γ Δ : Sequent) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.IntProver.Theorems.falsum_left #[T, Γ, Δ]


-- @@ L342-348 verbatim
def andLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.and_left #[T, Γ, Δ, φ, ψ, e]


-- @@ L350-356 verbatim
def orLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.or_left #[T, Γ, Δ, φ, ψ, e₁, e₂]


-- @@ L358-363 verbatim
def negLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.neg_left #[T, Γ, Δ, φ, e]


-- @@ L365-371 verbatim
def implyLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.imply_left #[T, Γ, Δ, φ, ψ, e₁, e₂]


-- @@ L373-379 verbatim
def iffLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``FFL.Meta.IntProver.Theorems.iff_left #[T, Γ, Δ, φ, ψ, e]


-- @@ L381-385 verbatim
def isWeakerSequent (Γ Δ : Sequent) (T : Tableaux) : M Bool := do
  match T with
  |           [] => return false
  | (Ξ ⟶ Λ) :: T =>
    return ((←Lit.dSubsetList Γ Ξ) && (←Lit.dSubsetList Δ Λ)) || (←isWeakerSequent Γ Δ T)


-- @@ L387-483 verbatim
def prover (k : ℕ) (b : Bool) (T : Tableaux) : M Expr := do
  -- logInfo m!"step: {k}, case: {b}, {← T.toExpr}"
  match k, b with
  |     0,      _ => throwError m!"Proof search failed: {← T.toExpr}"
  | k + 1, false =>
    match T with
    |           [] => throwError m!"Proof search failed: empty tableaux reached."
    | (Γ ⟶ Δ) :: T =>
      if ←isWeakerSequent Γ Δ T then
        let e ← prover k false T
        remove T Γ Δ e
      else
      match Γ with
      |     [] => prover k true (([] ⟶ Δ) :: T)
      | φ :: Γ => do
        match ← tryLeftClose T Γ Δ φ with
        | some h => return h
        |   none => do
          if ← φ.dMem Γ then
            let e ← prover k true ((Γ ⟶ Δ) :: T)
            removeLeft T Γ Δ φ e
          else
          match φ with
          | .atom a => do
            let e ← prover k true ((Γ ++ [.atom a] ⟶ Δ) :: T)
            rotateLeft T Γ Δ (.atom a) e
          | ⊤ => do
            let e ← prover k true ((Γ ⟶ Δ) :: T)
            verumLeft T Γ Δ e
          | ⊥ => do
            falsumLeft T Γ Δ
          | φ ⋏ ψ => do
            let e ← prover k true ((Γ ++ [φ, ψ] ⟶ Δ) :: T)
            andLeft T Γ Δ φ ψ e
          | φ ⋎ ψ => do
            let e₁ ← prover k true ((Γ ++ [φ] ⟶ Δ) :: T)
            let e₂ ← prover k true ((Γ ++ [ψ] ⟶ Δ) :: T)
            orLeft T Γ Δ φ ψ e₁ e₂
          | ∼φ => do
            let e ← prover k true ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T)
            negLeft T Γ Δ φ e
          | φ 🡒 ψ => do
            let e₁ ← prover k true ((Γ ++ [φ 🡒 ψ] ⟶ Δ ++ [φ]) :: T)
            let e₂ ← prover k true ((Γ ++ [ψ] ⟶ Δ) :: T)
            implyLeft T Γ Δ φ ψ e₁ e₂
          | .iff φ ψ => do
            let e ← prover k true ((Γ ++ [φ 🡒 ψ, ψ 🡒 φ] ⟶ Δ) :: T)
            iffLeft T Γ Δ φ ψ e
  | k + 1,  true =>
    match T with
    |                [] => throwError m!"Proof search failed: empty tableaux reached."
    |     (Γ ⟶ Δ) :: T => do
      if ←isWeakerSequent Γ Δ T then
        let e ← prover k false T
        remove T Γ Δ e
      else
      match Δ with
      | [] =>
        let e ← prover k false (T ++ [Γ ⟶ []])
        rotate T Γ [] e
      | φ :: Δ => do
        match ← tryRightClose T Γ Δ φ with
        | some h => return h
        |   none => do
          if ← φ.dMem Δ then
            let e ← prover k false (T ++ [Γ ⟶ Δ])
            removeRight T Γ Δ φ e
          else
          match φ with
          | .atom a => do
            let e ← tryRightClose T Γ Δ (.atom a)
            match e with
            | some h => return h
            |   none => do
              let e ← prover k false (T ++ [Γ ⟶ Δ ++ [.atom a]])
              rotateRight T Γ Δ (.atom a) e
          | ⊤ => verumRight T Γ Δ
          | ⊥ => do
            let e ← prover k false (T ++ [Γ ⟶ Δ])
            falsumRight T Γ Δ e
          | φ ⋏ ψ => do
            let e₁ ← prover k false (T ++ [Γ ⟶ Δ ++ [φ]])
            let e₂ ← prover k false (T ++ [Γ ⟶ Δ ++ [ψ]])
            andRight T Γ Δ φ ψ e₁ e₂
          | φ ⋎ ψ => do
            let e ← prover k false (T ++ [Γ ⟶ Δ ++ [φ, ψ]])
            orRight T Γ Δ φ ψ e
          | ∼φ => do
            let e ← prover k false (T ++ [Γ ++ [φ] ⟶ []] ++ [Γ ⟶ Δ])
            negRight T Γ Δ φ e
          | φ 🡒 ψ => do
            let e ← prover k false (T ++ [Γ ++ [φ] ⟶ [ψ]] ++ [Γ ⟶ Δ])
            implyRight T Γ Δ φ ψ e
          | .iff φ ψ => do
            let e₁ ← prover k false (T ++ [Γ ⟶ Δ ++ [φ 🡒 ψ]])
            let e₂ ← prover k false (T ++ [Γ ⟶ Δ ++ [ψ 🡒 φ]])
            iffRight T Γ Δ φ ψ e₁ e₂


-- @@ L485-494 verbatim
structure HypInfo where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $S $F)
  𝓢 : Q($S)
  φ : Q($F)
  proof : Q($𝓢 ⊢ $φ)


-- @@ L496-499 verbatim
def synthProvable (e : Expr) : MetaM HypInfo := do
  let (ty : Q(Prop)) ← inferType e
  let ~q(@Entailment.Provable $F $S $E $𝓢 $φ) := ty | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  return ⟨_, _, _, F, S, E, 𝓢, φ, e⟩


-- @@ L501-505 verbatim
structure CompatibleHypInfo where
  𝓢 : Expr
  WT : Expr
  φ : Lit
  proof : Expr


-- @@ L507-515 verbatim
def HypInfo.toCompatible (h : HypInfo) : M CompatibleHypInfo := do
  let c ← read
  if (← isDefEq (← whnf h.F) (← whnf c.F)) && (← isDefEq (← whnf h.S) (← whnf c.S)) && (← isDefEq (← whnf h.E) (← whnf c.E)) then
    let e := @Expr.const ``FFL.Entailment.WeakerThan [c.levelF, c.levelS, c.levelS, c.levelE, c.levelE]
      |>.app c.F |>.app c.S |>.app c.S |>.app c.E |>.app c.E |>.app h.𝓢 |>.app c.𝓢
    let .some wt ← trySynthInstance e
      | throwError m! "error: failed to find instance {e}"
    return ⟨h.𝓢, wt, ← exprToLit h.φ, h.proof⟩
  else throwError m! "error: proof not compatible: {h.proof}"


-- @@ L517-521 verbatim
def addHyp (𝓣 wt : Expr) (Γ Δ : Sequent) (φ : Lit) (E e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.IntProver.Theorems.add_hyp #[𝓣, wt, eΓ, eΔ, eφ, E, e]


-- @@ L523-527 verbatim
def addHyps (prover : (Γ Δ : Sequent) → M Expr) (Γ Δ : Sequent) : List HypInfo → M Expr
  |        [] => prover Γ Δ
  | h :: hyps => do
    let H ← h.toCompatible
    addHyp H.𝓢 H.WT Γ Δ H.φ H.proof <| ← addHyps prover (H.φ :: Γ) Δ hyps


-- @@ L529-532 verbatim
def main (n : ℕ) (hyps : Array HypInfo) (L R : List Expr) : M Expr := do
  let Γ ← exprListToLitList L
  let Δ ← exprListToLitList R
  addHyps (fun Γ Δ ↦ prover n false [Γ ⟶ Δ]) Γ Δ hyps.toList


-- @@ L534-537 verbatim
def toTwoSided (L R : List Expr) (e : Expr) : M Expr := do
  let Γ ← Sequent.toExpr <| ← exprListToLitList L
  let Δ ← Sequent.toExpr <| ← exprListToLitList R
  iapp ``FFL.Meta.IntProver.Theorems.to_twoSided #[Γ, Δ, e]


-- @@ L539-540 verbatim
def toProvable (φ : Expr) (e : Expr) : M Expr :=
  iapp ``FFL.Meta.IntProver.Theorems.to_provable #[φ, e]


-- @@ L542-542 verbatim
syntax termSeq := "[" (term,*) "]"


-- @@ L544-561 verbatim
elab "int_prover_2s" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 64
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `int_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps L R
    toTwoSided L R e


-- @@ L563-580 verbatim
elab "int_prover" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, φ⟩ ← getGoalProvable <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 64
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `int_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps [] [φ]
    toProvable φ e


-- @@ L582-582 verbatim
end IntProver


-- @@ L584-584 verbatim
end FFL.Meta


-- @@ L586-586 verbatim
end
