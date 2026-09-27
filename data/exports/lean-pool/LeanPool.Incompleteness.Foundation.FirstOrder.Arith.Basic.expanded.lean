/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Eq
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Corollaries


-- @@ L13-13 verbatim
/-! # Basic -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO


-- @@ L20-21 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class ORingStruc (α : Type*) extends Zero α, One α, Add α, Mul α, LT α


-- @@ L23-23 verbatim
instance [Zero α] [One α] [Add α] [Mul α] [LT α] : ORingStruc α where


-- @@ L25-25 verbatim
namespace ORingStruc


-- @@ L27-27 verbatim
variable {α : Type*} [ORingStruc α]


-- @@ L29-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def numeral : ℕ → α
  | 0     => 0
  | 1     => 1
  | n + 2 => numeral (n + 1) + 1


-- @@ L35-35 verbatim
@[simp] lemma zero_eq_zero : (numeral 0 : α) = 0 := rfl


-- @@ L37-37 verbatim
@[simp] lemma one_eq_one : (numeral 1 : α) = 1 := rfl


-- @@ L39-39 verbatim
end ORingStruc


-- @@ L41-44 verbatim
@[simp] lemma _root_.LO.Nat.numeral_eq : (n : ℕ) → ORingStruc.numeral n = n
  | 0     => rfl
  | 1     => rfl
  | n + 2 => by simp[ORingStruc.numeral, Nat.numeral_eq (n + 1)]


-- @@ L46-46 verbatim
namespace FirstOrder


-- @@ L48-48 verbatim
namespace Language


-- @@ L50-50 verbatim
variable {L : Language} [L.ORing]


-- @@ L52-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def oringEmb : oRing →ᵥ L
    where
  func := fun {k} f ↦
    match k, f with
    | _, Zero.zero => Zero.zero
    | _, One.one => One.one
    | _, Add.add => Add.add
    | _, Mul.mul => Mul.mul
  rel := fun {k} r ↦
    match k, r with
    | _, Eq.eq => Eq.eq
    | _, LT.lt => LT.lt


-- @@ L65-65 expanded
@[simp]
lemma oringEmb_zero : (oringEmb : oRing →ᵥ L).func Zero.zero = Zero.zero :=
  rfl


-- @@ L67-67 expanded
@[simp]
lemma oringEmb_one : (oringEmb : oRing →ᵥ L).func One.one = One.one :=
  rfl


-- @@ L69-69 expanded
@[simp]
lemma oringEmb_add : (oringEmb : oRing →ᵥ L).func Add.add = Add.add :=
  rfl


-- @@ L71-71 expanded
@[simp]
lemma oringEmb_mul : (oringEmb : oRing →ᵥ L).func Mul.mul = Mul.mul :=
  rfl


-- @@ L73-73 expanded
@[simp]
lemma oringEmb_eq : (oringEmb : oRing →ᵥ L).rel Eq.eq = Eq.eq :=
  rfl


-- @@ L75-75 expanded
@[simp]
lemma oringEmb_lt : (oringEmb : oRing →ᵥ L).rel LT.lt = LT.lt :=
  rfl


-- @@ L77-77 verbatim
end Language


-- @@ L79-79 verbatim
section «lp_section_1»


-- @@ L81-81 verbatim
variable {L : Language} [L.ORing]


-- @@ L83-83 verbatim
namespace Semiterm


-- @@ L85-85 expanded
instance : Coe (Semiterm oRing ξ n) (Semiterm L ξ n) :=
  ⟨lMap Language.oringEmb⟩


-- @@ L87-90 expanded
@[simp]
lemma oringEmb_zero :
    Semiterm.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.Zero.zero.const : Semiterm oRing ξ n) =
      Operator.Zero.zero.const :=
  by simp [Operator.const, lMap_func, Operator.operator, Operator.Zero.term_eq, Matrix.empty_eq]


-- @@ L92-95 expanded
@[simp]
lemma oringEmb_one :
    Semiterm.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.One.one.const : Semiterm oRing ξ n) =
      Operator.One.one.const :=
  by simp [Operator.const, lMap_func, Operator.operator, Operator.One.term_eq, Matrix.empty_eq]


-- @@ L97-103 expanded
@[simp]
lemma oringEmb_add (v : Fin 2 → Semiterm oRing ξ n) :
    Semiterm.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.Add.add.operator v) =
      Operator.Add.add.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] :=
  by
  simp only [Operator.operator, Operator.Add.term_eq, Rew.func, Rew.emb_bvar, Rew.substs_bvar,
    lMap_func, Language.oringEmb_add, Fin.isValue, Matrix.empty_eq, func.injEq, heq_eq_eq, true_and]
  funext i; cases i using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L105-111 expanded
@[simp]
lemma oringEmb_mul (v : Fin 2 → Semiterm oRing ξ n) :
    Semiterm.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.Mul.mul.operator v) =
      Operator.Mul.mul.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] :=
  by
  simp only [Operator.operator, Operator.Mul.term_eq, Rew.func, Rew.emb_bvar, Rew.substs_bvar,
    lMap_func, Language.oringEmb_mul, Fin.isValue, Matrix.empty_eq, func.injEq, heq_eq_eq, true_and]
  funext i; cases i using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L113-125 expanded
@[simp]
lemma oringEmb_numeral (z : ℕ) :
    Semiterm.lMap (Language.oringEmb : oRing →ᵥ L)
        ((Operator.numeral oRing z).const : Semiterm oRing ξ n) =
      (Operator.numeral L z).const :=
  by
  match z with
  | 0 => exact oringEmb_zero
  | 1 => exact oringEmb_one
  |
  z +
      2 =>
    simp only [Operator.numeral_add_two, Operator.operator_comp, oringEmb_add, Fin.isValue,
      Matrix.vecCons_zero, Matrix.cons_val_one, oringEmb_one]
    congr; funext i; cases i using Fin.cases
    · exact oringEmb_numeral (z + 1)
    · simp


-- @@ L127-127 verbatim
end Semiterm


-- @@ L129-129 verbatim
namespace Semiformula


-- @@ L131-131 expanded
instance : Coe (Semiformula oRing ξ n) (Semiformula L ξ n) :=
  ⟨Semiformula.lMap Language.oringEmb⟩


-- @@ L133-133 expanded
instance : Coe (Theory oRing) (Theory L) :=
  ⟨(Semiformula.lMap Language.oringEmb '' ·)⟩


-- @@ L135-140 expanded
@[simp]
lemma oringEmb_eq (v : Fin 2 → Semiterm oRing ξ n) :
    Semiformula.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.Eq.eq.operator v) =
      Operator.Eq.eq.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] :=
  by
  simp only [Operator.operator, Operator.Eq.sentence_eq, rew_rel, Rew.emb_bvar, Rew.substs_bvar,
    lMap_rel, Language.oringEmb_eq, Fin.isValue, rel.injEq, heq_eq_eq, true_and]
  funext i; cases i using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L142-147 expanded
@[simp]
lemma oringEmb_lt (v : Fin 2 → Semiterm oRing ξ n) :
    Semiformula.lMap (Language.oringEmb : oRing →ᵥ L) (Operator.LT.lt.operator v) =
      Operator.LT.lt.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] :=
  by
  simp only [Operator.operator, Operator.LT.sentence_eq, rew_rel, Rew.emb_bvar, Rew.substs_bvar,
    lMap_rel, Language.oringEmb_lt, Fin.isValue, rel.injEq, heq_eq_eq, true_and]
  funext i; cases i using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L149-149 verbatim
end Semiformula


-- @@ L151-151 verbatim
end «lp_section_1»


-- @@ L153-153 verbatim
open Semiterm Semiformula


-- @@ L155-156 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Polynomial (n : ℕ) : Type :=
  Semiterm oRing Empty n


-- @@ L158-162 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.FirstOrder.Structure.ORing (L : Language) [L.ORing] (M :
    Type w) [ORingStruc M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M,
    Structure.LT L M


-- @@ L164-164 verbatim
attribute [instance] Structure.ORing.mk


-- @@ L166-166 verbatim
namespace Structure


-- @@ L168-169 verbatim
variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingStruc M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]


-- @@ L171-177 verbatim
@[simp] lemma numeral_eq_numeral : (z :
    ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStruc.numeral z :
    M)
  | 0     => by simp[ORingStruc.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp[ORingStruc.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp[ORingStruc.numeral, Semiterm.Operator.numeral_add_two,
                  Semiterm.Operator.val_comp, Matrix.fun_eq_vec₂, numeral_eq_numeral (z + 1)]


-- @@ L179-179 verbatim
end Structure


-- @@ L181-181 verbatim
namespace Semiformula


-- @@ L183-183 verbatim
variable {L : Language} [L.LT] [L.Zero] [L.One] [L.Add]


-- @@ L185-187 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ballLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  φ.ballLT (Semiterm.Operator.Add.add.operator ![t, Semiterm.numeral 1])


-- @@ L189-191 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def bexLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  φ.bexLT (Semiterm.Operator.Add.add.operator ![t, Semiterm.numeral 1])


-- @@ L193-193 verbatim
variable {M : Type*} {s : Structure L M} [LT M] [One M] [Add M] [Structure.LT L M]

-- @@ L194-194 verbatim
variable [Structure.One L M] [Structure.Add L M]


-- @@ L196-196 verbatim
variable {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}


-- @@ L198-200 expanded
lemma eval_ballLTSucc {e ε} :
    Eval s e ε (φ.ballLTSucc t) ↔ ∀ x < t.val s e ε + 1, Eval s (vecCons x e) ε φ := by
  simp [ballLTSucc, Operator.numeral]


-- @@ L202-204 expanded
lemma eval_bexLTSucc {e ε} :
    Eval s e ε (φ.bexLTSucc t) ↔ ∃ x < t.val s e ε + 1, Eval s (vecCons x e) ε φ := by
  simp [bexLTSucc, Operator.numeral]


-- @@ L206-206 verbatim
end Semiformula


-- @@ L208-208 verbatim
namespace BinderNotation


-- @@ L210-210 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L212-213 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " <⁺ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L215-216 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " <⁺ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula


-- @@ L218-228 expanded
macro_rules
  |
  `(Semiformula.ballLTSucc foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.ballLTSucc foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])
  |
  `(Semiformula.bexLTSucc foTerm[$binders* | $fbinders* | $t]
        foFormula[$x$binders* | $fbinders* | $φ]) =>
    do
    if binders.elem x then 
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.bexLTSucc foTerm[$binders* | $fbinders* | $t]
            foFormula[$binders'* | $fbinders* | $φ])


-- @@ L230-230 verbatim
end BinderNotation


-- @@ L232-232 verbatim
namespace Arith


-- @@ L234-237 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class SoundOn {L : Language} [Structure L ℕ] (T : Theory L) (F : Sentence L → Prop) where
  sound : ∀ {σ}, F σ → Provable T ↑σ → Models₀ ℕ σ


-- @@ L239-239 verbatim
section «lp_section_2»


-- @@ L241-241 verbatim
variable {L : Language} [Structure L ℕ] (T : Theory L) (F : Set (Sentence L))


-- @@ L243-245 verbatim
lemma consistent_of_sound [SoundOn T F] (hF : ⊥ ∈ F) : Entailment.Consistent T :=
  Entailment.consistent_iff_unprovable_bot.mpr fun b ↦ by
    simpa [Models₀] using SoundOn.sound (F := F) hF b


-- @@ L247-247 verbatim
end «lp_section_2»


-- @@ L249-249 verbatim
section «lp_section_3»


-- @@ L251-251 verbatim
variable {L : Language.{u}} [L.ORing] (T : Theory L)


-- @@ L253-264 expanded
lemma consequence_of [WeakerThan eqAxiom T] (φ : SyntacticFormula L)
    (H :
      ∀ (M : Type (max u w)) [ORingStruc M] [Structure L M] [Structure.ORing L M]
        [ModelsTheory M T], Models M φ) :
    Consequence T φ :=
  consequence_iff_consequence.{u, w}.mp <|
    consequence_iff_eq.mpr fun M _ _ _ hT =>
      letI : ModelsTheory (Structure.Model L M) T :=
        ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
      (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
        (H (Structure.Model L M))


-- @@ L266-266 verbatim
end «lp_section_3»


-- @@ L268-268 verbatim
section «lp_section_4»


-- @@ L270-270 verbatim
open Encodable Semiterm.Operator.GoedelNumber


-- @@ L272-273 expanded
instance {α} [Encodable α] : Semiterm.Operator.GoedelNumber oRing α :=
  Semiterm.Operator.GoedelNumber.ofEncodable


-- @@ L275-276 expanded
lemma goedelNumber_def {α} [Encodable α] (a : α) :
    goedelNumber a = Semiterm.Operator.encode oRing a :=
  rfl


-- @@ L278-279 expanded
lemma goedelNumber'_def {α} [Encodable α] (a : α) :
    (GoedelQuote.quote a : Semiterm oRing ξ n) = Semiterm.Operator.encode oRing a :=
  rfl


-- @@ L281-283 expanded
@[simp]
lemma encode_encode_eq {α} [Encodable α] (a : α) :
    (goedelNumber (encode a) : Semiterm.Const oRing) = goedelNumber a := by
  simp [Semiterm.Operator.encode, goedelNumber_def]


-- @@ L285-285 verbatim
end «lp_section_4»


-- @@ L287-287 verbatim
end Arith


-- @@ L289-289 verbatim
namespace Theory


-- @@ L291-291 verbatim
variable {L : Language} [L.Eq]


-- @@ L293-296 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive EQ' : Theory L
  | refl : EQ' (Semiformula.Operator.operator Operator.Eq.eq ![&0, &0])
  |
  replace (φ : SyntacticSemiformula L 1) :
    EQ'
      (UnivQuantifier.univ
        (UnivQuantifier.univ
          (Arrow.arrow (Semiformula.Operator.operator Operator.Eq.eq ![#1, #0])
            (Arrow.arrow (LO.FirstOrder.Rewriting.substitute φ (vecCons #1 ![]))
              (LO.FirstOrder.Rewriting.substitute φ (vecCons #0 ![]))))))


-- @@ L298-299 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "𝐄𝐐'" => EQ'


-- @@ L301-301 verbatim
variable (T : Theory L)


-- @@ L303-314 expanded
noncomputable instance _root_.LO.FirstOrder.Theory.EQ'.subTheoryOfEQ :
    WeakerThan (EQ' : Theory L) eqAxiom :=
  Entailment.WeakerThan.ofAxm! <| by
    rintro φ h
    rcases (show EQ' φ from h)
    case refl => apply Entailment.by_axm _ eqAxiom.refl
    case replace φ =>
      apply complete ?_
      apply EQ.provOf.{_, 0} _ ?_
      intro M _ s _ _
      simp [models_iff, Semiformula.eval_substs]


-- @@ L316-316 verbatim
end Theory


-- @@ L318-318 verbatim
end FirstOrder


-- @@ L320-320 verbatim
end LO
