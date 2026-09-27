/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Completeness
import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.Corollaries


-- @@ L13-13 verbatim
/-! # CobhamR0 -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L20-20 verbatim
namespace LO


-- @@ L22-22 verbatim
namespace Arith


-- @@ L24-24 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L26-26 expanded
variable {M : Type*} [ORingStruc M] [ModelsTheory M CobhamR0]


-- @@ L28-28 verbatim
open Language ORingStruc


-- @@ L30-31 verbatim
lemma numeral_add_numeral (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₁ n m) (fun _ ↦ 0)


-- @@ L33-34 verbatim
lemma numeral_mul_numeral (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m) := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₂ n m) (fun _ ↦ 0)


-- @@ L36-37 verbatim
lemma numeral_ne_numeral_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m := by
  simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₃ n m h) (fun _ ↦ 0)


-- @@ L39-46 verbatim
lemma lt_numeral_iff {x : M} {n : ℕ} : x < numeral n ↔ ∃ i : Fin n, x = numeral i := by
  have := by simpa [models_iff] using ModelsTheory.models M (Theory.CobhamR0.Ω₄ n) (fun _ ↦ 0)
  constructor
  · intro hx
    rcases (this x).mp hx with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (this (numeral i)).mpr ⟨i, by simp, rfl⟩


-- @@ L48-49 verbatim
@[simp] lemma numeral_inj_iff {n m : ℕ} : (numeral n : M) = numeral m ↔ n = m :=
  ⟨by contrapose; exact numeral_ne_numeral_of_ne, by rintro rfl; rfl⟩


-- @@ L51-57 verbatim
@[simp] lemma numeral_lt_numeral_iff : (numeral n : M) < numeral m ↔ n < m :=
  ⟨by contrapose
      intro h H
      rcases lt_numeral_iff.mp H with ⟨i, hi⟩
      rcases numeral_inj_iff.mp hi
      exact (lt_self_iff_false m).mp (lt_of_le_of_lt (Nat.le_of_not_lt h) i.prop),
   fun h ↦ lt_numeral_iff.mpr ⟨⟨n, h⟩, by simp⟩⟩


-- @@ L59-59 verbatim
open Hierarchy


-- @@ L61-71 expanded
lemma val_numeral {n} :
    ∀ (t : Semiterm oRing ξ n),
      ∀ v f,
        Semiterm.valm M (fun x ↦ numeral (v x)) (fun x ↦ numeral (f x)) t =
          numeral (Semiterm.valm ℕ v f t)
  | #_, _, _ => by simp
  | &x, _, _ => by simp
  | Semiterm.func Language.Zero.zero _, e, f => by simp
  | Semiterm.func Language.One.one _, e, f => by simp
  | Semiterm.func Language.Add.add v, e, f => by
    simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_add_numeral]
  | Semiterm.func Language.Mul.mul v, e, f => by
    simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_mul_numeral]


-- @@ L73-100 expanded
lemma bold_sigma_one_completeness {n} {φ : Semiformula oRing ξ n}
    (hp : Hierarchy SigmaSymbol.sigma 1 φ) {e f} :
    Semiformula.Evalm ℕ e f φ →
      Semiformula.Evalm M (fun x ↦ numeral (e x)) (fun x ↦ numeral (f x)) φ :=
  by
  revert e
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hNEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hLT => intro n t₁ t₂ e; simp [val_numeral]
  case hNLT => intro n t₁ t₂ e; simp [val_numeral]
  case hAnd => simp_all
  case hOr =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rintro n φ ψ _ _ ihp ihq e (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq
  case
    hBall =>
    simp only [Semiformula.eval_ball, Nat.succ_eq_add_one, Semiformula.eval_operator₂,
      Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Structure.LT.lt, val_numeral]
    intro n t φ _ ihp e hp x hx
    rcases lt_numeral_iff.mp hx with ⟨x, rfl⟩
    simpa [Matrix.comp_vecCons'] using ihp (hp x (by simp))
  case hEx =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one, forall_exists_index]
    intro n φ _ ihp e x hp
    exact ⟨numeral x, by simpa [Matrix.comp_vecCons'] using ihp hp⟩


-- @@ L102-106 expanded
lemma sigma_one_completeness {σ : Sentence oRing} (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Models₀ ℕ σ → Models₀ M σ :=
  by
  suffices Semiformula.Evalbm ℕ ![] σ → Semiformula.Evalbm M ![] σ by simpa [models₀_iff]
  intro h
  simpa [Matrix.empty_eq, Empty.eq_elim] using bold_sigma_one_completeness hσ h


-- @@ L108-108 verbatim
end Arith


-- @@ L110-110 verbatim
namespace FirstOrder

-- @@ L111-111 verbatim
namespace Arith


-- @@ L113-113 verbatim
open LO.Arith


-- @@ L115-115 expanded
variable {T : Theory oRing} [WeakerThan CobhamR0 T]


-- @@ L117-122 expanded
theorem sigma_one_completeness {σ : Sentence oRing} (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Models₀ ℕ σ → Provable T ↑σ := fun H =>
  haveI : WeakerThan eqAxiom T :=
    Entailment.WeakerThan.trans (𝓣 := CobhamR0) inferInstance inferInstance
  complete <|
    oRing_consequence_of.{0} _ _ <| fun M _ _ =>
      by
      have : ModelsTheory M CobhamR0 :=
        ModelsTheory.of_provably_subtheory M CobhamR0 T inferInstance
      exact LO.Arith.sigma_one_completeness hσ H


-- @@ L124-127 expanded
theorem sigma_one_completeness_iff [ss : Sigma1Sound T] {σ : Sentence oRing}
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) : Models₀ ℕ σ ↔ Provable T ↑σ :=
  haveI : WeakerThan CobhamR0 T := Entailment.WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  ⟨fun h ↦ sigma_one_completeness (T := T) hσ h, fun h ↦ ss.sound (by simp [hσ]) h⟩


-- @@ L129-133 verbatim
/-!
## Unprovable theorems of $\mathsf{R}_0$

$\omega + 1$ (the structure of order type $\omega + 1$) is a models of $\mathsf{R}_0$.
-/


-- @@ L135-135 verbatim
/-! ω + 1 models 𝐑₀ -/

-- @@ L136-136 verbatim
namespace Countermodel


-- @@ L138-139 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def OmegaAddOne := Option ℕ


-- @@ L141-141 verbatim
namespace OmegaAddOne


-- @@ L143-143 verbatim
instance : NatCast OmegaAddOne := ⟨fun i ↦ .some i⟩


-- @@ L145-145 verbatim
instance (n : ℕ) : OfNat OmegaAddOne n := ⟨.some n⟩


-- @@ L147-147 verbatim
instance : Top OmegaAddOne := ⟨.none⟩


-- @@ L149-164 verbatim
instance : ORingStruc OmegaAddOne where
  add a b :=
    match a, b with
    | .some i, .some j => i + j
    |   .none, _       => 0
    |       _,   .none => 0
  mul a b :=
    match a, b with
    | .some i, .some j => (i * j)
    |   .none, _       => 0
    |       _,   .none => 0
  lt a b :=
    match a, b with
    | .some i, .some j => i < j
    |   .none, _       => False
    | .some _,   .none => True


-- @@ L166-166 verbatim
@[simp] lemma coe_zero : (↑(0 : ℕ) : OmegaAddOne) = 0 := rfl


-- @@ L168-168 verbatim
@[simp] lemma coe_one : (↑(1 : ℕ) : OmegaAddOne) = 1 := rfl


-- @@ L170-170 verbatim
@[simp] lemma coe_add (a b : ℕ) : ↑(a + b) = ((↑a + ↑b) : OmegaAddOne) := rfl


-- @@ L172-172 verbatim
@[simp] lemma coe_mul (a b : ℕ) : ↑(a * b) = ((↑a * ↑b) : OmegaAddOne) := rfl


-- @@ L174-174 verbatim
@[simp] lemma lt_coe_iff (n m : ℕ) : (n : OmegaAddOne) < (m : OmegaAddOne) ↔ n < m := by rfl


-- @@ L176-176 verbatim
@[simp] lemma not_top_lt (n : ℕ) : ¬⊤ < (n : OmegaAddOne) := by rintro ⟨⟩


-- @@ L178-178 verbatim
@[simp] lemma lt_top (n : ℕ) : (n : OmegaAddOne) < ⊤ := by trivial


-- @@ L180-180 verbatim
@[simp] lemma top_add_zero : (⊤ : OmegaAddOne) + 0 = 0 := by rfl


-- @@ L182-186 verbatim
@[simp] lemma numeral_eq (n : ℕ) : (ORingStruc.numeral n : OmegaAddOne) = n :=
  match n with
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStruc.numeral, numeral_eq (n + 1)]; rfl


-- @@ L188-189 verbatim
@[simp] lemma coe_inj_iff (n m : ℕ) : (↑n : OmegaAddOne) = (↑m :
    OmegaAddOne) ↔ n = m := Option.some_inj


-- @@ L191-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def cases' {P : OmegaAddOne → Sort*}
    (nat : (n : ℕ) → P n)
    (top : P ⊤) : ∀ x : OmegaAddOne, P x
  | .some n => nat n
  |   .none => top


-- @@ L198-224 expanded
instance : ModelsTheory OmegaAddOne CobhamR0 :=
  ⟨by
    intro σ h
    rcases h
    case equal
      h =>
      have : ModelsTheory OmegaAddOne (eqAxiom : Theory oRing) := inferInstance
      exact modelsTheory_iff.mp this h
    case Ω₁ n m =>
      simp only [models_def, Semiformula.eval_operator₂, Semiterm.val_operator₂, Semiterm.val_const,
        Structure.numeral_eq_numeral, numeral_eq, Structure.Add.add, coe_add, Structure.Eq.eq,
        implies_true]
    case Ω₂ n m =>
      simp only [models_def, Semiformula.eval_operator₂, Semiterm.val_operator₂, Semiterm.val_const,
        Structure.numeral_eq_numeral, numeral_eq, Structure.Mul.mul, coe_mul, Structure.Eq.eq,
        implies_true]
    case Ω₃
      h =>
      simp only [models_def, LogicalConnective.HomClass.map_neg, Semiformula.eval_operator₂,
        Semiterm.val_const, Structure.numeral_eq_numeral, numeral_eq, Structure.Eq.eq, coe_inj_iff,
        LogicalConnective.Prop.neg_eq, forall_const]
      exact h
    case Ω₄
      n =>
      simp only [Nat.reduceAdd, Fin.isValue, models_def, Semiformula.eval_all, Nat.succ_eq_add_one,
        LogicalConnective.HomClass.map_iff, Semiformula.eval_operator₂, Semiterm.val_bvar,
        Matrix.vecCons_zero, Semiterm.val_const, Structure.numeral_eq_numeral, numeral_eq,
        Structure.LT.lt, hom_disj_prop, Structure.Eq.eq, LogicalConnective.Prop.iff_eq,
        forall_const]
      intro x
      cases x using cases' <;> simp⟩


-- @@ L226-226 verbatim
end OmegaAddOne


-- @@ L228-228 verbatim
end Countermodel


-- @@ L230-231 expanded
lemma R₀_unprovable_add_zero :
    Unprovable CobhamR0
      (Semiformula.Operator.operator Operator.Eq.eq
        ![Semiterm.Operator.Add.add.operator ![&0, Semiterm.numeral 0], &0]) :=
  unprovable_of_countermodel (M := Countermodel.OmegaAddOne) (fun _ ↦ ⊤) _ (by simp)


-- @@ L233-233 verbatim
end Arith

-- @@ L234-234 verbatim
end FirstOrder


-- @@ L236-236 verbatim
end LO


-- @@ L238-238 verbatim
end «lp_nc_section_1»
