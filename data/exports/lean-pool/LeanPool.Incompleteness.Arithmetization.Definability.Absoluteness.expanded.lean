/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Definability.Boldface
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.CobhamR0


-- @@ L12-12 verbatim
/-! # Absoluteness -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace FirstOrder

-- @@ L19-19 verbatim
namespace Arith


-- @@ L21-21 verbatim
open LO.Arith


-- @@ L23-24 expanded
lemma nat_modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence oRing k} :
    (Evalbm ℕ v) φ ↔
      Models₀ ℕ
        (LO.FirstOrder.Rewriting.substitute φ (fun i ↦ Semiterm.Operator.numeral oRing (v i))) :=
  by simp [models_iff]


-- @@ L26-26 expanded
variable (V : Type*) [ORingStruc V] [ModelsTheory V PeanoMinus]


-- @@ L28-30 expanded
lemma modelsWithParam_iff_models_substs {v : Fin k → ℕ} {φ : Semisentence oRing k} :
    (Evalbm V (v ·)) φ ↔
      Models₀ V
        (LO.FirstOrder.Rewriting.substitute φ (fun i ↦ Semiterm.Operator.numeral oRing (v i))) :=
  by simp [models_iff, numeral_eq_natCast]


-- @@ L32-39 expanded
lemma shigmaZero_absolute {k} (φ : Sg0.Semisentence k) (v : Fin k → ℕ) :
    (Evalbm ℕ v) φ.val ↔ (Evalbm V (v ·)) φ.val :=
  ⟨by
    rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
    exact nat_extention_sigmaOne V (by simp),
    by
    rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
    exact nat_extention_piOne V (by simp)⟩


-- @@ L41-45 verbatim
lemma _root_.LO.FirstOrder.Arith.Defined.shigmaZero_absolute {k} {R : (Fin k → ℕ) → Prop} {R' :
    (Fin k → V) → Prop} {φ :
    Sg0.Semisentence k}
    (hR : Sg0.Defined R φ) (hR' : Sg0.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by simpa [hR.iff, hR'.iff] using Arith.shigmaZero_absolute V φ v


-- @@ L47-52 expanded
lemma _root_.LO.FirstOrder.Arith.DefinedFunction.shigmaZero_absolute_func {k} {f : (Fin k → ℕ) → ℕ}
    {f' : (Fin k → V) → V} {φ : Sg0.Semisentence (k + 1)} (hf : Sg0.DefinedFunction f φ)
    (hf' : Sg0.DefinedFunction f' φ) (v : Fin k → ℕ) : (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaZero_absolute V hf hf' (vecCons (f v) v)


-- @@ L54-57 expanded
lemma sigmaOne_upward_absolute {k} (φ : Sg1.Semisentence k) (v : Fin k → ℕ) :
    (Evalbm ℕ v) φ.val → (Evalbm V (v ·)) φ.val :=
  by
  rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_sigmaOne V (by simp)


-- @@ L59-62 expanded
lemma piOne_downward_absolute {k} (φ : Pg1.Semisentence k) (v : Fin k → ℕ) :
    (Evalbm V (v ·)) φ.val → (Evalbm ℕ v) φ.val :=
  by
  rw [nat_modelsWithParam_iff_models_substs, modelsWithParam_iff_models_substs]
  exact nat_extention_piOne V (by simp)


-- @@ L64-68 expanded
lemma deltaOne_absolute {k} (φ : Dlt1.Semisentence k) (properNat : φ.ProperOn ℕ)
    (proper : φ.ProperOn V) (v : Fin k → ℕ) : (Evalbm ℕ v) φ.val ↔ (Evalbm V (v ·)) φ.val :=
  ⟨by simpa [HierarchySymbol.Semiformula.val_sigma] using sigmaOne_upward_absolute V φ.sigma v, by
    simpa [proper.iff', properNat.iff'] using piOne_downward_absolute V φ.pi v⟩


-- @@ L70-75 verbatim
lemma _root_.LO.FirstOrder.Arith.Defined.shigmaOne_absolute {k} {R : (Fin k → ℕ) → Prop} {R' :
    (Fin k → V) → Prop} {φ :
    Dlt1.Semisentence k}
    (hR : Dlt1.Defined R φ) (hR' : Dlt1.Defined R' φ) (v : Fin k → ℕ) :
    R v ↔ R' (fun i ↦ (v i : V)) := by
  simpa [hR.df.iff, hR'.df.iff] using deltaOne_absolute V φ hR.proper hR'.proper v


-- @@ L77-83 expanded
lemma _root_.LO.FirstOrder.Arith.DefinedFunction.shigmaOne_absolute_func {k} {f : (Fin k → ℕ) → ℕ}
    {f' : (Fin k → V) → V} {φ : Sg1.Semisentence (k + 1)} (hf : Sg1.DefinedFunction f φ)
    (hf' : Sg1.DefinedFunction f' φ) (v : Fin k → ℕ) : (f v : V) = f' (fun i ↦ (v i)) := by
  simpa using Defined.shigmaOne_absolute V hf.graph_delta hf'.graph_delta (vecCons (f v) v)


-- @@ L85-85 verbatim
variable {V}


-- @@ L87-98 expanded
lemma models_iff_of_Sigma0 {σ : Semisentence oRing n} (hσ : Hierarchy SigmaSymbol.sigma 0 σ)
    {e : Fin n → ℕ} : (Evalbm V (e ·)) σ ↔ (Evalbm ℕ e) σ :=
  by
  by_cases h : (Evalbm ℕ e) σ <;> simp [h]
  · have : (Evalbm V (e ·)) σ := by
      simpa [numeral_eq_natCast] using
        LO.Arith.bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) h
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : (Evalbm ℕ e) (Tilde.tilde σ) := by simpa using h
    have : (Evalbm V (e ·)) (Tilde.tilde σ) := by
      simpa [numeral_eq_natCast] using
        LO.Arith.bold_sigma_one_completeness' (M := V) (by simp [Hierarchy.of_zero hσ]) this
    simpa using this


-- @@ L100-111 expanded
lemma models_iff_of_Delta1 {σ : Dlt1.Semisentence n} (hσ : σ.ProperOn ℕ) (hσV : σ.ProperOn V)
    {e : Fin n → ℕ} : (Evalbm V (e ·)) σ.val ↔ (Evalbm ℕ e) σ.val :=
  by
  by_cases h : (Evalbm ℕ e) σ.val <;> simp [h]
  · have : (Evalbm ℕ e) σ.sigma.val := by simpa [HierarchySymbol.Semiformula.val_sigma] using h
    have : (Evalbm V (e ·)) σ.sigma.val := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [HierarchySymbol.Semiformula.val_sigma] using this
  · have : (Evalbm ℕ e) (Tilde.tilde σ.pi.val) := by simpa [hσ.iff'] using h
    have : (Evalbm V (e ·)) (Tilde.tilde σ.pi.val) := by
      simpa [numeral_eq_natCast] using LO.Arith.bold_sigma_one_completeness' (M := V) (by simp) this
    simpa [hσV.iff'] using this


-- @@ L113-113 expanded
variable {T : Theory oRing} [WeakerThan PeanoMinus T] [Sigma1Sound T]


-- @@ L115-117 expanded
noncomputable instance : WeakerThan CobhamR0 T :=
  Entailment.WeakerThan.trans (𝓣 := PeanoMinus) inferInstance inferInstance


-- @@ L119-123 expanded
theorem sigma_one_completeness_iff_param {σ : Semisentence oRing n}
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) {e : Fin n → ℕ} :
    (Evalbm ℕ e) σ ↔
      Provable₀ T
        (LO.FirstOrder.Rewriting.substitute σ fun x ↦ Semiterm.Operator.numeral oRing (e x)) :=
  Iff.trans (by simp [models_iff, Semiformula.eval_substs])
    (sigma_one_completeness_iff (T := T) (by simp [hσ]))


-- @@ L125-132 expanded
lemma models_iff_provable_of_Sigma0_param {σ : Semisentence oRing n}
    (hσ : Hierarchy SigmaSymbol.sigma 0 σ) {e : Fin n → ℕ} :
    (Evalbm V (e ·)) σ ↔
      Provable₀ T
        (LO.FirstOrder.Rewriting.substitute σ fun x ↦ Semiterm.Operator.numeral oRing (e x)) :=
  by
  calc
    (Evalbm V (e ·)) σ ↔ (Evalbm ℕ e) σ := by simp [models_iff_of_Sigma0 hσ]
    _ ↔
        Provable₀ T
          (LO.FirstOrder.Rewriting.substitute σ fun x ↦ Semiterm.Operator.numeral oRing (e x)) :=
      by apply sigma_one_completeness_iff_param (by simp [Hierarchy.of_zero hσ])


-- @@ L134-145 expanded
lemma models_iff_provable_of_Delta1_param {σ : Dlt1.Semisentence n} (hσ : σ.ProperOn ℕ)
    (hσV : σ.ProperOn V) {e : Fin n → ℕ} :
    (Evalbm V (e ·)) σ.val ↔
      Provable₀ T
        (LO.FirstOrder.Rewriting.substitute σ fun x ↦ Semiterm.Operator.numeral oRing (e x)) :=
  by
  calc
    (Evalbm V (e ·)) σ.val ↔ (Evalbm ℕ e) σ.val := by simp [models_iff_of_Delta1 hσ hσV]
    _ ↔ (Evalbm ℕ e) σ.sigma.val := by simp [HierarchySymbol.Semiformula.val_sigma]
    _ ↔
        Provable₀ T
          (LO.FirstOrder.Rewriting.substitute σ.sigma.val fun x ↦
            Semiterm.Operator.numeral oRing (e x)) :=
      by apply sigma_one_completeness_iff_param (by simp)
    _ ↔
        Provable₀ T
          (LO.FirstOrder.Rewriting.substitute σ.val fun x ↦
            Semiterm.Operator.numeral oRing (e x)) :=
      by simp [HierarchySymbol.Semiformula.val_sigma]


-- @@ L147-147 verbatim
end Arith


-- @@ L149-149 verbatim
end FirstOrder

-- @@ L150-150 verbatim
end LO
