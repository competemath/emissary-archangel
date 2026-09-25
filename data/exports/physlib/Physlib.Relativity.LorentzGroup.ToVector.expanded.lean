/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

-- @@ L9-15 verbatim
/-!

# Vectors from Lorentz group elements

Every element of the Lorentz group defines a Lorentz vector, but it's first column.

-/


-- @@ L17-17 verbatim
@[expose] public section

-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace LorentzGroup

-- @@ L21-21 verbatim
open Lorentz Module

-- @@ L22-22 verbatim
open Vector


-- @@ L24-25 verbatim
/-- The Lorentz vector obtained by acting the Lorentz group element `Λ` on `basis (Sum.inl 0)`. -/
def toVector {d : ℕ} (Λ : LorentzGroup d) : Lorentz.Vector d := Λ • basis (Sum.inl 0)


-- @@ L27-29 verbatim
lemma toVector_mul {d : ℕ} (Λ₁ Λ₂ : LorentzGroup d) :
    toVector (Λ₁ * Λ₂) = Λ₁ • toVector Λ₂ := by
  rw [toVector, toVector, smul_smul]


-- @@ L31-33 verbatim
lemma toVector_neg {d : ℕ} (Λ : LorentzGroup d) :
    toVector (-Λ) = -toVector Λ := by
  simp [toVector, neg_smul]


-- @@ L35-38 verbatim
@[simp]
lemma toVector_apply {d : ℕ} (Λ : LorentzGroup d)
    (i : Fin 1 ⊕ Fin d) : (toVector Λ) i = Λ.1 i (Sum.inl 0) := by
  simp [toVector, smul_eq_sum]


-- @@ L40-43 verbatim
lemma toVector_eq_fun {d : ℕ} (Λ : LorentzGroup d) :
    toVector Λ = (fun i => Λ.1 i (Sum.inl 0)) := by
  funext i
  simp


-- @@ L45-54 verbatim
@[fun_prop]
lemma toVector_continuous {d : ℕ} : Continuous (toVector (d := d)) := by
  change Continuous (fun Λ => toVector (d := d) Λ)
  conv =>
    enter [1, Λ]
    rw [toVector_eq_fun]
  refine Vector.continuous_of_apply _ ?_
  intro i
  refine Continuous.matrix_elem ?_ i (Sum.inl 0)
  fun_prop


-- @@ L56-58 verbatim
lemma toVector_timeComponent {d : ℕ} (Λ : LorentzGroup d) :
    (toVector Λ).timeComponent = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
  simp


-- @@ L60-63 verbatim
@[simp]
lemma toVector_minkowskiProduct_self {d : ℕ} (Λ : LorentzGroup d) :
    ⟪toVector Λ, toVector Λ⟫ₘ = 1 := by
  simp [toVector, minkowskiMatrix.inl_0_inl_0]


-- @@ L65-68 verbatim
lemma one_le_abs_timeComponent {d : ℕ} (Λ : LorentzGroup d) :
    1 ≤ |Λ.1 (Sum.inl 0) (Sum.inl 0)| := by
  rw [← toVector_timeComponent Λ, ← one_le_sq_iff_one_le_abs, ← toVector_minkowskiProduct_self Λ]
  exact minkowskiProduct_self_le_timeComponent_sq (toVector Λ)


-- @@ L70-91 verbatim
lemma toVector_eq_basis_iff_timeComponent_eq_one {d : ℕ} (Λ : LorentzGroup d) :
    toVector Λ = basis (Sum.inl 0) ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  constructor
  · intro h
    rw [← toVector_timeComponent Λ, h]
    simp
  · intro h
    funext i
    have h1 := toVector_minkowskiProduct_self Λ
    rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h1
    simp [h] at h1
    simp [toVector, smul_eq_sum]
    match i with
    | Sum.inl 0 => simp [h]
    | Sum.inr j =>
      simp only [Fin.isValue, reduceCtorEq, ↓reduceIte]
      trans (toVector Λ).spatialPart j
      · simp
      simp only [toVector_apply, Fin.isValue]
      change (fun i => Λ.1 (Sum.inr i) (Sum.inl 0)) j = _
      rw [h1]
      simp


-- @@ L93-110 verbatim
lemma smul_timeComponent_eq_toVector_minkowskiProduct {d : ℕ} (Λ : LorentzGroup d)
    (v : Lorentz.Vector d) :
    (Λ • v).timeComponent = ⟪toVector Λ⁻¹, v⟫ₘ := by
  simp [timeComponent]
  rw [smul_eq_sum]
  simp only [Fin.isValue, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  congr
  · simp [inv_eq_dual, minkowskiMatrix.dual_apply, minkowskiMatrix.inl_0_inl_0]
  · simp only [Fin.isValue, inv_eq_dual, PiLp.inner_apply, toVector_apply, RCLike.inner_apply,
      conj_trivial]
    rw [← Finset.sum_neg_distrib]
    congr
    funext i
    rw [minkowskiMatrix.dual_apply]
    simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    ring


-- @@ L112-112 verbatim
end LorentzGroup


-- @@ L114-114 verbatim
end
