/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Mathlib.RepresentationTheory.Intertwining

-- @@ L11-21 verbatim
/-!

# Contraction of Real Lorentz Vectors and Covectors

We define the intertwining maps which define the contraction of a contravariant Lorentz vector with
a covariant Lorentz vector, and vice versa.

Note: This file will eventually replace `./Pre/Contraction.lean` when we move
  `realLorentzTensor` over to `Vector` and `CoVector`.

-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Matrix MatrixGroups Complex TensorProduct minkowskiMatrix


-- @@ L29-29 verbatim
namespace Lorentz

-- @@ L30-30 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L31-31 verbatim
variable {d : ℕ}


-- @@ L33-37 verbatim
/-!

## A. The definitions

-/


-- @@ L39-41 verbatim
TODO "In a similar way to `Vector.contract` and `CoVector.contract`,
  we want to define metrics and units as intertwining maps of representations.
  This should copy (and eventually replace) the definitions e.g. `./Units/Pre.lean`."


-- @@ L43-61 verbatim
/-- The intertwining map defining the contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def Vector.contract : (Vector.rep.tprod CoVector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · simp [add_mul, Finset.sum_add_distrib]
    · simp [Finset.mul_sum, mul_assoc]
    · simp [mul_add, Finset.sum_add_distrib]
    · intros
      simp_rw [CoVector.apply_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  isIntertwining' Λ := by
    ext φ ψ
    trans (Λ.1 *ᵥ φ) ⬝ᵥ ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ ψ)
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]
    · simp [dotProduct_mulVec, LorentzGroup.transpose_val,
        vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      rfl


-- @@ L63-81 verbatim
/-- The intertwining map defining the contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def CoVector.contract : (CoVector.rep.tprod Vector.rep).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := by
    refine TensorProduct.lift (LinearMap.mk₂ ℝ (fun φ ψ => ∑ i, φ i * ψ i) ?_ ?_ ?_ ?_)
    · simp [add_mul, Finset.sum_add_distrib]
    · simp [Finset.mul_sum, mul_assoc]
    · simp [mul_add, Finset.sum_add_distrib]
    · intros
      simp_rw [Vector.apply_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  isIntertwining' Λ := by
    ext φ ψ
    trans ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ φ) ⬝ᵥ (Λ.1 *ᵥ ψ)
    · simp [dotProduct, Vector.rep_apply_eq_mulVec, CoVector.rep_apply_eq_mulVec]
    · simp [dotProduct_mulVec, LorentzGroup.transpose_val,
        mulVec_transpose, vecMul_vecMul, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
      rfl


-- @@ L83-87 verbatim
/-!

## B. Properties of the contractions

-/


-- @@ L89-90 verbatim
lemma Vector.contract_tmul (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl


-- @@ L92-93 verbatim
lemma CoVector.contract_tmul (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract (φ ⊗ₜ ψ) = ∑ i, φ i * ψ i := rfl


-- @@ L95-96 verbatim
lemma Vector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (ψ : CoVector d) :
    Vector.contract (basis μ ⊗ₜ ψ) = ψ μ := by simp [Vector.contract_tmul, basis_apply]


-- @@ L98-99 verbatim
lemma CoVector.contract_basis_left (μ : Fin 1 ⊕ Fin d) (φ : Vector d) :
    CoVector.contract (basis μ ⊗ₜ φ) = φ μ := by simp [CoVector.contract_tmul, basis_apply]


-- @@ L101-102 verbatim
lemma Vector.contract_basis_right (φ : Vector d) (μ : Fin 1 ⊕ Fin d) :
    Vector.contract (φ ⊗ₜ basis μ) = φ μ := by simp [Vector.contract_tmul, basis_apply]


-- @@ L104-105 verbatim
lemma CoVector.contract_basis_right (ψ : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    CoVector.contract (ψ ⊗ₜ basis μ) = ψ μ := by simp [CoVector.contract_tmul, basis_apply]


-- @@ L107-109 verbatim
lemma Vector.contract_eq_coVector_contract (φ : Vector d) (ψ : CoVector d) :
    Vector.contract (φ ⊗ₜ ψ) = CoVector.contract (ψ ⊗ₜ φ) := by
  simp_rw [Vector.contract_tmul, CoVector.contract_tmul, mul_comm]


-- @@ L111-113 verbatim
lemma Vector.contract_rep (Λ : LorentzGroup d) (φ : Vector d) (ψ : CoVector d) :
    Vector.contract ((Vector.rep Λ φ) ⊗ₜ (CoVector.rep Λ ψ)) = Vector.contract (φ ⊗ₜ ψ) := by
  convert! Vector.contract.isIntertwining _ _ Λ (φ ⊗ₜ ψ)


-- @@ L115-117 verbatim
lemma CoVector.contract_rep (Λ : LorentzGroup d) (φ : CoVector d) (ψ : Vector d) :
    CoVector.contract ((CoVector.rep Λ φ) ⊗ₜ (Vector.rep Λ ψ)) = CoVector.contract (φ ⊗ₜ ψ) := by
  convert! CoVector.contract.isIntertwining _ _ Λ (φ ⊗ₜ ψ)


-- @@ L119-119 verbatim
end Lorentz

-- @@ L120-120 verbatim
end
