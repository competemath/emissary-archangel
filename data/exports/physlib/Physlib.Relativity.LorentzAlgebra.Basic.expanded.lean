/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.MinkowskiMatrix
public import Mathlib.Algebra.Lie.SerreConstruction

-- @@ L10-20 verbatim
/-!
# The Lorentz Algebra

We define

- Define `lorentzAlgebra` via `LieAlgebra.Orthogonal.so'` as a subalgebra of
  `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`.
- In `mem_iff` prove that a matrix is in the Lorentz algebra if and only if it satisfies the
  condition `Aᵀ * η = - η * A`.

-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Matrix

-- @@ L25-25 verbatim
open TensorProduct


-- @@ L27-27 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L29-31 verbatim
/-- The Lorentz algebra as a subalgebra of `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`. -/
def lorentzAlgebra : LieSubalgebra ℝ (Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :=
  (LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ)


-- @@ L33-33 verbatim
namespace lorentzAlgebra

-- @@ L34-34 verbatim
open minkowskiMatrix


-- @@ L36-39 verbatim
lemma transpose_eta (A : lorentzAlgebra) : A.1ᵀ * η = - η * A.1 := by
  have h : A.1 ∈ skewAdjointMatricesSubmodule η := A.2
  simpa only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, IsAdjointPair, ← neg_mul_comm]
    using h


-- @@ L41-46 verbatim
lemma mem_of_transpose_eta_eq_eta_mul_self {A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ}
    (h : Aᵀ * η = - η * A) : A ∈ lorentzAlgebra := by
  simp_all only [neg_mul, lorentzAlgebra, LieAlgebra.Orthogonal.so',
    mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    IsAdjointPair, mul_neg]
  exact h


-- @@ L48-50 verbatim
lemma mem_iff {A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} :
    A ∈ lorentzAlgebra ↔ Aᵀ * η = - η * A :=
  Iff.intro (fun h => transpose_eta ⟨A, h⟩) (fun h => mem_of_transpose_eta_eq_eta_mul_self h)


-- @@ L52-60 verbatim
lemma mem_iff' (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
    A ∈ lorentzAlgebra ↔ A = - η * Aᵀ * η := by
  rw [mem_iff]
  constructor
  · intro h
    rw [mul_assoc, h, ← mul_assoc, neg_mul_neg, minkowskiMatrix.sq, one_mul]
  · intro h
    nth_rewrite 2 [h]
    rw [← mul_assoc, ← mul_assoc, neg_mul_neg, minkowskiMatrix.sq, one_mul]


-- @@ L62-68 verbatim
lemma diag_comp (Λ : lorentzAlgebra) (μ : Fin 1 ⊕ Fin 3) : Λ.1 μ μ = 0 := by
  have h := congrArg (fun M ↦ M μ μ) $ transpose_eta Λ
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    transpose_apply, diagonal_neg, diagonal_mul, neg_mul] at h
  rcases μ with μ | μ <;>
    simp only [Sum.elim_inl, Sum.elim_inr, mul_one, one_mul, mul_neg, neg_mul, neg_neg] at h <;>
    linarith


-- @@ L70-74 verbatim
lemma time_comps (Λ : lorentzAlgebra) (i : Fin 3) :
    Λ.1 (Sum.inr i) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inr i) := by
  simpa only [Fin.isValue, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    transpose_apply, Sum.elim_inr, mul_neg, mul_one, diagonal_neg, diagonal_mul, Sum.elim_inl,
    neg_mul, one_mul, neg_inj] using congrArg (fun M ↦ M (Sum.inl 0) (Sum.inr i)) $ transpose_eta Λ


-- @@ L76-80 verbatim
lemma space_comps (Λ : lorentzAlgebra) (i j : Fin 3) :
    Λ.1 (Sum.inr i) (Sum.inr j) = - Λ.1 (Sum.inr j) (Sum.inr i) := by
  simpa only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_neg, diagonal_mul,
    Sum.elim_inr, neg_neg, one_mul, mul_diagonal, transpose_apply, mul_neg, mul_one] using
    (congrArg (fun M ↦ M (Sum.inr i) (Sum.inr j)) $ transpose_eta Λ).symm


-- @@ L82-82 verbatim
end lorentzAlgebra
