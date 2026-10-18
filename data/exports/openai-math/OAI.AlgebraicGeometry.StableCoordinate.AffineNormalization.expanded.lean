import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Constant affine changes of polynomial coordinates

The automorphisms in this file normalize a nonzero scalar multiple of a
coordinate and a constant translate.  They are actual algebra automorphisms
of the whole polynomial ring, with explicit polynomial inverses.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
section Generic


-- @@ L21-21 verbatim
variable {k σ : Type*} [Field k]


-- @@ L23-40 verbatim
/-- Simultaneously replace every variable `X i` by `a * X i + b`. -/
noncomputable def affineAll (a b : k) (ha : a ≠ 0) :
    MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom
    (aeval fun i => C a * X i + C b)
    (aeval fun i => C a⁻¹ * (X i - C b))
    (by
      apply algHom_ext
      intro i
      simp only [AlgHom.comp_apply, map_mul, map_sub, aeval_X, aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq]
      rw [add_sub_cancel_right, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul])
    (by
      apply algHom_ext
      intro i
      simp only [AlgHom.comp_apply, map_mul, map_add, aeval_X, aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, sub_add_cancel])


-- @@ L42-45 verbatim
@[simp] theorem affineAll_X (a b : k) (ha : a ≠ 0) (i : σ) :
    affineAll (σ := σ) a b ha (X i) = C a * X i + C b := by
  change (aeval fun j => C a * X j + C b) (X i) = _
  exact aeval_X _ _


-- @@ L47-49 verbatim
@[simp] theorem affineAll_C (a b : k) (ha : a ≠ 0) (c : k) :
    affineAll (σ := σ) a b ha (C c) = C c := by
  exact (affineAll (σ := σ) a b ha).commutes c


-- @@ L51-55 verbatim
/-- Its inverse removes the scalar and translate from every variable. -/
@[simp] theorem affineAll_symm_X (a b : k) (ha : a ≠ 0) (i : σ) :
    (affineAll (σ := σ) a b ha).symm (X i) = C a⁻¹ * (X i - C b) := by
  change (aeval fun j => C a⁻¹ * (X j - C b)) (X i) = _
  exact aeval_X _ _


-- @@ L57-66 verbatim
/-- An ambient algebra automorphism taking a polynomial to an affine-linear
    coordinate can be normalized to take it to that variable exactly. -/
theorem exists_equiv_eq_X_of_affine
    (p : MvPolynomial σ k) (i : σ) (a b : k) (ha : a ≠ 0)
    (φ : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (hφ : φ p = C a * X i + C b) :
    ∃ ψ : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k, ψ p = X i := by
  refine ⟨φ.trans (affineAll (σ := σ) a b ha).symm, ?_⟩
  change (affineAll (σ := σ) a b ha).symm (φ p) = X i
  rw [hφ, ← affineAll_X a b ha i, AlgEquiv.symm_apply_apply]


-- @@ L68-78 verbatim
/-- The normalization needed after identifying the generators of two
    principal hypersurface ideals. -/
theorem exists_equiv_eq_X_of_sub_eq_scalar_mul
    (p : MvPolynomial σ k) (i : σ) (t a : k) (ha : a ≠ 0)
    (φ : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k)
    (hφ : φ (p - C t) = C a * X i) :
    ∃ ψ : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k, ψ p = X i := by
  apply exists_equiv_eq_X_of_affine p i a t ha φ
  have hc : φ (C t) = C t := φ.commutes t
  rw [map_sub, hc] at hφ
  exact sub_eq_iff_eq_add.mp hφ


-- @@ L80-80 verbatim
end Generic


-- @@ L82-88 verbatim
/-- Specialized normalization for the exact `IsCoordinate` definition. -/
theorem isCoordinate_of_equiv_sub_eq_scalar_mul_X
    {n : ℕ} (hn : 0 < n) (p : R n) (t a : ℂ) (ha : a ≠ 0)
    (φ : R n ≃ₐ[ℂ] R n)
    (hφ : φ (p - C t) = C a * X ⟨0, hn⟩) :
    IsCoordinate hn p :=
  exists_equiv_eq_X_of_sub_eq_scalar_mul p ⟨0, hn⟩ t a ha φ hφ


-- @@ L90-101 verbatim
/-- A constant translate does not alter whether a polynomial is a coordinate. -/
theorem isCoordinate_sub_C_iff {n : ℕ} (hn : 0 < n) (p : R n) (t : ℂ) :
    IsCoordinate hn (p - C t) ↔ IsCoordinate hn p := by
  constructor
  · rintro ⟨φ, hφ⟩
    apply isCoordinate_of_equiv_sub_eq_scalar_mul_X hn p t 1 one_ne_zero φ
    simpa using hφ
  · rintro ⟨φ, hφ⟩
    apply exists_equiv_eq_X_of_affine (p - C t) ⟨0, hn⟩ 1 (-t) one_ne_zero φ
    rw [map_sub, hφ]
    have hc : φ (C t) = C t := φ.commutes t
    rw [hc, C_1, one_mul, C_neg, sub_eq_add_neg]


-- @@ L103-103 verbatim
end StableCoordinate


-- @@ L105-105 verbatim
end OAI
