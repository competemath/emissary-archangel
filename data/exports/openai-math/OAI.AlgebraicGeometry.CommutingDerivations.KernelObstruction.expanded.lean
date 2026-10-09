import OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization
import Mathlib.Algebra.Polynomial.AlgebraMap


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-8 verbatim
/-! Every element of the proposed common kernel has a critical point.
This proves the coordinate obstruction for all such elements, independently
of whether they generate that subalgebra. It does not assert kernel equality. -/

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace AbhyankarSathaye.CommutingDerivations

-- @@ L11-11 verbatim
open MvPolynomial


-- @@ L13-21 verbatim
theorem critical_aeval {σ B : Type*} [CommRing B]
    (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) (i : σ) :
    eval point (pderiv i (Polynomial.aeval f q)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, hq, hr, add_zero]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.aeval_C, MvPolynomial.algebraMap_eq, hc]


-- @@ L23-28 verbatim
theorem no_coordinate_aeval_of_critical {σ B : Type*} [Fintype σ] [CommRing B]
    [Nontrivial B] (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) :
    ¬ ∃ (e : MvPolynomial σ B ≃ₐ[B] MvPolynomial σ B) (i : σ),
      e (X i) = Polynomial.aeval f q :=
  no_coordinate_of_critical _ point (critical_aeval f point hc q)


-- @@ L30-35 verbatim
theorem polynomial_in_extendedF_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (q : Polynomial ℂ) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = Polynomial.aeval (extendedF hn) q :=
  no_coordinate_aeval_of_critical (extendedF hn) (extendedPoint hn)
    (extendedF_critical hn) q


-- @@ L37-45 verbatim
/-- In particular, no generator of a common kernel equal to `C[F_n]` can
be a coordinate. The explicit polynomial-expression hypothesis suffices. -/
theorem element_of_extendedF_subring_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (g : MvPolynomial (Fin n) ℂ)
    (hg : ∃ q : Polynomial ℂ, g = Polynomial.aeval (extendedF hn) q) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = g := by
  obtain ⟨q, rfl⟩ := hg
  exact polynomial_in_extendedF_not_coordinate hn q


-- @@ L47-47 verbatim
end AbhyankarSathaye.CommutingDerivations


-- @@ L49-49 verbatim
end


-- @@ L51-51 verbatim
end OAI
