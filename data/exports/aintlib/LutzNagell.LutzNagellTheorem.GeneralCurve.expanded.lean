import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring


-- @@ L5-12 verbatim
/-!
# General Weierstrass model for the generalized Lutz-Nagell theorem

This file sets up a general Weierstrass curve `W : WeierstrassCurve ℤ` and its base change to `ℚ`,
along with basic rewriting lemmas (equation, coefficients).

Downstream generalized Lutz-Nagell files import this file instead of `ShortWeierstrass.lean`.
-/


-- @@ L14-14 verbatim
open scoped Polynomial.Bivariate


-- @@ L16-16 verbatim
namespace LutzNagell

-- @@ L17-17 verbatim
namespace LutzNagellTheorem


-- @@ L19-19 verbatim
open WeierstrassCurve


-- @@ L21-21 verbatim
variable (W : WeierstrassCurve ℤ)


-- @@ L23-25 verbatim
/-- The base change of `W` to `ℚ`. -/
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)


-- @@ L27-27 verbatim
@[simp] lemma curveQ_a₁ : (curveQ W).a₁ = (W.a₁ : ℚ) := by simp [curveQ]

-- @@ L28-28 verbatim
@[simp] lemma curveQ_a₂ : (curveQ W).a₂ = (W.a₂ : ℚ) := by simp [curveQ]

-- @@ L29-29 verbatim
@[simp] lemma curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ) := by simp [curveQ]

-- @@ L30-30 verbatim
@[simp] lemma curveQ_a₄ : (curveQ W).a₄ = (W.a₄ : ℚ) := by simp [curveQ]

-- @@ L31-31 verbatim
@[simp] lemma curveQ_a₆ : (curveQ W).a₆ = (W.a₆ : ℚ) := by simp [curveQ]


-- @@ L33-38 verbatim
lemma curveQ_equation_iff (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveQ]


-- @@ L40-40 verbatim
end LutzNagellTheorem

-- @@ L41-41 verbatim
end LutzNagell
