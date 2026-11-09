/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring


-- @@ L10-20 verbatim
/-!
# Short Weierstrass model for Lutz-Nagell

This file sets up the short Weierstrass curve

`y^2 = x^3 + A*x + B`

over `ℤ` and its base change to `ℚ`, and proves basic rewriting lemmas (equation, discriminant).

Downstream Lutz-Nagell files should import this file instead of re-expanding `Δ`/`Equation`.
-/


-- @@ L22-22 verbatim
open scoped Polynomial.Bivariate


-- @@ L24-24 verbatim
namespace LutzNagell

-- @@ L25-25 verbatim
namespace LutzNagellTheorem


-- @@ L27-27 verbatim
open WeierstrassCurve


-- @@ L29-31 verbatim
/-- The short Weierstrass curve over `ℤ`: `y^2 = x^3 + A*x + B`. -/
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }


-- @@ L33-35 verbatim
/-- The short Weierstrass curve over `ℚ`, obtained from `shortCurveZ` by base change. -/
def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ :=
  (shortCurveZ A B).map (algebraMap ℤ ℚ)


-- @@ L37-37 verbatim
@[simp] lemma shortCurveZ_a₁ (A B : ℤ) : (shortCurveZ A B).a₁ = 0 := rfl

-- @@ L38-38 verbatim
@[simp] lemma shortCurveZ_a₂ (A B : ℤ) : (shortCurveZ A B).a₂ = 0 := rfl

-- @@ L39-39 verbatim
@[simp] lemma shortCurveZ_a₃ (A B : ℤ) : (shortCurveZ A B).a₃ = 0 := rfl

-- @@ L40-40 verbatim
@[simp] lemma shortCurveZ_a₄ (A B : ℤ) : (shortCurveZ A B).a₄ = A := rfl

-- @@ L41-41 verbatim
@[simp] lemma shortCurveZ_a₆ (A B : ℤ) : (shortCurveZ A B).a₆ = B := rfl


-- @@ L43-44 verbatim
@[simp] lemma shortCurveQ_a₁ (A B : ℤ) : (shortCurveQ A B).a₁ = 0 := by
  simp [shortCurveQ, shortCurveZ]


-- @@ L46-47 verbatim
@[simp] lemma shortCurveQ_a₂ (A B : ℤ) : (shortCurveQ A B).a₂ = 0 := by
  simp [shortCurveQ, shortCurveZ]


-- @@ L49-50 verbatim
@[simp] lemma shortCurveQ_a₃ (A B : ℤ) : (shortCurveQ A B).a₃ = 0 := by
  simp [shortCurveQ, shortCurveZ]


-- @@ L52-53 verbatim
@[simp] lemma shortCurveQ_a₄ (A B : ℤ) : (shortCurveQ A B).a₄ = (A : ℚ) := by
  simp [shortCurveQ, shortCurveZ]


-- @@ L55-56 verbatim
@[simp] lemma shortCurveQ_a₆ (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ) := by
  simp [shortCurveQ, shortCurveZ]


-- @@ L58-61 verbatim
lemma shortCurveQ_equation_iff (A B : ℤ) (x y : ℚ) :
    (shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ) := by
  simpa [shortCurveQ, shortCurveZ, add_assoc, add_comm, add_left_comm, mul_assoc]
    using (WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y)


-- @@ L63-67 verbatim
lemma shortCurveZ_delta (A B : ℤ) :
    (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, shortCurveZ]
  ring1


-- @@ L69-69 verbatim
end LutzNagellTheorem

-- @@ L70-70 verbatim
end LutzNagell
