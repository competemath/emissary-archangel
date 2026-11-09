/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Ring


-- @@ L11-18 verbatim
/-!
# General Weierstrass model over a PID and its fraction field

This file sets up a general Weierstrass curve `W : WeierstrassCurve R` for a PID `R` and its
base change to the fraction field `K`, along with basic rewriting lemmas.

This generalizes `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R` with fraction field `K`.
-/


-- @@ L20-20 verbatim
open scoped Polynomial.Bivariate


-- @@ L22-22 verbatim
namespace LutzNagell

-- @@ L23-23 verbatim
namespace PID


-- @@ L25-25 verbatim
open WeierstrassCurve


-- @@ L27-27 verbatim
variable (R : Type*) [CommRing R]

-- @@ L28-28 verbatim
variable (K : Type*) [Field K] [Algebra R K]

-- @@ L29-29 verbatim
variable (W : WeierstrassCurve R)


-- @@ L31-32 verbatim
/-- The base change of `W` to the fraction field `K`. -/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)


-- @@ L34-34 verbatim
@[simp] lemma curveK_a₁ : (curveK R K W).a₁ = algebraMap R K W.a₁ := by simp [curveK]

-- @@ L35-35 verbatim
@[simp] lemma curveK_a₂ : (curveK R K W).a₂ = algebraMap R K W.a₂ := by simp [curveK]

-- @@ L36-36 verbatim
@[simp] lemma curveK_a₃ : (curveK R K W).a₃ = algebraMap R K W.a₃ := by simp [curveK]

-- @@ L37-37 verbatim
@[simp] lemma curveK_a₄ : (curveK R K W).a₄ = algebraMap R K W.a₄ := by simp [curveK]

-- @@ L38-38 verbatim
@[simp] lemma curveK_a₆ : (curveK R K W).a₆ = algebraMap R K W.a₆ := by simp [curveK]


-- @@ L40-46 verbatim
lemma curveK_equation_iff (x y : K) :
    (curveK R K W).toAffine.Equation x y ↔
      y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x +
        algebraMap R K W.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveK]


-- @@ L48-48 verbatim
end PID

-- @@ L49-49 verbatim
end LutzNagell
