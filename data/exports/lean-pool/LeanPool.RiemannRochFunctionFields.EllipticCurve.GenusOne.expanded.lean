/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.WeilDifferential.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import LeanPool.RiemannRochFunctionFields.EllipticCurve.GenusCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L13-18 verbatim
/-!
# Genus one for elliptic function fields
Shows `g(K) = 1` for a fraction field `K` of an elliptic coordinate ring by counting the
Weierstrass monomials in `L(n·∞)`.  The zero canonical divisor is then obtained by moving an
arbitrary canonical divisor with its unique nonzero Riemann–Roch section.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open FunctionField

-- @@ L23-23 verbatim
open FunctionField.Chart


-- @@ L25-25 verbatim
open scoped Polynomial RatFunc


-- @@ L27-27 verbatim
namespace WeierstrassCurve.Affine.Chart


-- @@ L29-29 verbatim
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]


-- @@ L31-31 verbatim
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]


-- @@ L33-36 verbatim
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]


-- @@ L38-38 verbatim
include W


-- @@ L40-43 verbatim
/-- The divisor of the invariant differential is zero (canonical class is trivial). -/
theorem divOmega_invariant_differential :
    IsCanonical k K (0 : DivisorA k K) := by
  exact zero_isCanonical_of_genus_eq_one K (genus_eq_one_counting W K)


-- @@ L45-47 verbatim
/-- **M7b**: the genus of an elliptic function field is `1`. -/
theorem genus_eq_one : genus k K = 1 := by
  exact genus_eq_one_counting W K


-- @@ L49-49 verbatim
end WeierstrassCurve.Affine.Chart
