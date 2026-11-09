/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import ModularCurves.Vendored.RiemannRoch.EllipticCurve.GenusCounting


-- @@ L10-15 verbatim
/-!
# Genus one for elliptic function fields
Shows `g(K) = 1` for a fraction field `K` of an elliptic coordinate ring by counting the
Weierstrass monomials in `L(n·∞)`.  The zero canonical divisor is then obtained by moving an
arbitrary canonical divisor with its unique nonzero Riemann–Roch section.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open FunctionField

-- @@ L20-20 verbatim
open FunctionField.Chart


-- @@ L22-22 verbatim
open scoped Polynomial RatFunc


-- @@ L24-24 verbatim
namespace WeierstrassCurve.Affine.Chart


-- @@ L26-26 verbatim
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]


-- @@ L28-28 verbatim
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]


-- @@ L30-33 verbatim
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]


-- @@ L35-35 verbatim
include W


-- @@ L37-40 verbatim
/-- The divisor of the invariant differential is zero (canonical class is trivial). -/
theorem divOmega_invariant_differential :
    IsCanonical k K (0 : DivisorA k K) := by
  exact zero_isCanonical_of_genus_eq_one K (genus_eq_one_counting W K)


-- @@ L42-44 verbatim
/-- **M7b**: the genus of an elliptic function field is `1`. -/
theorem genus_eq_one : genus k K = 1 := by
  exact genus_eq_one_counting W K


-- @@ L46-46 verbatim
end WeierstrassCurve.Affine.Chart
