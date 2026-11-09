/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PolynomialStandardSmooth
import ModularCurves.Moduli.UniversalLegendre


-- @@ L9-15 verbatim
/-!
# The Legendre moduli scheme is smooth of relative dimension one

`Spec R[λ][(λ(λ−1))⁻¹] ⟶ Spec R` is smooth of relative dimension one: the
λ-line chart of the `Y(ρ̄)` smoothness leaf (T-YR-6 (b1)+(b2a) applied to the
`T-E14` universal Legendre object).
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace ModularCurves


-- @@ L21-21 verbatim
open AlgebraicGeometry Algebra


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
variable (R : CommRingCat.{u})


-- @@ L27-30 verbatim
instance legendreModuliRing_isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (LegendreModuliRing R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.localizationAway_mvPolynomialFinOne
    R (legendrePoly R)


-- @@ L32-36 verbatim
/-- **[T-YR-6 (b1) scheme level]** The universal Legendre object's structure
map is smooth of relative dimension one. -/
theorem universalLegendreObj_structMap_smooth (hR : IsUnit (2 : R)) :
    SmoothOfRelativeDimension 1 (universalLegendreObj R hR).structMap :=
  smoothOfRelativeDimension_spec_map_algebraMap 1


-- @@ L38-38 verbatim
end ModularCurves


-- @@ L40-40 verbatim
end
