/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `CanonicalSupportThickening.lean` in
Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.FiniteSupportIdealSheafPullbackUnit


-- @@ L11-18 verbatim
/-!
# Canonical closed thickenings of scheme-module support

For a finite-type quasicoherent module on a Noetherian scheme, a positive
power of the vanishing ideal of its closed stalk support annihilates the
module scheme-theoretically. This file packages the resulting closed
thickening and the pullback-pushforward comparison isomorphism.
-/


-- @@ L20-20 verbatim
open CategoryTheory AlgebraicGeometry TopologicalSpace


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L28-36 verbatim
/-- A positive power of the vanishing ideal of `F` whose associated
closed subscheme recovers `F` by pullback followed by pushforward. -/
structure CanonicalSupportThickening {X : Scheme.{u}} (F : X.Modules) where
  exponent : ℕ
  unitIsIso :
    IsIso
      ((pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (exponent + 1)).subschemeι)).unit.app F)


-- @@ L38-38 verbatim
namespace CanonicalSupportThickening


-- @@ L40-40 verbatim
variable {X : Scheme.{u}} {F : X.Modules}


-- @@ L42-45 verbatim
/-- The positive power of the vanishing ideal defining the thickening. -/
def idealSheaf (A : CanonicalSupportThickening F) : X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal (closedStalkSupport F)) ^
    (A.exponent + 1)


-- @@ L47-49 verbatim
/-- The canonical closed support thickening. -/
abbrev supportScheme (A : CanonicalSupportThickening F) : Scheme.{u} :=
  A.idealSheaf.subscheme


-- @@ L51-53 verbatim
/-- The canonical closed immersion of the support thickening. -/
def inclusion (A : CanonicalSupportThickening F) : A.supportScheme ⟶ X :=
  A.idealSheaf.subschemeι


-- @@ L55-57 verbatim
/-- The pullback of the original module to its support thickening. -/
def modelModule (A : CanonicalSupportThickening F) : A.supportScheme.Modules :=
  (pullback A.inclusion).obj F


-- @@ L59-62 verbatim
instance inclusion_isClosedImmersion (A : CanonicalSupportThickening F) :
    IsClosedImmersion A.inclusion := by
  change IsClosedImmersion A.idealSheaf.subschemeι
  infer_instance


-- @@ L64-71 verbatim
instance unit_isIso (A : CanonicalSupportThickening F) :
    IsIso ((pullbackPushforwardAdjunction A.inclusion).unit.app F) := by
  change
    IsIso
      ((pullbackPushforwardAdjunction
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (A.exponent + 1)).subschemeι)).unit.app F)
  exact A.unitIsIso


-- @@ L73-77 verbatim
/-- The original module is the pushforward of its canonical model. -/
def comparisonIso (A : CanonicalSupportThickening F) :
    F ≅ (pushforward A.inclusion).obj A.modelModule := by
  change F ≅ (pushforward A.inclusion).obj ((pullback A.inclusion).obj F)
  exact asIso ((pullbackPushforwardAdjunction A.inclusion).unit.app F)


-- @@ L79-90 verbatim
/-- The range of the support thickening is the closed stalk support of
the original module. -/
theorem range_inclusion (A : CanonicalSupportThickening F) :
    Set.range A.inclusion = (closedStalkSupport F : Set X) := by
  change
    Set.range
        (((Scheme.IdealSheafData.vanishingIdeal
          (closedStalkSupport F)) ^ (A.exponent + 1)).subschemeι) =
      _
  rw [Scheme.IdealSheafData.range_positivePower_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal
    (closedStalkSupport F)


-- @@ L92-107 verbatim
/-- Every finite-type quasicoherent module on a Noetherian scheme admits
its canonical support thickening. -/
theorem nonempty [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    Nonempty (CanonicalSupportThickening F) := by
  obtain ⟨n, hn⟩ :=
    exists_positivePower_isIso_pullbackPushforward_unit F
      (Scheme.IdealSheafData.vanishingIdeal (closedStalkSupport F))
      (by
        intro x hx
        change x ∈
          ((Scheme.IdealSheafData.vanishingIdeal
            (closedStalkSupport F)).support : Set X)
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hx)
  exact ⟨⟨n, hn⟩⟩


-- @@ L109-113 verbatim
/-- A chosen canonical support thickening. -/
def ofFiniteType [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    CanonicalSupportThickening F :=
  Classical.choice (nonempty F)


-- @@ L115-115 verbatim
end CanonicalSupportThickening

-- @@ L116-116 verbatim
end AlgebraicGeometry.Scheme.Modules
