/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `IdealSheafPowerSubscheme.lean` in
Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion


-- @@ L12-17 verbatim
/-!
# Positive powers and their closed subschemes

This file records the affine kernel and underlying closed set of the
subscheme defined by a positive power of an ideal sheaf.
-/


-- @@ L19-19 verbatim
open TopologicalSpace


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
namespace AlgebraicGeometry.Scheme.IdealSheafData


-- @@ L27-27 verbatim
variable {X : Scheme.{u}} (J : X.IdealSheafData)


-- @@ L29-34 verbatim
/-- On an affine open, a positive-power subscheme has the expected kernel. -/
@[simp]
theorem ker_positivePower_subschemeι_app (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((J ^ (n + 1)).subschemeι.app U).hom =
      (J.ideal U) ^ (n + 1) := by
  simpa using (J ^ (n + 1)).ker_subschemeι_app U


-- @@ L36-41 verbatim
/-- Passing to a positive power does not change the underlying closed subset. -/
@[simp]
theorem range_positivePower_subschemeι (n : ℕ) :
    Set.range (J ^ (n + 1)).subschemeι = J.support := by
  rw [(J ^ (n + 1)).range_subschemeι]
  exact congrArg (fun Z : Closeds X ↦ (Z : Set X)) (J.support_pow_succ n)


-- @@ L43-46 verbatim
/-- The subscheme inclusion associated to a positive power is a closed immersion. -/
theorem isClosedImmersion_positivePower_subschemeι (n : ℕ) :
    IsClosedImmersion (J ^ (n + 1)).subschemeι :=
  inferInstance


-- @@ L48-48 verbatim
end AlgebraicGeometry.Scheme.IdealSheafData
