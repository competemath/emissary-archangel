/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
Adapted from the Apache-licensed `SchemeModuleRestrictionIsoMonotone.lean`
in Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict


-- @@ L13-18 verbatim
/-!
# Monotonicity of open-local module isomorphisms

A scheme-module morphism which is invertible on an open remains
invertible after shrinking that open.
-/


-- @@ L20-20 verbatim
open CategoryTheory AlgebraicGeometry


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L28-28 verbatim
variable {X : Scheme.{u}}


-- @@ L30-53 verbatim
/-- An isomorphism after restriction to `V` remains one on `W ≤ V`. -/
theorem isIso_restrict_map_of_le
    {M N : X.Modules} (α : M ⟶ N)
    {W V : X.Opens} (hWV : W ≤ V)
    [IsIso ((restrictFunctor V.ι).map α)] :
    IsIso ((restrictFunctor W.ι).map α) := by
  let j : W.toScheme ⟶ V.toScheme :=
    X.homOfLE hWV
  let e :
      restrictFunctor W.ι ≅
        restrictFunctor V.ι ⋙ restrictFunctor j :=
    restrictFunctorCongr
        (Scheme.homOfLE_ι X hWV).symm ≪≫
      restrictFunctorComp j V.ι
  haveI :
      IsIso
        ((restrictFunctor V.ι ⋙
          restrictFunctor j).map α) := by
    change
      IsIso
        ((restrictFunctor j).map
          ((restrictFunctor V.ι).map α))
    infer_instance
  exact (NatIso.isIso_map_iff e α).mpr inferInstance


-- @@ L55-55 verbatim
end AlgebraicGeometry.Scheme.Modules
