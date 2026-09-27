/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import LeanPool.Rupert.Basic


-- @@ L10-14 verbatim
/-!
# LeanPool.Rupert.Set

Imported Lean Pool material for `LeanPool.Rupert.Set`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open scoped Matrix


-- @@ L20-30 expanded
/-- The Rupert Property for a pair of subsets X, Y of ℝ³. X has the
    Rupert property with respect to Y if there such that the shadow of
    X fits "comfortably" within the shadow of Y under affine
    transformations. By "comfortably" we mean the closure of one set is
    a subset of the interior of the other. This definition rules out
    trivial cases of a set fitting inside itself. -/
def IsRupertPair (inner outer : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ innerRot ∈ SO3,
    ∃ innerOffset : EuclideanSpace ℝ (Fin 2),
      ∃ outerRot ∈ SO3,
        let inner_shadow := {innerOffset + projXy (innerRot.toEuclideanLin p) | p ∈ inner}
        let outerShadow := {projXy (outerRot.toEuclideanLin p) | p ∈ outer}
        closure inner_shadow ⊆ interior outerShadow


-- @@ L32-35 expanded
/-- The Rupert Property for a subset S of ℝ³. S has the Rupert property if there
    are rotations and translations such that one 2-dimensional "shadow" of S can
    be made to fit entirely inside the interior of another such "shadow". -/
def IsRupertSet (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsRupertPair S S

