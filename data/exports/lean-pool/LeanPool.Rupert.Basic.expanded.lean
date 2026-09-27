/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2


-- @@ L10-14 verbatim
/-!
# LeanPool.Rupert.Basic

Imported Lean Pool material for `LeanPool.Rupert.Basic`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open scoped Matrix


-- @@ L20-21 verbatim
/-- Three-dimensional Euclidean space over `ℝ`. -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

-- @@ L22-23 verbatim
/-- Two-dimensional Euclidean space over `ℝ`. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)


-- @@ L25-26 verbatim
/-- `n`-dimensional Euclidean space over `ℝ`, indexed by `Fin n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)


-- @@ L28-29 verbatim
/-- The special orthogonal group in dimension three over `ℝ`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ


-- @@ L31-33 verbatim
/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def projXy {k : Type} (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  !₂[v 0, v 1]


-- @@ L35-41 expanded
/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupert {ι : Type} (vertices : ι → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ innerRotation ∈ SO3,
    ∃ innerOffset : EuclideanSpace ℝ (Fin 2),
      ∃ outerRotation ∈ SO3,
        let hull := convexHull ℝ {vertices i | i}
        let inner_shadow := {innerOffset + projXy (innerRotation.toEuclideanLin p) | p ∈ hull}
        let outerShadow := {projXy (outerRotation.toEuclideanLin p) | p ∈ hull}
        inner_shadow ⊆ interior outerShadow


-- @@ L43-49 expanded
/-- Alternate formulation of the Rupert Property. This is equivalent to IsRupert and
    should be easier to prove. -/
def IsRupert' {ι : Type} (vertices : ι → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ innerRotation ∈ SO3,
    ∃ innerOffset : EuclideanSpace ℝ (Fin 2),
      ∃ outerRotation ∈ SO3,
        let inner_shadow := {innerOffset + projXy (innerRotation.toEuclideanLin (vertices i)) | i}
        let outerShadow := {projXy (outerRotation.toEuclideanLin (vertices i)) | i}
        inner_shadow ⊆ interior (convexHull ℝ outerShadow)

