/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import LeanPool.Rupert.Basic
import LeanPool.Rupert.Affine
import LeanPool.Rupert.Set
import Mathlib.Algebra.Order.Archimedean.Real.Hom


-- @@ L13-17 verbatim
/-!
# LeanPool.Rupert.Equivalences.Util

Imported Lean Pool material for `LeanPool.Rupert.Equivalences.Util`.
-/


-- @@ L19-19 verbatim
@[expose] public section

-- @@ L20-20 verbatim
open Pointwise

-- @@ L21-21 verbatim
open Matrix


-- @@ L23-34 expanded
/-- Projecting from ℝ³ to ℝ² is linear -/
noncomputable def projXyLinear : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  { toFun := projXy, map_add' := by intro x y; ext i; fin_cases i <;> simp [projXy],
    map_smul' := by intro x y; ext i; fin_cases i <;> simp [projXy] }


-- @@ L36-38 expanded
/-- Rotation by an element of `SO3`, viewed as an affine map. -/
noncomputable def rotationAffine (rot : SO3) :
    EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (Matrix.toEuclideanLin rot).toAffineMap


-- @@ L40-43 expanded
/-- Translating is affine. -/
noncomputable def offsetAffine (off : E 2) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  { toFun v := off + v, linear := LinearMap.id, map_vadd' p v := add_vadd_comm v off p }


-- @@ L45-48 expanded
/-- Projection of a rotated point onto the xy-plane, as an affine map. -/
noncomputable def projXyRotationIsAffine (rot : SO3) :
    EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  AffineMap.comp projXyLinear.toAffineMap (rotationAffine rot)


-- @@ L50-53 expanded
/-- Full affine transform used for projected Rupert shadows. -/
noncomputable def fullTransformAffine (off : E 2) (rot : SO3) :
    EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  AffineMap.comp (offsetAffine off) (projXyRotationIsAffine rot)


-- @@ L55-57 verbatim
proof_wanted affine_rupert_iff_rupert_set
    (X : Set (EuclideanSpace ℝ (Fin 3))) :
    IsAffineRupertSet X ↔ IsRupertSet X
