/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup


-- @@ L9-13 verbatim
/-!
# Unitarity of permutation matrices

This file records that a complex permutation matrix belongs to the unitary group.
-/


-- @@ L15-15 verbatim
open scoped Matrix


-- @@ L17-17 verbatim
namespace Equiv.Perm


-- @@ L19-25 verbatim
/-- A complex permutation matrix is unitary. -/
theorem permMatrix_mem_unitaryGroup {n : Type*} [DecidableEq n] [Fintype n]
    (σ : Equiv.Perm n) :
    permMatrix ℂ σ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp


-- @@ L27-27 verbatim
end Equiv.Perm
