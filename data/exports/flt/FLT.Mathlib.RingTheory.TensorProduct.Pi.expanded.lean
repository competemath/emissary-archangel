/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi


-- @@ L10-14 verbatim
/-!
# Pi

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-23 verbatim
theorem Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap (R S N ι : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring N] [Algebra R N] [Algebra S N]
    [IsScalarTower R S N] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (TensorProduct.piScalarRight R S N ι).symm (fun i => algebraMap _ _ (x i)) =
      1 ⊗ₜ[R] (∑ i, Pi.single i (x i)) := by
  simp [LinearEquiv.symm_apply_eq, algebraMap_eq_smul_one]
