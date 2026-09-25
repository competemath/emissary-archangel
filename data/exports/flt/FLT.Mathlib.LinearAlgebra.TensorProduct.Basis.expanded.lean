/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.DirectSum.Finsupp


-- @@ L12-16 verbatim
/-!
# Basis

Material destined for Mathlib.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open scoped TensorProduct


-- @@ L22-31 verbatim
/-- If A is a nontrivial free R-module and B is a nontrivial R-module then A ⊗[R] B is
  also nontrivial. -/
instance (R : Type*) [CommSemiring R] (A B : Type*) [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [Module.Free R A] [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[R] B) := by
  -- A ⊗[R] B ≃ (ι →₀ R) ⊗[R] B
  suffices Nontrivial ((Module.Free.ChooseBasisIndex R A →₀ R) ⊗[R] B) by
    apply (LinearEquiv.rTensor B (Module.Free.chooseBasis R A).repr).toEquiv.nontrivial
  -- ≃ ι →₀ B which is nontrivial
  apply (TensorProduct.finsuppScalarLeft R B (Module.Free.ChooseBasisIndex R A)).toEquiv.nontrivial


-- @@ L33-43 verbatim
/-- If A is a nontrivial R-module and B is a nontrivial free R-module then A ⊗[R] B is
  also nontrivial. -/
instance (R : Type*) [CommSemiring R] (A B : Type*) [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [Module.Free R B] [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[R] B) := by
  -- A ⊗[R] B ≃ A ⊗[R] (ι →₀ R)
  suffices Nontrivial (A ⊗[R] (Module.Free.ChooseBasisIndex R B →₀ R)) by
    apply (LinearEquiv.lTensor A (Module.Free.chooseBasis R B).repr).toEquiv.nontrivial
  -- ≃ ι →₀ A which is nontrivial
  exact (TensorProduct.finsuppScalarRight R R A
    (Module.Free.ChooseBasisIndex R B)).toEquiv.nontrivial
