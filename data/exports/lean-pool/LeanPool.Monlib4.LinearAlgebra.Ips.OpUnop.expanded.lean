/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Lemmas


-- @@ L10-20 verbatim
/-!

# The multiplicative opposite linear equivalence

This file defines the multiplicative opposite linear equivalence as linear maps
`op` and `unop`.

We also define `ten_swap`, the linear automorphism on `A ⊗[R] Aᵐᵒᵖ` that
swaps the tensor factors while keeping the `ᵒᵖ` in place.

-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
variable {R A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A]


-- @@ L27-29 verbatim
/-- The linear equivalence sending a vector to its multiplicative opposite. -/
abbrev op (R : Type*) {A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A] :=
(MulOpposite.opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ)


-- @@ L31-33 verbatim
@[simp]
theorem op_apply (x : A) : op R x = MulOpposite.op x :=
  rfl


-- @@ L35-38 verbatim
/-- The inverse linear equivalence from the multiplicative opposite. -/
abbrev unop (R : Type*) {A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A] :
  Aᵐᵒᵖ ≃ₗ[R] A :=
(op R).symm


-- @@ L40-42 verbatim
@[simp]
theorem unop_apply (x : Aᵐᵒᵖ) : unop R x = MulOpposite.unop x :=
  rfl


-- @@ L44-46 verbatim
@[simp]
theorem unop_op (x : A) : unop R (op R x) = x :=
  rfl


-- @@ L48-50 verbatim
@[simp]
theorem op_unop (x : Aᵐᵒᵖ) : op R (unop R x) = x :=
  rfl


-- @@ L52-53 verbatim
theorem unop_comp_op : (unop R).toLinearMap ∘ₗ (op R).toLinearMap = (1 : A →ₗ[R] A) :=
  rfl


-- @@ L55-56 verbatim
theorem op_comp_unop : (op R).toLinearMap ∘ₗ (unop R).toLinearMap = (1 : Aᵐᵒᵖ →ₗ[R] Aᵐᵒᵖ) :=
  rfl


-- @@ L58-60 verbatim
theorem op_star_apply [Star A] (a : A) :
    op R (star a) = star (op R a) :=
  rfl


-- @@ L62-64 verbatim
theorem unop_star_apply [Star A] (a : Aᵐᵒᵖ) :
    unop R (star a) = star (unop R a) :=
  rfl


-- @@ L66-66 verbatim
open scoped TensorProduct


-- @@ L68-68 verbatim
variable {B : Type*} [AddCommMonoid B] [Module R B]

-- @@ L69-75 verbatim
/-- Swap tensor factors while moving the multiplicative-opposite marker to the other factor. -/
noncomputable abbrev tenSwap (R : Type*)
  {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
  [CommSemiring R] [Module R A] [Module R B] :
    A ⊗[R] Bᵐᵒᵖ ≃ₗ[R] B ⊗[R] Aᵐᵒᵖ :=
(TensorProduct.comm R A Bᵐᵒᵖ).trans
  (LinearEquiv.TensorProduct.map (unop R) (op R))


-- @@ L77-79 verbatim
theorem tenSwap_apply (x : A) (y : Bᵐᵒᵖ) :
    tenSwap R (x ⊗ₜ[R] y) = MulOpposite.unop y ⊗ₜ[R] MulOpposite.op x :=
  rfl


-- @@ L81-83 verbatim
theorem tenSwap_apply' (x : A) (y : B) :
    tenSwap R (x ⊗ₜ MulOpposite.op y) = y ⊗ₜ[R] MulOpposite.op x :=
  rfl


-- @@ L85-89 verbatim
theorem tenSwap_symm :
  (tenSwap R).symm = (tenSwap R : B ⊗[R] Aᵐᵒᵖ ≃ₗ[R] A ⊗[R] Bᵐᵒᵖ) := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  simp_all


-- @@ L91-95 verbatim
theorem tenSwap_comp_tenSwap :
    (tenSwap R).toLinearMap ∘ₗ (tenSwap R).toLinearMap =
      (1 : A ⊗[R] Bᵐᵒᵖ →ₗ[R] A ⊗[R] Bᵐᵒᵖ) := by
  apply TensorProduct.ext'
  simp_all


-- @@ L97-100 verbatim
theorem tenSwap_apply_tenSwap (x : A ⊗[R] Bᵐᵒᵖ) :
    tenSwap R (tenSwap R x) = x := by
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
    tenSwap_comp_tenSwap]; rfl
