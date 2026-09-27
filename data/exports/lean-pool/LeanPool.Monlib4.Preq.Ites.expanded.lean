/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map


-- @@ L11-15 verbatim
/-!
 # Some stuff on ites

 Some lemmas about `ite` and `coe` for `star` and `tensor_product`.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-29 verbatim
@[simp]
theorem star_ite {α : Type _} [InvolutiveStar α] (P : Prop) [Decidable P] (a b : α) :
    star (ite P a b) = ite P (star a) (star b) := by
  by_cases h : a = b
  · simp_rw [h, ite_self]
  · have : ¬star a = star b := by
      simp_all
    by_cases h' : P
    · simp_rw [(Ne.ite_eq_left_iff h).mpr h', (Ne.ite_eq_left_iff this).mpr h']
    · simp_rw [(Ne.ite_eq_right_iff h).mpr h', (Ne.ite_eq_right_iff this).mpr h']


-- @@ L31-33 verbatim
theorem coe_ite {α β : Type _} [CoeTC α β] (P : Prop) [Decidable P] (a b : α) :
    (↑(ite P a b) : β) = ite P (a : β) (b : β) :=
by split_ifs <;> rfl


-- @@ L35-40 verbatim
theorem ite_apply_lm {R A B : Type _} [Semiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A]
    [Module R B] (f g : A →ₗ[R] B) (x : A) (P : Prop) [Decidable P] :
    (if P then f else g : A →ₗ[R] B) x = if P then f x else g x := by
  by_cases h : P
  · simp only [h, ite_true]
  · simp only [h, ite_false]


-- @@ L42-42 verbatim
local notation f " ⊗ₘ " g => TensorProduct.map f g


-- @@ L44-44 verbatim
open scoped TensorProduct


-- @@ L46-50 expanded
theorem TensorProduct.ite_map {R M₁ M₂ M₃ M₄ : Type _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [Module R M₁] [Module R M₂]
    [Module R M₃] [Module R M₄] (f₁ f₂ : M₁ →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (P : Prop) [Decidable P] :
    (TensorProduct.map (ite P f₁ f₂) g) =
      (ite P (TensorProduct.map f₁ g) (TensorProduct.map f₂ g) : M₁ ⊗[R] M₃ →ₗ[R] M₂ ⊗[R] M₄) :=
  by split_ifs <;> simp

