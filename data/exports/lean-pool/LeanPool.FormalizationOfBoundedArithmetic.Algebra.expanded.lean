/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module


public import LeanPool.FormalizationOfBoundedArithmetic.IDelta0
import Mathlib.Tactic.Positivity.Finset


-- @@ L12-14 verbatim
/-!
# LeanPool.FormalizationOfBoundedArithmetic.Algebra
-/


-- @@ L16-18 verbatim
@[expose] public section

-- INSTANCES!


-- @@ L20-20 verbatim
universe u v


-- @@ L22-22 verbatim
section IOPEN

-- @@ L23-23 verbatim
variable {M : Type u} [iopen : IOPENModel M]


-- @@ L25-25 verbatim
open BASICModel IOPENModel



-- @@ L28-30 verbatim
theorem isAddRightRegular_one : IsAddRightRegular (1 : M) := by
  unfold IsAddRightRegular Function.Injective
  exact B2


-- @@ L32-38 verbatim
instance : IsRightCancelAdd M where
  add_right_cancel := by
    intro a
    unfold IsAddRightRegular Function.Injective
    intro b c
    simp only
    apply add_cancel_right.mp


-- @@ L40-42 verbatim
instance instMulZeroClassLeanPool : MulZeroClass M where
  zero_mul := zero_mul
  mul_zero := by apply B5


-- @@ L44-48 verbatim
instance instCommMonoidLeanPool : CommMonoid M where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm


-- @@ L50-55 verbatim
instance instAddCommMonoidLeanPool : AddCommMonoid M where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := B3
  nsmul := nsmulRec
  add_comm := add_comm


-- @@ L57-64 verbatim
instance instSemiringLeanPool : Semiring M where
  left_distrib := IOPENModel.mul_add
  right_distrib := by
    intro a b c
    rw [<- iopen.mul_comm]
    rw [iopen.mul_add]
    rw [iopen.mul_comm]
    conv => lhs; rhs; rw [iopen.mul_comm]


-- @@ L66-66 verbatim
end IOPEN


-- @@ L68-68 verbatim
section IDelta0


-- @@ L70-70 verbatim
open BASICModel

-- @@ L71-71 verbatim
variable {M : Type u} [idelta0 : IDelta0Model M]


-- @@ L73-76 verbatim
instance : IsOrderedAddMonoid M where
  add_le_add_left := fun _ _ a_1 c ↦ add_le_add_left a_1 c

-- D7 used

-- @@ L77-78 verbatim
instance : IsOrderedMonoid M where
  mul_le_mul_left := fun _ _ h _ ↦ idelta0.le_mul_right h


-- @@ L80-80 verbatim
instance instAddCommMonoidLeanPool' : AddCommMonoid M where



-- @@ L83-91 verbatim
instance : IsOrderedRing M where
  zero_le_one := idelta0.zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a h_zero_a b c hbc
    rw [mul_comm a b, mul_comm a c]
    exact idelta0.le_mul_right hbc
  mul_le_mul_of_nonneg_right := by
    intro c h_zero_c a b hab
    exact idelta0.le_mul_right hab


-- @@ L93-93 verbatim
instance instCommSemiringLeanPool : CommSemiring M where


-- @@ L95-107 verbatim
instance : IsLeftCancelAdd M where
  add_left_cancel x := by
    unfold IsAddLeftRegular
    unfold Function.Injective
    intro a1 a2
    simp only
    intro h
    conv at h =>
      rw [add_comm]
      rhs
      rw [add_comm]
    rw [@IOPENModel.add_cancel_right] at h
    exact h


-- @@ L109-109 verbatim
end IDelta0
