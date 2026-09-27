/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic


-- @@ L10-14 verbatim
/-!
# Two-sided ideal compatibility helpers

This file restores upstream scalar-action helpers for two-sided ideals.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace TwoSidedIdeal


-- @@ L20-20 verbatim
variable {R : Type*}


-- @@ L22-22 verbatim
section NonUnitalNonAssocRing


-- @@ L24-24 verbatim
variable [NonUnitalNonAssocRing R] {I : TwoSidedIdeal R} {x : R}


-- @@ L26-27 verbatim
lemma smul_mem (r : R) (hx : x ∈ I) : r • x ∈ I := by
  exact I.mul_mem_left r x hx


-- @@ L29-29 verbatim
end NonUnitalNonAssocRing


-- @@ L31-31 verbatim
section Ring


-- @@ L33-33 verbatim
variable [Ring R] {I : TwoSidedIdeal R}


-- @@ L35-42 verbatim
instance instModuleMulOppositeSubtypeMemLeanPool : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul _ := Subtype.ext <| mul_one _
  mul_smul _ _ _ := Subtype.ext <| (mul_assoc _ _ _).symm
  smul_zero _ := Subtype.ext <| zero_mul _
  zero_smul _ := Subtype.ext <| mul_zero _
  add_smul _ _ _ := Subtype.ext <| mul_add _ _ _
  smul_add _ _ _ := Subtype.ext <| add_mul _ _ _


-- @@ L44-44 verbatim
end Ring


-- @@ L46-46 verbatim
end TwoSidedIdeal
