/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Order.Group.Indicator


-- @@ L13-15 verbatim
/-!
# Ordered indicator functions
-/



-- @@ L18-18 verbatim
namespace Set

-- @@ L19-19 verbatim
variable {α M : Type*} [Zero M] [One M]


-- @@ L21-21 verbatim
section Preorder

-- @@ L22-22 verbatim
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}


-- @@ L24-27 verbatim
@[simp]
public
lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  indicator_nonneg (by simp)


-- @@ L29-32 verbatim
@[simp]
public
lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a


-- @@ L34-34 verbatim
end Preorder


-- @@ L36-36 verbatim
section PartialOrder

-- @@ L37-37 verbatim
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}


-- @@ L39-44 verbatim
@[simp]
public
lemma indicator_one_pos : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]


-- @@ L46-46 verbatim
end PartialOrder

-- @@ L47-47 verbatim
end Set
