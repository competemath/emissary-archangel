/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar


-- @@ L13-15 verbatim
/-!
# Pointwise set operations
-/


-- @@ L17-17 verbatim
open scoped Pointwise


-- @@ L19-19 verbatim
namespace Set

-- @@ L20-20 verbatim
variable {α : Type*}


-- @@ L22-22 verbatim
section Mul

-- @@ L23-23 verbatim
variable [Mul α]


-- @@ L25-27 verbatim
@[to_additive]
public
lemma singleton_mul' (a : α) (s : Set α) : {a} * s = a • s := singleton_mul




-- @@ L31-31 verbatim
end Mul

-- @@ L32-32 verbatim
end Set
