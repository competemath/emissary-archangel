/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public meta import Mathlib.Tactic.ToDual
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.SetLike


-- @@ L17-22 verbatim
/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open Function

-- @@ L27-29 verbatim
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?

-- @@ L30-31 verbatim
/-- Notation `[G : H]` for the (additive) index of a subgroup `H ≤ G`. -/
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H


-- @@ L33-38 verbatim
theorem Subgroup.index_op {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective


-- @@ L40-41 verbatim
instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [Subgroup.index_op]; exact Subgroup.FiniteIndex.index_ne_zero⟩
