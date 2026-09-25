/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth

-- @@ L9-16 verbatim
/-!

# Functions of temperate growth

This file is intended to collect useful general properties of `HasTemperateGrowth` which are not
(yet) in Mathlib.

-/

-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Function.HasTemperateGrowth


-- @@ L21-21 verbatim
open Finset


-- @@ L23-33 verbatim
/-- The finite product of functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
lemma prod {ι : Type*} {s : Finset ι} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedCommRing F] [NormedAlgebra ℝ F] {f : ι → E → F}
    (hf : ∀ i ∈ s, HasTemperateGrowth (f i)) : HasTemperateGrowth (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact const _
  | insert j t hjt ih =>
    simp_rw [insert_eq, prod_union (disjoint_singleton_left.mpr hjt), prod_singleton]
    exact fun_mul (hf j <| mem_insert_self j t) (ih fun i h ↦ hf i <| mem_insert_of_mem h)


-- @@ L35-35 verbatim
end Function.HasTemperateGrowth
