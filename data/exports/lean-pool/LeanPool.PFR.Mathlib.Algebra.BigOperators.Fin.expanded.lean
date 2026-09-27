/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin


-- @@ L14-16 verbatim
/-!
# Finite sums indexed by `Fin`
-/


-- @@ L18-18 verbatim
open Finset


-- @@ L20-22 verbatim
variable {M : Type*} [AddCommMonoid M] {n : ℕ}

-- TODO: Rename `Fin.sum_univ_castSucc` to `Fin.sum_univ_eq_castSucc`

-- @@ L23-29 verbatim
public
lemma Fin.sum_univ_castSucc' (f : Fin (n + 1) → M) :
    ∑ i : Fin n, f i.castSucc = ∑ i ∈ .Iio (.last _), f i := by
  convert (sum_image (castSucc_injective _).injOn).symm
  refine coe_injective ?_
  ext
  simp [← Fin.lt_last_iff_ne_last, ← Fin.val_fin_lt]
