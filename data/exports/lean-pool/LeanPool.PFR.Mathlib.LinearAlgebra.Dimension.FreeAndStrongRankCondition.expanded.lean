/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition


-- @@ L12-14 verbatim
/-!
# Cardinality bounds for finite-dimensional modules
-/


-- @@ L16-16 verbatim
open Cardinal Module Module Set Submodule


-- @@ L18-18 verbatim
universe u v


-- @@ L20-21 verbatim
variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K]
  [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]


-- @@ L23-29 verbatim
variable (K V) in
public
theorem cardinal_le_aleph0_of_finiteDimensional [h : Countable K] :
    #V ≤ ℵ₀ := by
  rw [← lift_le_aleph0.{v, u}, lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  apply power_le_aleph0 (lift_le_aleph0.mpr (mk_le_aleph0_iff.mpr h))
    (lift_lt_aleph0.mpr (rank_lt_aleph0 K V))


-- @@ L31-35 verbatim
variable (K V) in
public
theorem countable_of_finiteDimensional [h : Countable K] : Countable V := by
  have : #V ≤ ℵ₀ := cardinal_le_aleph0_of_finiteDimensional K V
  exact mk_le_aleph0_iff.mp this
