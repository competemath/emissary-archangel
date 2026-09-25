/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Kevin Buzzard, Matthew Jasper
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology


-- @@ L10-14 verbatim
/-!
# Valuation Topology

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
variable {F : Type*} [Field F]


-- @@ L20-25 verbatim
@[simp]
lemma Valued.isUnit_valuationSubring_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued F Γ₀] {x : Valued.v.valuationSubring} :
    IsUnit x ↔ Valued.v (x.val : F) = 1 := by
  convert! Valuation.Integers.isUnit_iff_valuation_eq_one _
  exact Valuation.integer.integers _
