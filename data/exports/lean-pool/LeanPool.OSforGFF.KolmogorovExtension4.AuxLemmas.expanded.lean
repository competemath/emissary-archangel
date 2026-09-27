/-
Copyright (c) 2026 Rémy Degenne, Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.SetAccumulate
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


-- @@ L15-18 verbatim
/-!

THIS FILE IS NOT USED FOR THE MAIN RESULT
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open Finset Set Filter


-- @@ L24-24 verbatim
open scoped ENNReal NNReal Topology


-- @@ L26-26 verbatim
section Accumulate


-- @@ L28-28 verbatim
variable {α : Type*}


-- @@ L30-32 verbatim
theorem MeasurableSet.accumulate {_ : MeasurableSpace α} {s : ℕ → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (n : ℕ) : MeasurableSet (Set.accumulate s n) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦ hs n


-- @@ L34-34 verbatim
end Accumulate
