/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


-- @@ L10-14 verbatim
/-!
# Finite

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
section IsOpenEmbeddingComap


-- @@ L20-20 verbatim
open MeasureTheory Measure


-- @@ L22-29 verbatim
lemma Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (comap φ μ) where
  lt_top_of_isCompact K hK := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image hφ.continuous)


-- @@ L31-31 verbatim
end IsOpenEmbeddingComap
