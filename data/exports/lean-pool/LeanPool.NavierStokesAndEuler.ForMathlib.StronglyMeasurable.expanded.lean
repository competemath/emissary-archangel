/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable


-- @@ L11-11 verbatim
/-! Strong measurability using second countability of the source. -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open MeasureTheory TopologicalSpace


-- @@ L17-24 verbatim
/-- A continuous map on a second-countable source is almost everywhere strongly measurable.
Specifying the source avoids a search for second countability of the codomain. -/
theorem Continuous.aestronglyMeasurable_of_secondCountable
    {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    {μ : Measure α} {f : α → β} (hf : Continuous f) : AEStronglyMeasurable f μ := by
  let _ := secondCountableTopologyEither_of_left α β
  exact hf.aestronglyMeasurable
