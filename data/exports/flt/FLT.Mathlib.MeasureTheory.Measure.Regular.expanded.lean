/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Measure.Typeclasses.Finite


-- @@ L11-15 verbatim
/-!
# Regular

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
section IsOpenEmbeddingComap


-- @@ L21-21 verbatim
open MeasureTheory Measure


-- @@ L23-26 verbatim
variable {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y}


-- @@ L28-28 verbatim
namespace Topology.IsOpenEmbedding


-- @@ L30-40 verbatim
lemma outerRegular_comap
    (hφ : IsOpenEmbedding φ) (μ : Measure Y) [OuterRegular μ] :
    OuterRegular (comap φ μ) where
  outerRegular A hA r hr := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ :=
      OuterRegular.outerRegular (hφ.measurableEmbedding.measurableSet_image' hA) r hr
    use φ ⁻¹' U
    refine ⟨Set.image_subset_iff.mp hUA, Uopen.preimage hφ.continuous, ?_⟩
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    apply lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) hμU


-- @@ L42-53 verbatim
lemma innerRegularWRT_comap
    (hφ : IsOpenEmbedding φ) {μ : Measure Y} (hμ : InnerRegularWRT μ IsCompact IsOpen) :
    InnerRegularWRT (comap φ μ) IsCompact IsOpen := by
  intro A hA r hr
  rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding] at hr
  obtain ⟨K, hKA, Kcompact, hμK⟩ := hμ (hφ.isOpen_iff_image_isOpen.mp hA) r hr
  have hK := subset_trans hKA (Set.image_subset_range _ _)
  use φ ⁻¹' K
  refine ⟨?_, hφ.isInducing.isCompact_preimage' Kcompact hK, ?_⟩
  · rw [← hφ.injective.preimage_image A]; exact Set.preimage_mono hKA
  · rwa [MeasurableEmbedding.comap_apply hφ.measurableEmbedding,
      Set.image_preimage_eq_iff.mpr hK]



-- @@ L56-61 verbatim
lemma regular_comap
    (φ : X → Y) (hφ : IsOpenEmbedding φ) (μ : Measure Y) [Regular μ] :
    Regular (comap φ μ) where
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  outerRegular := (hφ.outerRegular_comap μ).outerRegular
  innerRegular := hφ.innerRegularWRT_comap Regular.innerRegular


-- @@ L63-63 verbatim
end Topology.IsOpenEmbedding


-- @@ L65-65 verbatim
end IsOpenEmbeddingComap
