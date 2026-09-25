/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Translations
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

-- @@ L10-14 verbatim
/-!

## Ring surface in `Space 3`

-/

-- @@ L15-15 verbatim
@[expose] public section

-- @@ L16-16 verbatim
open SchwartzMap NNReal

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
open Physlib Distribution

-- @@ L19-20 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L22-22 verbatim
namespace Space


-- @@ L24-24 verbatim
open MeasureTheory Real


-- @@ L26-30 verbatim
/-!

## A. The definition of the ring surface

-/


-- @@ L32-34 verbatim
/-- The embedding of the unit ring (a circle `S¹` in `Space 2`) into `Space 3`. -/
def ring : Metric.sphere (0 : Space 2) 1 → Space 3 := fun x =>
  (slice 2).symm (0, Space.sphericalShell 2 x)


-- @@ L36-36 verbatim
lemma ring_eq : ring = (slice 2).symm ∘ (fun x => (0, sphericalShell 2 x)) := rfl


-- @@ L38-41 verbatim
lemma ring_injective : Function.Injective ring := by
  intro x y h
  simp [ring] at h
  exact sphericalShell_injective _ h


-- @@ L43-47 verbatim
@[fun_prop]
lemma ring_continuous : Continuous ring := by
  apply Continuous.comp
  · fun_prop
  · fun_prop


-- @@ L49-50 verbatim
lemma ring_measurableEmbedding : MeasurableEmbedding ring :=
  Continuous.measurableEmbedding ring_continuous ring_injective



-- @@ L53-57 verbatim
/-!

## B. The measure associated with the ring

-/


-- @@ L59-61 verbatim
/-- The measure on `Space 3` corresponding to integration around a ring. -/
def ringMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map ring (MeasureTheory.Measure.toSphere volume)


-- @@ L63-68 verbatim
instance ringMeasure_hasTemperateGrowth :
    ringMeasure.HasTemperateGrowth := by
  rw [ringMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp


-- @@ L70-72 verbatim
instance ringMeasure_prod_volume_hasTemperateGrowth :
    (ringMeasure.prod (volume (α := Space))).HasTemperateGrowth := by
  exact IsDistBounded.instHasTemperateGrowthProdProdOfOpensMeasurableSpace ringMeasure volume


-- @@ L74-76 verbatim
instance ringMeasure_sFinite: SFinite ringMeasure := by
  rw [ringMeasure]
  exact Measure.instSFiniteMap volume.toSphere ring


-- @@ L78-80 verbatim
instance ringMeasure_finite: IsFiniteMeasure ringMeasure := by
  rw [ringMeasure]
  exact Measure.isFiniteMeasure_map volume.toSphere ring


-- @@ L82-89 verbatim
lemma integrable_ringMeasure_of_continuous (f : Space → ℝ) (hf : Continuous (f ∘ ring)) :
    Integrable f ringMeasure := by
  rw [ringMeasure]
  rw [MeasurableEmbedding.integrable_map_iff]
  · let f' : BoundedContinuousFunction (Metric.sphere (0 : Space 2) 1) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨f ∘ ring, hf⟩
    exact BoundedContinuousFunction.integrable _ f'
  · exact ring_measurableEmbedding


-- @@ L91-98 verbatim
lemma integrable_ringMeasure_of_continuous_euclid (f : Space → EuclideanSpace ℝ (Fin n))
    (hf : Continuous (f ∘ ring)) :
    Integrable f ringMeasure := by
  rw [ringMeasure]
  rw [MeasurableEmbedding.integrable_map_iff]
  · exact BoundedContinuousFunction.integrable _
      (BoundedContinuousFunction.mkOfCompact ⟨f ∘ ring, hf⟩)
  · exact ring_measurableEmbedding


-- @@ L100-108 verbatim
lemma ringMeasure_prod_volume_map :
    (ringMeasure.prod (volume (α := Space))).map (fun x : Space × Space => (x.1, x.2 + x.1))
     = (ringMeasure.prod (volume (α := Space))) := by
  refine (MeasureTheory.MeasurePreserving.skew_product (f := id) (g := fun x => fun y => y + x)
    ?_ ?_ ?_).map_eq
  · exact MeasurePreserving.id ringMeasure
  · fun_prop
  · filter_upwards with x
    exact Measure.IsAddRightInvariant.map_add_right_eq_self (x)


-- @@ L110-116 verbatim
@[simp]
lemma ringMeasure_univ : ringMeasure Set.univ = ENNReal.ofReal ((2 : ℝ) * π) := by
  rw [ringMeasure, Measure.map_apply]
  simp only [Set.preimage_univ, Measure.toSphere_apply_univ, finrank_eq_dim, Nat.cast_ofNat,
    volume_metricBall_two, Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat]
  · fun_prop
  · exact MeasurableSet.univ



-- @@ L119-123 verbatim
/-!

## C. The distribution associated with the ring

-/


-- @@ L125-127 expanded
/-- The distribution on `Space 3` corresponding to integration around a ring. -/
def ringDist : Distribution ℝ (Space 3) ℝ :=
  SchwartzMap.integralCLM ℝ ringMeasure


-- @@ L129-131 verbatim
lemma ringDist_apply_eq_integral_ringMeasure (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ x, f x ∂ringMeasure := by
  rw [ringDist, SchwartzMap.integralCLM_apply]


-- @@ L133-136 verbatim
lemma ringDist_eq_integral_delta (f : 𝓢(Space 3, ℝ)) :
    ringDist f = ∫ z, diracDelta ℝ z f ∂ringMeasure := by
  rw [ringDist_apply_eq_integral_ringMeasure]
  simp


-- @@ L138-138 verbatim
end Space
