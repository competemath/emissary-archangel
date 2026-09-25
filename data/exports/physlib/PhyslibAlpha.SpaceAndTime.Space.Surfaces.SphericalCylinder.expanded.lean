/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ring
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

-- @@ L11-18 verbatim
/-!

## Spherical cylinder surface in `Space 3`

The spherical cylinder is the unit circular shell in `Space 2` extruded along the
third coordinate.

-/


-- @@ L20-20 verbatim
@[expose] public section

-- @@ L21-21 verbatim
open SchwartzMap NNReal

-- @@ L22-22 verbatim
noncomputable section

-- @@ L23-23 verbatim
open Physlib Distribution

-- @@ L24-25 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L27-27 verbatim
namespace Space


-- @@ L29-29 verbatim
open MeasureTheory Real


-- @@ L31-35 verbatim
/-!

## A. The definition of the spherical cylinder surface

-/


-- @@ L37-39 verbatim
/-- The map embedding the unit circular shell extruded along the axis into `Space 3`. -/
def sphericalCylinder : Metric.sphere (0 : Space 2) 1 × ℝ → Space 3 := fun x =>
  (slice 2).symm (x.2, sphericalShell 2 x.1)


-- @@ L41-42 verbatim
lemma sphericalCylinder_eq :
    sphericalCylinder = (slice 2).symm ∘ (fun x => (x.2, sphericalShell 2 x.1)) := rfl


-- @@ L44-48 verbatim
lemma sphericalCylinder_injective : Function.Injective sphericalCylinder := by
  intro x y h
  have h' := congrArg (slice 2) h
  simp [sphericalCylinder] at h'
  exact Prod.ext (sphericalShell_injective 2 h'.2) h'.1


-- @@ L50-54 verbatim
@[fun_prop]
lemma sphericalCylinder_continuous : Continuous sphericalCylinder := by
  apply Continuous.comp
  · fun_prop
  · fun_prop


-- @@ L56-57 verbatim
lemma sphericalCylinder_measurableEmbedding : MeasurableEmbedding sphericalCylinder :=
  Continuous.measurableEmbedding sphericalCylinder_continuous sphericalCylinder_injective


-- @@ L59-63 verbatim
@[simp]
lemma norm_sphericalCylinder (x : Metric.sphere (0 : Space 2) 1 × ℝ) :
    ‖sphericalCylinder x‖ = √(‖x.2‖ ^ 2 + 1) := by
  rw [sphericalCylinder, norm_slice_symm_eq, norm_sphericalShell]
  norm_num


-- @@ L65-69 verbatim
/-!

## B. The measure associated with the spherical cylinder

-/


-- @@ L71-74 verbatim
/-- The measure on `Space 3` corresponding to integration over a spherical cylinder. -/
def sphericalCylinderMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map sphericalCylinder
    ((MeasureTheory.Measure.toSphere volume).prod (volume (α := ℝ)))


-- @@ L76-98 verbatim
instance sphericalCylinderMeasure_hasTemperateGrowth :
    sphericalCylinderMeasure.HasTemperateGrowth := by
  rw [sphericalCylinderMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := ℝ))
  use n
  rw [MeasurableEmbedding.integrable_map_iff sphericalCylinder_measurableEmbedding]
  change Integrable
    (fun x : Metric.sphere (0 : Space 2) 1 × ℝ =>
      (1 + ‖sphericalCylinder x‖) ^ (-(n : ℝ)))
    ((MeasureTheory.Measure.toSphere volume).prod (volume (α := ℝ)))
  apply Integrable.mono' (hn.comp_snd (MeasureTheory.Measure.toSphere volume))
  · apply AEMeasurable.aestronglyMeasurable
    exact ((continuous_const.add sphericalCylinder_continuous.norm).rpow_const
      (fun x => Or.inl (by positivity : (1 : ℝ) + ‖sphericalCylinder x‖ ≠ 0))).aemeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · simp only [norm_sphericalCylinder]
      exact add_le_add_right (Real.le_sqrt_of_sq_le (le_add_of_nonneg_right zero_le_one)) 1
    · simp


-- @@ L100-103 verbatim
instance sphericalCylinderMeasure_sFinite : SFinite sphericalCylinderMeasure := by
  rw [sphericalCylinderMeasure]
  exact Measure.instSFiniteMap ((MeasureTheory.Measure.toSphere volume).prod (volume (α := ℝ)))
    sphericalCylinder


-- @@ L105-109 verbatim
/-!

## C. The distribution associated with the spherical cylinder

-/


-- @@ L111-113 expanded
/-- The distribution on `Space 3` corresponding to integration over a spherical cylinder. -/
def sphericalCylinderDist : Distribution ℝ (Space 3) ℝ :=
  SchwartzMap.integralCLM ℝ sphericalCylinderMeasure


-- @@ L115-117 verbatim
lemma sphericalCylinderDist_apply_eq_integral_sphericalCylinderMeasure (f : 𝓢(Space 3, ℝ)) :
    sphericalCylinderDist f = ∫ x, f x ∂sphericalCylinderMeasure := by
  rw [sphericalCylinderDist, SchwartzMap.integralCLM_apply]


-- @@ L119-124 verbatim
lemma sphericalCylinderDist_apply_eq_integral_sphere_volume (f : 𝓢(Space 3, ℝ)) :
    sphericalCylinderDist f =
    ∫ x, f (sphericalCylinder x)
      ∂((MeasureTheory.Measure.toSphere volume).prod (volume (α := ℝ))) := by
  rw [sphericalCylinderDist_apply_eq_integral_sphericalCylinderMeasure, sphericalCylinderMeasure,
    MeasurableEmbedding.integral_map sphericalCylinder_measurableEmbedding]


-- @@ L126-126 verbatim
end Space
