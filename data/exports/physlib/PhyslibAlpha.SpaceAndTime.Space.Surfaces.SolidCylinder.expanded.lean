/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SolidSphere
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

-- @@ L11-23 verbatim
/-!

## Solid cylinder surface in `Space 3`

The solid cylinder is the closed unit disk in `Space 2` extruded along the third coordinate.
It is the solid analogue of the spherical cylinder, in the same way that the solid sphere is the
solid analogue of the spherical shell. Like the solid sphere it is a region of positive ambient
volume, so the measure associated with it is built from the ambient volume of the cross-sectional
disk (the solid-sphere measure in `Space 2`) extruded along the axis, rather than a pushforward of
a lower-dimensional surface measure. The measure-zero requirement is therefore not applicable here
and is replaced by a statement that the solid cylinder has positive ambient volume.

-/


-- @@ L25-25 verbatim
@[expose] public section

-- @@ L26-26 verbatim
open SchwartzMap NNReal

-- @@ L27-27 verbatim
noncomputable section

-- @@ L28-28 verbatim
open Physlib Distribution

-- @@ L29-30 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L32-32 verbatim
namespace Space


-- @@ L34-34 verbatim
open MeasureTheory Real


-- @@ L36-40 verbatim
/-!

## A. The definition of the solid cylinder surface

-/


-- @@ L42-45 verbatim
/-- The map embedding a cross-sectional disk extruded along the axis into `Space 3`. The disk is
  cut out by the solid-cylinder measure, which is supported on the closed unit disk. -/
def solidCylinder : Space 2 × ℝ → Space 3 := fun x =>
  (slice 2).symm (x.2, x.1)


-- @@ L47-48 verbatim
lemma solidCylinder_eq :
    solidCylinder = (slice 2).symm ∘ (fun x : Space 2 × ℝ => (x.2, x.1)) := rfl


-- @@ L50-54 verbatim
lemma solidCylinder_injective : Function.Injective solidCylinder := by
  intro x y h
  have h' := congrArg (slice 2) h
  simp only [solidCylinder, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq] at h'
  exact Prod.ext h'.2 h'.1


-- @@ L56-59 verbatim
@[fun_prop]
lemma solidCylinder_continuous : Continuous solidCylinder := by
  rw [solidCylinder_eq]
  fun_prop


-- @@ L61-62 verbatim
lemma solidCylinder_measurableEmbedding : MeasurableEmbedding solidCylinder :=
  Continuous.measurableEmbedding solidCylinder_continuous solidCylinder_injective


-- @@ L64-67 verbatim
@[simp]
lemma norm_solidCylinder (x : Space 2 × ℝ) :
    ‖solidCylinder x‖ = √(‖x.2‖ ^ 2 + ‖x.1‖ ^ 2) := by
  rw [solidCylinder, norm_slice_symm_eq]


-- @@ L69-73 verbatim
/-!

## B. The measure associated with the solid cylinder

-/


-- @@ L75-79 verbatim
/-- The measure on `Space 3` corresponding to integration over a solid cylinder, i.e. the
  pushforward of the product of the solid-sphere (closed unit disk) measure on `Space 2` with the
  line measure along the axis. -/
def solidCylinderMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map solidCylinder ((solidSphereMeasure 2).prod (volume (α := ℝ)))


-- @@ L81-104 verbatim
instance solidCylinderMeasure_hasTemperateGrowth :
    solidCylinderMeasure.HasTemperateGrowth := by
  rw [solidCylinderMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := ℝ))
  use n
  rw [MeasurableEmbedding.integrable_map_iff solidCylinder_measurableEmbedding]
  change Integrable
    (fun x : Space 2 × ℝ => (1 + ‖solidCylinder x‖) ^ (-(n : ℝ)))
    ((solidSphereMeasure 2).prod (volume (α := ℝ)))
  apply Integrable.mono' (hn.comp_snd (solidSphereMeasure 2))
  · apply AEMeasurable.aestronglyMeasurable
    exact ((continuous_const.add solidCylinder_continuous.norm).rpow_const
      (fun x => Or.inl (by positivity : (1 : ℝ) + ‖solidCylinder x‖ ≠ 0))).aemeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · rw [norm_solidCylinder]
      gcongr
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [sq_nonneg ‖x.1‖, norm_nonneg x.2]
    · simp


-- @@ L106-108 verbatim
instance solidCylinderMeasure_sFinite : SFinite solidCylinderMeasure := by
  rw [solidCylinderMeasure]
  exact Measure.instSFiniteMap ((solidSphereMeasure 2).prod (volume (α := ℝ))) solidCylinder


-- @@ L110-114 verbatim
/-!

## C. The distribution associated with the solid cylinder

-/


-- @@ L116-120 expanded
/-- The distribution on `Space 3` corresponding to integration over a solid cylinder.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density spread over a solid cylinder. -/
def solidCylinderDist : Distribution ℝ (Space 3) ℝ :=
  SchwartzMap.integralCLM ℝ solidCylinderMeasure


-- @@ L122-124 verbatim
lemma solidCylinderDist_apply_eq_integral_solidCylinderMeasure (f : 𝓢(Space 3, ℝ)) :
    solidCylinderDist f = ∫ x, f x ∂solidCylinderMeasure := by
  rw [solidCylinderDist, SchwartzMap.integralCLM_apply]


-- @@ L126-130 verbatim
lemma solidCylinderDist_apply_eq_integral_disk_volume (f : 𝓢(Space 3, ℝ)) :
    solidCylinderDist f =
    ∫ x, f (solidCylinder x) ∂((solidSphereMeasure 2).prod (volume (α := ℝ))) := by
  rw [solidCylinderDist_apply_eq_integral_solidCylinderMeasure, solidCylinderMeasure,
    MeasurableEmbedding.integral_map solidCylinder_measurableEmbedding]


-- @@ L132-136 verbatim
/-!

## D. The solid cylinder has positive ambient volume

-/


-- @@ L138-142 verbatim
lemma solidCylinderMeasure_univ_pos : 0 < solidCylinderMeasure Set.univ := by
  rw [solidCylinderMeasure, Measure.map_apply solidCylinder_measurableEmbedding.measurable
    MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod]
  refine ENNReal.mul_pos (solidSphereMeasure_univ_pos 2).ne' ?_
  simp


-- @@ L144-144 verbatim
end Space
