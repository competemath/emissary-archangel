/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Line

-- @@ L9-16 verbatim
/-!

## Half-plane surface in `Space 3`

The half-plane is the coordinate plane in `Space 3` with nonnegative second
coordinate.

-/


-- @@ L18-18 verbatim
@[expose] public section

-- @@ L19-19 verbatim
open SchwartzMap NNReal

-- @@ L20-20 verbatim
noncomputable section

-- @@ L21-21 verbatim
open Physlib Distribution

-- @@ L22-23 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L25-25 verbatim
namespace Space


-- @@ L27-27 verbatim
open MeasureTheory Real


-- @@ L29-33 verbatim
/-!

## A. The definition of the half-plane surface

-/


-- @@ L35-36 verbatim
/-- The domain of the half-plane inside `Space 2`. -/
def halfPlaneDomain : Set (Space 2) := {x | 0 ≤ x (1 : Fin 2)}


-- @@ L38-39 verbatim
/-- The coordinate plane embedding used for the half-plane surface in `Space 3`. -/
def halfPlane : Space 2 → Space 3 := fun x => (slice (2 : Fin 3)).symm (0, x)


-- @@ L41-41 verbatim
lemma halfPlane_eq : halfPlane = (slice (2 : Fin 3)).symm ∘ (fun x : Space 2 => (0, x)) := rfl


-- @@ L43-47 verbatim
lemma halfPlane_injective : Function.Injective halfPlane := by
  intro x y h
  have h' := congrArg (slice (2 : Fin 3)) h
  simp [halfPlane] at h'
  exact h'


-- @@ L49-52 verbatim
@[fun_prop]
lemma halfPlane_continuous : Continuous halfPlane := by
  rw [halfPlane_eq]
  fun_prop


-- @@ L54-55 verbatim
lemma halfPlane_measurableEmbedding : MeasurableEmbedding halfPlane :=
  Continuous.measurableEmbedding halfPlane_continuous halfPlane_injective


-- @@ L57-60 verbatim
@[simp]
lemma norm_halfPlane (x : Space 2) : ‖halfPlane x‖ = ‖x‖ := by
  rw [halfPlane, norm_slice_symm_eq]
  simp


-- @@ L62-66 verbatim
/-!

## B. The measure associated with the half-plane

-/


-- @@ L68-70 verbatim
/-- The measure on `Space 3` corresponding to integration over a half-plane. -/
def halfPlaneMeasure : Measure (Space 3) :=
  MeasureTheory.Measure.map halfPlane (volume.restrict halfPlaneDomain)


-- @@ L72-82 verbatim
instance halfPlaneMeasure_hasTemperateGrowth :
    halfPlaneMeasure.HasTemperateGrowth := by
  rw [halfPlaneMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨n, hn⟩ := MeasureTheory.Measure.HasTemperateGrowth.exists_integrable
    (μ := volume (α := Space 2))
  use n
  rw [MeasurableEmbedding.integrable_map_iff halfPlane_measurableEmbedding]
  convert! hn.restrict using 1
  ext x
  simp [norm_halfPlane]


-- @@ L84-86 verbatim
instance halfPlaneMeasure_sFinite : SFinite halfPlaneMeasure := by
  rw [halfPlaneMeasure]
  exact Measure.instSFiniteMap (volume.restrict halfPlaneDomain) halfPlane


-- @@ L88-92 verbatim
/-!

## C. The distribution associated with the half-plane

-/


-- @@ L94-96 expanded
/-- The distribution on `Space 3` corresponding to integration over a half-plane. -/
def halfPlaneDist : Distribution ℝ (Space 3) ℝ :=
  SchwartzMap.integralCLM ℝ halfPlaneMeasure


-- @@ L98-100 verbatim
lemma halfPlaneDist_apply_eq_integral_halfPlaneMeasure (f : 𝓢(Space 3, ℝ)) :
    halfPlaneDist f = ∫ x, f x ∂halfPlaneMeasure := by
  rw [halfPlaneDist, SchwartzMap.integralCLM_apply]


-- @@ L102-105 verbatim
lemma halfPlaneDist_apply_eq_integral_volume (f : 𝓢(Space 3, ℝ)) :
    halfPlaneDist f = ∫ x, f (halfPlane x) ∂(volume.restrict halfPlaneDomain) := by
  rw [halfPlaneDist_apply_eq_integral_halfPlaneMeasure, halfPlaneMeasure,
    MeasurableEmbedding.integral_map halfPlane_measurableEmbedding]


-- @@ L107-111 verbatim
/-!

## D. The half-plane has ambient volume zero

-/


-- @@ L113-122 verbatim
/-- The coordinate plane containing the half-plane in `Space 3`. -/
def halfPlaneSubmodule : Submodule ℝ (Space 3) where
  carrier := {x | x (2 : Fin 3) = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Space.add_apply, hx, hy, add_zero]
  smul_mem' c x hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [Space.smul_apply, hx, mul_zero]


-- @@ L124-125 verbatim
lemma halfPlane_mem_halfPlaneSubmodule (x : Space 2) : halfPlane x ∈ halfPlaneSubmodule := by
  simp [halfPlaneSubmodule, halfPlane]


-- @@ L127-130 verbatim
lemma halfPlane_image_domain_subset_halfPlaneSubmodule :
    halfPlane '' halfPlaneDomain ⊆ (halfPlaneSubmodule : Set (Space 3)) := by
  rintro x ⟨y, _, rfl⟩
  exact halfPlane_mem_halfPlaneSubmodule y


-- @@ L132-137 verbatim
lemma halfPlaneSubmodule_ne_top : halfPlaneSubmodule ≠ ⊤ := by
  intro htop
  have hbasis : basis (2 : Fin 3) ∈ halfPlaneSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  simp [halfPlaneSubmodule] at hbasis


-- @@ L139-145 verbatim
lemma volume_halfPlane_image_domain :
    volume (halfPlane '' halfPlaneDomain : Set (Space 3)) = 0 := by
  refine measure_mono_null halfPlane_image_domain_subset_halfPlaneSubmodule ?_
  rw [volume_eq_addHaar]
  exact MeasureTheory.Measure.addHaar_submodule
    (Space.basis.toBasis.addHaar : Measure (Space 3))
    halfPlaneSubmodule halfPlaneSubmodule_ne_top


-- @@ L147-147 verbatim
end Space
