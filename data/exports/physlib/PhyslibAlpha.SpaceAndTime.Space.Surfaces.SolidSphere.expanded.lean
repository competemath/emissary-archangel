/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- @@ L10-20 verbatim
/-!

## Solid sphere surfaces in `Space d`

The solid sphere is the closed unit ball in `Space d`. Unlike the line or the spherical
shell, it is a region of positive ambient volume, so the measure associated with it is the
ambient volume restricted to the ball rather than a pushforward of a lower-dimensional measure.
The requirement that the surface has ambient measure zero is therefore not applicable here, and
is replaced by a statement that the solid sphere has positive ambient volume.

-/

-- @@ L21-21 verbatim
@[expose] public section

-- @@ L22-22 verbatim
open SchwartzMap NNReal

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open Physlib Distribution

-- @@ L25-26 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L28-28 verbatim
namespace Space


-- @@ L30-30 verbatim
open MeasureTheory Real


-- @@ L32-36 verbatim
/-!

## A. The definition of the solid sphere surface

-/


-- @@ L38-39 verbatim
/-- The inclusion into `Space d` of its closed unit ball `B^d` (the subtype coercion `x ↦ x.1`). -/
def solidSphere (d : ℕ) : Metric.closedBall (0 : Space d) 1 → Space d := fun x => x.1


-- @@ L41-44 verbatim
lemma solidSphere_injective (d : ℕ) : Function.Injective (solidSphere d) := by
  intro x y h
  simp [solidSphere] at h
  grind


-- @@ L46-46 verbatim
lemma solidSphere_continuous (d : ℕ) : Continuous (solidSphere d) := continuous_subtype_val


-- @@ L48-51 verbatim
lemma solidSphere_measurableEmbedding (d : ℕ) : MeasurableEmbedding (solidSphere d) := by
  apply Continuous.measurableEmbedding
  · exact solidSphere_continuous d
  · exact solidSphere_injective d


-- @@ L53-58 verbatim
@[simp]
lemma norm_solidSphere_le (d : ℕ) (x : Metric.closedBall (0 : Space d) 1) :
    ‖solidSphere d x‖ ≤ 1 := by
  have hx := x.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  exact hx


-- @@ L60-64 verbatim
/-!

## B. The measure associated with the solid sphere

-/


-- @@ L66-69 verbatim
/-- The measure on `Space d` corresponding to integration over a solid sphere, i.e. the
  ambient volume measure restricted to the closed unit ball. -/
def solidSphereMeasure (d : ℕ) : Measure (Space d) :=
  volume.restrict (Metric.closedBall (0 : Space d) 1)


-- @@ L71-74 verbatim
instance solidSphereMeasure_isFiniteMeasure (d : ℕ) :
    IsFiniteMeasure (solidSphereMeasure d) := by
  rw [solidSphereMeasure, isFiniteMeasure_restrict]
  exact (Metric.isBounded_closedBall).measure_lt_top.ne


-- @@ L76-78 verbatim
instance solidSphereMeasure_hasTemperateGrowth (d : ℕ) :
    (solidSphereMeasure d).HasTemperateGrowth :=
  inferInstance


-- @@ L80-84 verbatim
/-!

## C. The distribution associated with the solid sphere

-/


-- @@ L86-90 expanded
/-- The distribution on `Space d` corresponding to integration over a solid sphere.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density spread over a solid ball. -/
def solidSphereDist (d : ℕ) : Distribution ℝ (Space d) ℝ :=
  SchwartzMap.integralCLM ℝ (solidSphereMeasure d)


-- @@ L92-94 verbatim
lemma solidSphereDist_apply_eq_integral_solidSphereMeasure (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    solidSphereDist d f = ∫ x, f x ∂solidSphereMeasure d := by
  rw [solidSphereDist, SchwartzMap.integralCLM_apply]


-- @@ L96-98 verbatim
lemma solidSphereDist_apply_eq_integral_closedBall (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    solidSphereDist d f = ∫ x in Metric.closedBall (0 : Space d) 1, f x := by
  rw [solidSphereDist_apply_eq_integral_solidSphereMeasure, solidSphereMeasure]


-- @@ L100-104 verbatim
/-!

## D. The solid sphere has positive ambient volume

-/


-- @@ L106-110 verbatim
lemma solidSphere_volume_pos (d : ℕ) :
    0 < volume (Metric.closedBall (0 : Space d) 1) := by
  apply lt_of_lt_of_le (b := volume (Metric.ball (0 : Space d) 1))
  · exact (Metric.isOpen_ball).measure_pos volume (Metric.nonempty_ball.mpr one_pos)
  · exact measure_mono Metric.ball_subset_closedBall


-- @@ L112-114 verbatim
lemma solidSphereMeasure_univ_pos (d : ℕ) : 0 < solidSphereMeasure d Set.univ := by
  rw [solidSphereMeasure, Measure.restrict_apply_univ]
  exact solidSphere_volume_pos d


-- @@ L116-116 verbatim
end Space
