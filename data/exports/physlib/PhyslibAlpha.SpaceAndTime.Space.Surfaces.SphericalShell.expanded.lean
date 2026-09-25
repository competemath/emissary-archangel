/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.SpaceAndTime.Space.ConstantSliceDist
public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- @@ L10-15 verbatim
/-!

## Spherical surfaces on Space.


-/

-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open SchwartzMap NNReal

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open Physlib Distribution

-- @@ L21-22 verbatim
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]


-- @@ L24-24 verbatim
namespace Space


-- @@ L26-26 verbatim
open MeasureTheory Real


-- @@ L28-32 verbatim
/-!

## A. The definition of the spherical shell surface

-/


-- @@ L34-35 verbatim
/-- The inclusion into `Space d` of its unit sphere `S^{d-1}` (the subtype coercion `x ↦ x.1`). -/
def sphericalShell (d : ℕ) : Metric.sphere (0 : Space d) 1 → Space d := fun x => x.1


-- @@ L37-40 verbatim
lemma sphericalShell_injective (d : ℕ) : Function.Injective (sphericalShell d) := by
  intro x y h
  simp [sphericalShell] at h
  grind


-- @@ L42-42 verbatim
lemma sphericalShell_continuous (d : ℕ) : Continuous (sphericalShell d) := continuous_subtype_val


-- @@ L44-47 verbatim
lemma sphericalShell_measurableEmbedding (d : ℕ) : MeasurableEmbedding (sphericalShell d) := by
  apply Continuous.measurableEmbedding
  · exact sphericalShell_continuous d
  · exact sphericalShell_injective d


-- @@ L49-52 verbatim
@[simp]
lemma norm_sphericalShell (d : ℕ) (x : Metric.sphere (0 : Space d) 1) :
    ‖sphericalShell d x‖ = 1 := by
  simp [sphericalShell, Metric.sphere]


-- @@ L54-58 verbatim
/-!

## B. The measure associated with the spherical shell

-/


-- @@ L60-62 verbatim
/-- The measure on `Space d` corresponding to integration around a spherical shell. -/
def sphericalShellMeasure (d : ℕ) : Measure (Space d) :=
  MeasureTheory.Measure.map (sphericalShell d) (MeasureTheory.Measure.toSphere volume)


-- @@ L64-69 verbatim
instance sphericalShellMeasure_hasTemperateGrowth (d : ℕ) :
    (sphericalShellMeasure d).HasTemperateGrowth := by
  rw [sphericalShellMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp


-- @@ L71-75 verbatim
/-!

## C. The distribution associated with the spherical shell

-/


-- @@ L77-82 expanded
/-- The distribution associated with a spherical shell.
  One can roughly think of this distribution as the distribution which
  takes test functions `f (r)` to `∫ d³r f(r) ρ(r)` where `ρ(r)` is the
  mass, charge or current etc. distribution. -/
def sphericalShellDist (d : ℕ) : Distribution ℝ (Space d) ℝ :=
  SchwartzMap.integralCLM ℝ (sphericalShellMeasure d)


-- @@ L85-87 verbatim
lemma sphericalShellDist_apply_eq_integral_sphericalShellMeasure (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    sphericalShellDist d f = ∫ x, f x ∂sphericalShellMeasure d := by
  rw [sphericalShellDist, SchwartzMap.integralCLM_apply]


-- @@ L89-93 verbatim
lemma sphericalShellDist_apply_eq_integral_sphere_volume (d : ℕ) (f : 𝓢(Space d, ℝ)) :
    sphericalShellDist d f =
    ∫ x, f (sphericalShell d x) ∂(MeasureTheory.Measure.toSphere volume) := by
  rw [sphericalShellDist_apply_eq_integral_sphericalShellMeasure, sphericalShellMeasure,
   MeasurableEmbedding.integral_map (sphericalShell_measurableEmbedding d)]


-- @@ L95-95 verbatim
end Space
