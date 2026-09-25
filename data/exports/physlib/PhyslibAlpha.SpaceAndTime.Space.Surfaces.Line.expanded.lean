/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- @@ L10-14 verbatim
/-!

## Line surfaces in `Space d`

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

## A. The definition of the line surface

-/


-- @@ L32-34 verbatim
/-- The coordinate line embedded in `Space d`. -/
def line (d : ℕ) [NeZero d] : ℝ → Space d := fun r =>
  r • basis (0 : Fin d)


-- @@ L36-37 verbatim
lemma line_eq_smul_basis (d : ℕ) [NeZero d] :
    line d = fun r => r • basis (0 : Fin d) := rfl


-- @@ L39-42 verbatim
lemma line_injective (d : ℕ) [NeZero d] : Function.Injective (line d) := by
  intro x y h
  have h0 := congrArg (fun p : Space d => p (0 : Fin d)) h
  simpa [line] using h0


-- @@ L44-47 verbatim
@[fun_prop]
lemma line_continuous (d : ℕ) [NeZero d] : Continuous (line d) := by
  rw [line_eq_smul_basis]
  fun_prop


-- @@ L49-50 verbatim
lemma line_measurableEmbedding (d : ℕ) [NeZero d] : MeasurableEmbedding (line d) :=
  Continuous.measurableEmbedding (line_continuous d) (line_injective d)


-- @@ L52-55 verbatim
@[simp]
lemma norm_line (d : ℕ) [NeZero d] (r : ℝ) : ‖line d r‖ = ‖r‖ := by
  rw [line, norm_smul]
  simp


-- @@ L57-61 verbatim
/-!

## B. The measure associated with the line

-/


-- @@ L63-65 verbatim
/-- The measure on `Space d` corresponding to integration along a coordinate line. -/
def lineMeasure (d : ℕ) [NeZero d] : Measure (Space d) :=
  MeasureTheory.Measure.map (line d) volume


-- @@ L67-77 verbatim
instance lineMeasure_hasTemperateGrowth (d : ℕ) [NeZero d] :
    (lineMeasure d).HasTemperateGrowth := by
  rw [lineMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨r, hr⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := ℝ))
  use r
  rw [MeasurableEmbedding.integrable_map_iff]
  · convert hr using 1
    ext x
    simp [norm_line]
  · exact line_measurableEmbedding d


-- @@ L79-83 verbatim
/-!

## C. The distribution associated with the line

-/


-- @@ L85-89 expanded
/-- The distribution on `Space d` corresponding to integration along a coordinate line.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density concentrated on a line. -/
def lineDist (d : ℕ) [NeZero d] : Distribution ℝ (Space d) ℝ :=
  SchwartzMap.integralCLM ℝ (lineMeasure d)


-- @@ L91-93 verbatim
lemma lineDist_apply_eq_integral_lineMeasure (d : ℕ) [NeZero d] (f : 𝓢(Space d, ℝ)) :
    lineDist d f = ∫ x, f x ∂lineMeasure d := by
  rw [lineDist, SchwartzMap.integralCLM_apply]


-- @@ L95-98 verbatim
lemma lineDist_apply_eq_integral_volume (d : ℕ) [NeZero d] (f : 𝓢(Space d, ℝ)) :
    lineDist d f = ∫ r : ℝ, f (line d r) := by
  rw [lineDist_apply_eq_integral_lineMeasure, lineMeasure,
    MeasurableEmbedding.integral_map (line_measurableEmbedding d)]


-- @@ L100-104 verbatim
/-!

## D. The line has ambient volume zero

-/


-- @@ L106-108 verbatim
/-- The linear subspace spanned by the coordinate line in `Space d`. -/
def lineSubmodule (d : ℕ) [NeZero d] : Submodule ℝ (Space d) :=
  ℝ ∙ basis (0 : Fin d)


-- @@ L110-112 verbatim
lemma line_mem_lineSubmodule (d : ℕ) [NeZero d] (r : ℝ) : line d r ∈ lineSubmodule d := by
  rw [line_eq_smul_basis]
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self (basis (0 : Fin d)))


-- @@ L114-117 verbatim
lemma range_line_subset_lineSubmodule (d : ℕ) [NeZero d] :
    Set.range (line d) ⊆ (lineSubmodule d : Set (Space d)) := by
  rintro x ⟨r, rfl⟩
  exact line_mem_lineSubmodule d r


-- @@ L119-127 verbatim
lemma lineSubmodule_ne_top (d : ℕ) [NeZero d] (hd : 2 ≤ d) : lineSubmodule d ≠ ⊤ := by
  intro htop
  have hbasis : basis (1 : Fin d) ∈ lineSubmodule d := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton.mp hbasis)
  have hcoord := congrArg (fun p : Space d => p (1 : Fin d)) hc
  have hd1 : d ≠ 1 := by omega
  simp [basis_apply, hd1] at hcoord


-- @@ L129-135 verbatim
lemma volume_line_range (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    volume (Set.range (line d) : Set (Space d)) = 0 := by
  refine measure_mono_null (range_line_subset_lineSubmodule d) ?_
  rw [volume_eq_addHaar]
  exact MeasureTheory.Measure.addHaar_submodule
    (Space.basis.toBasis.addHaar : Measure (Space d))
    (lineSubmodule d) (lineSubmodule_ne_top d hd)


-- @@ L137-137 verbatim
end Space
