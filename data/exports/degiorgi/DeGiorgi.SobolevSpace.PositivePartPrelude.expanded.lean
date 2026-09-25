import DeGiorgi.SobolevSpace.Approximation


-- @@ L3-8 verbatim
/-!
# Chapter 02: Sobolev Positive-Part Prelude

This module contains the small `L²` lemmas about positive-part truncation that
remain attached to the Sobolev layer.
-/


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open MeasureTheory Metric Filter Topology Set Function Matrix

-- @@ L13-13 verbatim
open scoped ENNReal NNReal Convolution Pointwise


-- @@ L15-15 verbatim
namespace DeGiorgi


-- @@ L17-17 verbatim
variable {d : ℕ} [NeZero d]


-- @@ L19-19 verbatim
local notation "E" => EuclideanSpace ℝ (Fin d)


-- @@ L21-21 verbatim
/-! ## Initial Positive-Part Infrastructure -/


-- @@ L23-49 verbatim
omit [NeZero d] in
/-- Truncating an `L²` function by the positivity set of an a.e.-measurable
scalar function preserves `L²`. -/
theorem indicator_component_memLp
    {Ω : Set E} {σ g : E → ℝ}
    (hσ_aemeas : AEMeasurable σ (volume.restrict Ω))
    (hg_memLp : MemLp g 2 (volume.restrict Ω)) :
    MemLp (fun x => if 0 < σ x then g x else 0) 2 (volume.restrict Ω) := by
  let h : ℝ × ℝ → ℝ := fun yz => if 0 < yz.1 then yz.2 else 0
  have hh_meas : Measurable h := by
    refine measurable_snd.piecewise ?_ measurable_const
    exact measurableSet_lt measurable_const measurable_fst
  have hpair_aemeas :
      AEMeasurable (fun x => (σ x, g x)) (volume.restrict Ω) :=
    hσ_aemeas.prodMk hg_memLp.aemeasurable
  have htrunc_aestrong :
      AEStronglyMeasurable (fun x => if 0 < σ x then g x else 0) (volume.restrict Ω) := by
    refine (hh_meas.comp_aemeasurable hpair_aemeas).aestronglyMeasurable.congr ?_
    filter_upwards [] with x
    by_cases hx : 0 < σ x
    · simp [h, hx]
    · simp [h, hx]
  refine hg_memLp.norm.mono' htrunc_aestrong ?_
  filter_upwards [] with x
  by_cases hx : 0 < σ x
  · simp [hx]
  · simp [hx]


-- @@ L51-63 verbatim
/-- Each component of the truncated positive-part gradient lies in `L²`. -/
theorem posPartGrad_component_memLp
    {Ω : Set E} {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) (i : Fin d) :
    MemLp (fun x => (if 0 < u x then hw.weakGrad x else 0) i) 2
      (volume.restrict Ω) := by
  let _ := (inferInstance : NeZero d)
  convert
    indicator_component_memLp hw.memLp.aemeasurable (hw.weakGrad_component_memLp i) using 1
  ext x
  by_cases hx : 0 < u x
  · simp [hx]
  · simp [hx]


-- @@ L65-65 verbatim
end DeGiorgi
