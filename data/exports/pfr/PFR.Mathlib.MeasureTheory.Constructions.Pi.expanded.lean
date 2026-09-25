module

public import Mathlib.MeasureTheory.Constructions.Pi


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
open Function Set


-- @@ L9-9 verbatim
namespace MeasureTheory.Measure

-- @@ L10-11 verbatim
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]


-- @@ L13-14 verbatim
instance : IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩


-- @@ L16-22 verbatim
@[simp]
lemma pi_pi_set (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by
  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]


-- @@ L24-29 verbatim
@[simp]
lemma pi_eval_preimage (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]


-- @@ L31-33 verbatim
lemma map_eval_pi (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by
  ext s hs
  simp_rw [Measure.map_apply (measurable_pi_apply i) hs, pi_eval_preimage]


-- @@ L35-35 verbatim
end MeasureTheory.Measure
