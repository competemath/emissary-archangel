import OAI.Analysis.LpDimension.DyadicRamps


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory Filter ProbabilityTheory Set Finset

-- @@ L7-7 verbatim
open scoped BigOperators Topology Matrix ENNReal NNReal

-- @@ L8-8 verbatim
universe u uE uΩ uι


-- @@ L10-10 verbatim
namespace SubpolynomialLp


-- @@ L12-12 verbatim
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]


-- @@ L14-15 verbatim
def averageLaw (μ : ι → Measure Ω) : Measure Ω :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, μ i


-- @@ L17-21 verbatim
instance averageLaw_probability [Nonempty ι] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (averageLaw μ) := by
  constructor
  simp [averageLaw,Measure.smul_apply,Measure.finsetSum_apply,ENNReal.inv_mul_cancel,
    Fintype.card_ne_zero]


-- @@ L23-29 verbatim
lemma averageLaw_integrable (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) : Integrable f (averageLaw μ) := by
  by_cases h : IsEmpty ι
  · let _ := h
    simp [averageLaw]
  · have : Nonempty ι := not_isEmpty_iff.mp h
    exact (integrable_finsetSum_measure.mpr (fun i _ => hf i)).smul_measure (by simp)


-- @@ L31-35 verbatim
lemma averageLaw_integral (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) :
    (∫ x, f x ∂averageLaw μ) = (∑ i, ∫ x, f x ∂μ i)/(Fintype.card ι : ℝ) := by
  rw [averageLaw,integral_smul_measure,integral_finsetSum_measure (fun i _ => hf i)]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]


-- @@ L37-39 verbatim
lemma averageLaw_ae [Nonempty ι] (μ : ι → Measure Ω) (P : Ω → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ i, P x) : ∀ᵐ x ∂averageLaw μ, P x := by
  exact Measure.ae_smul_measure (ae_finsetSum_measure_iff.mpr (fun i _ => hP i)) _


-- @@ L41-41 verbatim
section Symmetric

-- @@ L42-42 verbatim
variable {E : Type uE} [AddCommGroup E] [MeasurableSpace E] [MeasurableNeg E]


-- @@ L44-45 verbatim
def symmetricLaw (μ : Measure E) : Measure E := (1/2 : ℝ≥0∞) • μ +
  (1/2 : ℝ≥0∞) • μ.map (fun x => -x)


-- @@ L47-51 verbatim
instance symmetricLaw_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetricLaw μ) := by
  have : IsProbabilityMeasure (μ.map (fun x=>-x)) := inferInstance
  constructor
  norm_num [symmetricLaw,Measure.add_apply,Measure.smul_apply,ENNReal.inv_two_add_inv_two]


-- @@ L53-60 verbatim
lemma symmetricLaw_symmetry (μ : Measure E) :
    (symmetricLaw μ).map (fun x=>-x) = symmetricLaw μ := by
  rw [symmetricLaw,Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_map measurable_neg measurable_neg]
  simp only [Function.comp_def,neg_neg,Measure.map_id']
  exact add_comm _ _


-- @@ L62-69 verbatim
lemma symmetricLaw_ae (μ : Measure E) (P : E → Prop)
    (hP : ∀ᵐ x ∂μ, P x) (hN : ∀ x, P x → P (-x)) :
    ∀ᵐ x ∂symmetricLaw μ, P x := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure hP _
  · apply Measure.ae_smul_measure
    exact (measurableEmbedding_neg.ae_map_iff).mpr (hP.mono hN)



-- @@ L72-82 verbatim
lemma symmetricLaw_even_integral (μ : Measure E) (f : E → ℝ) (hf : Measurable f)
    (hi : Integrable f μ) (hn : ∀ x, f (-x) = f x) :
    (∫ x, f x ∂symmetricLaw μ) = ∫ x, f x ∂μ := by
  have hi' : Integrable f (μ.map (fun x=>-x)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable]
    simpa only [Function.comp_def,hn] using hi
  rw [symmetricLaw,integral_add_measure (hi.smul_measure (by norm_num))
    (hi'.smul_measure (by norm_num)),integral_smul_measure,integral_smul_measure,
    integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
  simp only [hn,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  ring

-- @@ L83-83 verbatim
end Symmetric


-- @@ L85-85 verbatim
end SubpolynomialLp


-- @@ L87-87 verbatim
end


-- @@ L89-89 verbatim
end OAI
