import OAI.Analysis.ProductSpaces.ExponentialExcess


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L6-6 verbatim
open scoped ENNReal NNReal Topology


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace IndependentProducts


-- @@ L12-26 verbatim
lemma exponentialLaw_hypotheses : MultiplierHypotheses exponentialLaw := by
  refine ⟨inferInstance, exponentialLaw_positive, ?_, exponentialLaw_mean, exponentialLaw_memLp⟩
  intro c hc
  have h1 : (1 : ℝ) = c := by
    calc
      1 = ∫ w : ℝ, w ∂exponentialLaw := exponentialLaw_mean.symm
      _ = ∫ _ : ℝ, c ∂exponentialLaw := integral_congr_ae hc
      _ = c := by simp
  have h2 : (∫ w : ℝ, w ^ 2 ∂exponentialLaw) = c ^ 2 := by
    calc
      _ = ∫ _ : ℝ, c ^ 2 ∂exponentialLaw :=
        integral_congr_ae (hc.mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw)
      _ = _ := by simp
  rw [exponentialLaw_second, ← h1] at h2
  norm_num at h2


-- @@ L28-52 verbatim
lemma exponential_midpoint_parameter (t K : ℝ) (ht : 0 < t) (hK : 0 < K) :
    excessConstant K * (t / 3 - 1 / K) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t := by
  have hc : 0 ≤ excessConstant K := (excessConstant_pos K).le
  have hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂exponentialLaw) := by
    rw [exponentialLaw_second]
    positivity
  have h := averaged_midpoint_from_scalar exponentialLaw exponentialLaw_hypotheses
    t (t * excessConstant K) (excessConstant K / K) ht.le (mul_nonneg ht.le hc)
    (div_nonneg hc hK.le) hC
    (fun ι _ a b r hr => exponential_scalar_excess a b K t r hK ht.le hr)
  rw [exponentialLaw_second] at h
  apply le_trans _ h
  have hs : 2 * Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd : t / 3 ≤ t / (2 * Real.sqrt 2) :=
    div_le_div_of_nonneg_left ht.le (by positivity) hs
  have hh := mul_le_mul_of_nonneg_left hd hc
  calc
    excessConstant K * (t / 3 - 1 / K) =
        excessConstant K * (t / 3) - excessConstant K / K := by ring
    _ ≤ excessConstant K * (t / (2 * Real.sqrt 2)) - excessConstant K / K :=
      sub_le_sub_right hh _
    _ = t * excessConstant K / (2 * Real.sqrt 2) - excessConstant K / K := by ring


-- @@ L54-64 verbatim
theorem main_exponential (t : ℝ) (ht : 0 < t) :
    (7 * t / 30) * excessConstant (10 / t) ≤
      averagedMidpointModulus (productSpan exponentialLaw)
        (normSeminorm ℝ (productSpan exponentialLaw)) t ∧
    0 < (7 * t / 30) * excessConstant (10 / t) := by
  constructor
  · have h := exponential_midpoint_parameter t (10 / t) ht (by positivity)
    convert h using 1
    field_simp
    ring
  · exact mul_pos (by positivity) (excessConstant_pos _)


-- @@ L66-66 verbatim
end IndependentProducts


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end OAI
