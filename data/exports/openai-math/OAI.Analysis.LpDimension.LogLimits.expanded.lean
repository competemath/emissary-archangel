import OAI.Analysis.LpDimension.AboveTwo


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix

-- @@ L7-7 verbatim
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace

-- @@ L8-8 verbatim
universe u


-- @@ L10-10 verbatim
namespace SubpolynomialLp


-- @@ L12-32 verbatim
lemma subpower_log_limit (f : ℕ → ℕ) (C r : ℝ) (hr : r < 1)
    (hpos : ∀ᶠ n in atTop, 0 < f n)
    (hup : ∀ᶠ n in atTop, (f n : ℝ) ≤ Real.exp (C*Real.log (n:ℝ)^r)) :
    Tendsto (fun n : ℕ => Real.log (f n : ℝ)/Real.log (n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => C*Real.log (n:ℝ)^(r-1)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0 < 1-r)).comp hlog
    simpa only [neg_sub, mul_zero, Function.comp_def] using hh.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
  · filter_upwards [hpos, hup, Filter.eventually_ge_atTop 2] with n hn hu hn2
    have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hl := Real.log_pos hnR
    have hf : (0:ℝ) < f n := by exact_mod_cast hn
    have hh := Real.log_le_log hf hu
    rw [Real.log_exp] at hh
    rw [Real.rpow_sub hl, Real.rpow_one]
    calc
      _ ≤ (C*Real.log (n:ℝ)^r)/Real.log (n:ℝ) := div_le_div_of_nonneg_right hh hl.le
      _ = _ := by ring


-- @@ L34-34 verbatim
end SubpolynomialLp


-- @@ L36-36 verbatim
end


-- @@ L38-38 verbatim
end OAI
