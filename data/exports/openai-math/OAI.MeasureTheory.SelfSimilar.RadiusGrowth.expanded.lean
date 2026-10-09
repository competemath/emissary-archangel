import OAI.MeasureTheory.SelfSimilar.BallLimits


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uι


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open scoped BigOperators ENNReal

-- @@ L9-9 verbatim
open MeasureTheory

-- @@ L10-10 verbatim
open MeasureTheory Metric Set Filter

-- @@ L11-11 verbatim
open scoped Topology ENNReal

-- @@ L12-12 verbatim
open MeasureTheory Filter Set ProbabilityTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
open MeasureTheory Metric Set Filter

-- @@ L15-15 verbatim
open scoped ENNReal Topology

-- @@ L16-16 verbatim
open MeasureTheory Filter Set

-- @@ L17-17 verbatim
open scoped Topology BigOperators

-- @@ L18-18 verbatim
namespace EntropyRateDimension.Coding

-- @@ L19-19 verbatim
open MeasureTheory Metric Set Filter

-- @@ L20-20 verbatim
open EntropyRateDimension.ErgodicAux

-- @@ L21-21 verbatim
open scoped Topology BigOperators

-- @@ L22-22 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L23-23 verbatim
local instance : MeasurableSpace ι := ⊤

-- @@ L24-24 verbatim
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩


-- @@ L26-28 verbatim
omit [Fintype ι] [Nonempty ι] in
theorem shift_iterate (n : ℕ) (ω : ℕ → ι) (k : ℕ) : shift^[n] ω k = ω (k+n) :=
  Bernoulli.shift_iterate n ω k


-- @@ L30-38 verbatim
omit [Nonempty ι] in
theorem contraction_integral (S : System ι) :
    (∫ ω, contractionObs S ω ∂addressMeasure S) = S.lyapunov * Real.log 2 := by
  change (∫ ω, -Real.log |S.ratio (ω 0)| ∂addressMeasure S) = _
  rw [head_integral S (fun i => -Real.log |S.ratio i|)]
  unfold System.lyapunov
  rw [neg_mul,Finset.sum_mul]
  simp only [mul_assoc,div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',
    mul_neg,Finset.sum_neg_distrib]


-- @@ L40-48 verbatim
omit [Nonempty ι] in
theorem slope_log_sum (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω n| = birkhoffSum shift (contractionObs S) n ω := by
  induction n with
  | zero => simp [slope_zero,birkhoffSum]
  | succ n ih =>
    rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',
      neg_add,ih,birkhoffSum_succ_apply]
    simp only [contractionObs,shift_iterate,zero_add]


-- @@ L50-60 verbatim
omit [Nonempty ι] in
theorem ae_slope_log_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => -Real.log |slope S ω n| / (n : ℝ)) atTop
      (𝓝 (S.lyapunov * Real.log 2)) := by
  have hT : Ergodic shift (addressMeasure S) := Bernoulli.shift_ergodic (symbolMeasure S)
  have hm : Measurable (contractionObs S) :=
    (measurable_of_finite (fun i => -Real.log |S.ratio i|)).comp (measurable_pi_apply 0)
  have hi : Integrable (contractionObs S) (addressMeasure S) := head_integrable S (fun i => -Real.log |S.ratio i|)
  have hh := ae_tendsto_average hT hm hi
  rw [contraction_integral] at hh
  simpa only [slope_log_sum] using hh


-- @@ L62-62 verbatim
noncomputable def exponent (S : System ι) : ℝ := infoRate S / (S.lyapunov * Real.log 2)


-- @@ L64-67 verbatim
theorem infoRate_nonneg (S : System ι) : 0 ≤ infoRate S := by
  obtain ⟨ω,hω⟩ := (ae_prefixInfo_limit S).exists
  exact ge_of_tendsto' hω (fun n => div_nonneg
    (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))


-- @@ L69-70 verbatim
theorem exponent_nonneg (S : System ι) : 0 ≤ exponent S :=
  div_nonneg (infoRate_nonneg S) (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).le


-- @@ L72-80 verbatim
theorem ae_prefix_exponent (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|) atTop (𝓝 (exponent S)) := by
  filter_upwards [ae_prefixInfo_limit S,ae_slope_log_limit S] with ω hI hR
  have hh := hI.div hR (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).ne'
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  field_simp


-- @@ L82-82 verbatim
end EntropyRateDimension.Coding


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
