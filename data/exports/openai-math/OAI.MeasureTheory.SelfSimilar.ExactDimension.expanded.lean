import OAI.MeasureTheory.SelfSimilar.RadialLimit


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
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology

-- @@ L20-20 verbatim
namespace EntropyRateDimension.BallRatios

-- @@ L21-21 verbatim
open MeasureTheory Metric Set Filter

-- @@ L22-22 verbatim
open scoped Topology


-- @@ L24-36 verbatim
theorem radial_limit_of_integer (μ : Measure ℝ) [IsProbabilityMeasure μ] {x d : ℝ}
    (hx : x ∈ μ.support)
    (hlim : Tendsto (fun n : ℕ => information μ x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 d)) :
    Tendsto (fun r => information μ x r / -Real.log r) (𝓝[>] 0) (𝓝 d) := by
  let F : ℝ → ℝ := fun s => information μ x (Real.exp (-s))
  have hF : Monotone F := fun a b hab => information_antitone μ hx (Real.exp_pos _)
    (Real.exp_le_exp.mpr (neg_le_neg hab))
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF Nat.mono_cast (by simp)
    (C := 1) (fun n => by push_cast; exact le_rfl) tendsto_natCast_atTop_atTop hlim
  apply (hfull.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]


-- @@ L38-38 verbatim
end EntropyRateDimension.BallRatios


-- @@ L40-40 verbatim
namespace EntropyRateDimension.Coding

-- @@ L41-41 verbatim
open MeasureTheory Metric Set Filter

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L44-44 verbatim
local instance : MeasurableSpace ι := ⊤

-- @@ L45-45 verbatim
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩


-- @@ L47-51 verbatim
theorem ae_radial_limit (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun r => BallRatios.information (law S) x r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  filter_upwards [ae_radial_sequence S,(law S).support_mem_ae] with x hlim hx
  exact BallRatios.radial_limit_of_integer _ hx hlim


-- @@ L53-53 verbatim
end EntropyRateDimension.Coding


-- @@ L55-55 verbatim
namespace EntropyRateDimension.System

-- @@ L56-56 verbatim
open MeasureEntropy

-- @@ L57-57 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L58-58 verbatim
local instance : MeasurableSpace ι := ⊤

-- @@ L59-59 verbatim
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩


-- @@ L61-67 verbatim
theorem selfSimilar_radial (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 (Coding.exponent S)) := by
  have he := S.selfSimilar_unique μ (Coding.law S) hμ (Coding.law_selfSimilar S)
  subst μ
  exact Coding.ae_radial_limit S


-- @@ L69-73 verbatim
theorem selfSimilar_dimension (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (Coding.exponent S) :=
  LocalMass.lower_dim_eq_of_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) (S.selfSimilar_radial μ hμ)


-- @@ L75-79 verbatim
theorem selfSimilar_entropy_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {D : ℝ} (hD : Coding.exponent S < D) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C :=
  entropy_bound_of_radial_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) hD (S.selfSimilar_radial μ hμ)


-- @@ L81-81 verbatim
end EntropyRateDimension.System


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
