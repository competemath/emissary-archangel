import OAI.Probability.GaussianPropeller.ProbabilityBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
open scoped RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped RealInnerProductSpace

-- @@ L11-11 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L12-12 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L13-13 verbatim
open Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L16-16 verbatim
open scoped Topology

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L20-20 verbatim
open scoped NNReal

-- @@ L21-21 verbatim
open Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L23-23 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L25-25 verbatim
open MeasureTheory Set Filter

-- @@ L26-26 verbatim
open scoped Topology BigOperators


-- @@ L28-28 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L29-29 verbatim
open scoped RealInnerProductSpace Topology


-- @@ L31-31 verbatim
namespace GaussianPropeller.Analytic


-- @@ L33-48 verbatim
theorem integral_pos_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hd (x : ℝ) : HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    apply (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv
    field_simp [hb']
    ring
  have ht : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1
  simp


-- @@ L50-68 verbatim
theorem integral_abs_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, |r| * Real.exp (-b * r ^ 2) = b⁻¹ := by
  let f : ℝ → ℝ := fun r => |r| * Real.exp (-b * r ^ 2)
  have hf : Integrable f := by
    simpa only [f, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).abs
  have hpos : ∫ r in Ioi 0, f r = (2 * b)⁻¹ := by
    rw [← integral_pos_mul_exp hb]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
      simp only [f, abs_of_pos (show (0 : ℝ) < r from hr)])
  have hneg : ∫ r in Iic 0, f r = ∫ r in Ioi 0, f r := by
    calc
      ∫ r in Iic 0, f r = ∫ r in Ioi 0, f (-r) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r in Ioi 0, f r := by simp only [f, abs_neg, neg_sq]
  change (∫ r, f r) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos]
  field_simp
  ring


-- @@ L70-82 verbatim
theorem integral_abs_gaussianReal_std :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
    rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [hfun, integral_const_mul, integral_abs_mul_exp (by norm_num : (0 : ℝ) < 1/2)]
  norm_num
  ring


-- @@ L84-96 verbatim
theorem integral_abs_dual_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    ∫ x, |L x| ∂stdGaussian E = ‖L‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  have hm : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => |x|) ((stdGaussian E).map L)), hm,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul, integral_abs_gaussianReal_std]


-- @@ L98-103 verbatim
theorem integral_abs_inner_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    ∫ x, |⟪v, x⟫| ∂stdGaussian E = ‖v‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  simpa only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.norm_map] using
    integral_abs_dual_stdGaussian (InnerProductSpace.toDual ℝ E v)


-- @@ L105-105 verbatim
end GaussianPropeller.Analytic


-- @@ L107-107 verbatim
end OAI
