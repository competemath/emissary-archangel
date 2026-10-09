import OAI.Probability.GaussianPropeller.Quantile


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uι


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


-- @@ L18-18 verbatim
open scoped RealInnerProductSpace

-- @@ L19-19 verbatim
namespace GaussianPropeller.QuantilePDE

-- @@ L20-20 verbatim
open GaussianPropeller.Quantile


-- @@ L22-22 verbatim
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L24-28 verbatim
lemma quantile_fderiv {u : E → ℝ} {g : E} {x : E}
    (hu : u x ∈ Ioo (0:ℝ) 1) (hd : HasFDerivAt u (innerSL ℝ g) x) :
    HasFDerivAt (fun y => q (u y)) (innerSL ℝ ((φ (q (u x)))⁻¹ • g)) x := by
  have hh := (hasDerivAt_q hu).comp_hasFDerivAt x hd
  convert hh using 1 <;> (first | rfl | (ext y; simp))


-- @@ L30-53 verbatim
lemma quantile_gradient_line_derivative {u : E → ℝ} {g : E → E}
    {K : E → E →L[ℝ] E} (hu : ∀ x, u x ∈ Ioo (0:ℝ) 1)
    (hdu : ∀ x, HasFDerivAt u (innerSL ℝ (g x)) x)
    (hdg : ∀ x, HasFDerivAt g (K x) x) (x e : E) :
    HasDerivAt (fun s : ℝ => ⟪(φ (q (u (x+s•e))))⁻¹ • g (x+s•e), e⟫)
      ((φ (q (u x)))⁻¹*⟪K x e,e⟫ +
        q (u x)*(φ (q (u x)))⁻¹^2*⟪g x,e⟫^2) 0 := by
  have hdx : HasDerivAt (fun s : ℝ => x+s•e) e 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
  have hdv : HasDerivAt (fun s : ℝ => q (u (x+s•e)))
      ((φ (q (u x)))⁻¹*⟪g x,e⟫) 0 := by
    simpa [Function.comp_def] using (quantile_fderiv (hu (x+0•e)) (hdu (x+0•e))).comp_hasDerivAt 0 hdx
  have hdφ := (hasDerivAt_φ (q (u (x+0•e)))).comp 0 hdv
  have hdi := hdφ.inv (ne_of_gt (φ_pos _))
  have hdg' : HasDerivAt (fun s : ℝ => g (x+s•e)) (K x e) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (hdg (x+0•e)).comp_hasDerivAt 0 hdx
  have hi : HasDerivAt (fun s : ℝ => ⟪g (x+s•e), e⟫) ⟪K x e,e⟫ 0 := by
    simpa using hdg'.inner ℝ (hasDerivAt_const (0:ℝ) e)
  have hh := hdi.mul hi
  convert hh using 1 <;> try rfl
  · funext s; simp only [real_inner_smul_left, Function.comp_def, Pi.mul_apply, Pi.inv_apply]
  · simp only [Function.comp_def, zero_smul, add_zero, Pi.inv_apply]
    field_simp [ne_of_gt (φ_pos (q (u x)))]
    ring


-- @@ L55-61 verbatim
lemma trace_quantile_hessian {ι : Type uι} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (v a : ℝ) (g : E) (K : E →L[ℝ] E) :
    (∑ i : ι, (a*⟪K (e i),e i⟫ + v*a^2*⟪g,e i⟫^2)) - v*‖a • g‖^2 =
      a*(∑ i : ι, ⟪K (e i),e i⟫) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    e.sum_sq_inner_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring


-- @@ L63-63 verbatim
end GaussianPropeller.QuantilePDE


-- @@ L65-65 verbatim
namespace GaussianPropeller.SmoothCDF

-- @@ L66-66 verbatim
open GaussianPropeller.Quantile

-- @@ L67-67 verbatim
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L69-78 verbatim
lemma abs_mul_φ_le (a : ℝ) : |a| *φ a ≤ φ 0 := by
  have hsq : |a| ≤ 1+a^2/2 := by nlinarith [sq_nonneg (|a|-1), sq_abs a]
  have he : |a| ≤ Real.exp (a^2/2) := hsq.trans (by nlinarith [Real.add_one_le_exp (a^2/2)])
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-a^2/2)).le
  rw [← Real.exp_add] at hh
  have heq : a^2/2 + -a^2/2 = 0 := by ring
  rw [heq, Real.exp_zero] at hh
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)]


-- @@ L80-80 verbatim
noncomputable def grad (f : E → ℝ) (g : E → E) (x : E) : E := φ (f x) • g x

-- @@ L81-82 verbatim
noncomputable def hess (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (x : E) : E →L[ℝ] E :=
  φ (f x) • K x - (f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))


-- @@ L84-88 verbatim
lemma fderiv {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (x : E) :
    HasFDerivAt (fun y => Φ (f y)) (innerSL ℝ (grad f g x)) x := by
  have h := (hasDerivAt_Φ (f x)).comp_hasFDerivAt x (hf x)
  convert h using 1 <;> (first | rfl | (ext e; simp [grad]))


-- @@ L90-99 verbatim
lemma grad_fderiv {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (x : E) :
    HasFDerivAt (grad f g) (hess f g K x) x := by
  have h := ((hasDerivAt_φ (f x)).comp_hasFDerivAt x (hf x)).smul (hg x)
  convert h using 1 <;> try rfl
  ext e
  simp only [hess, sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_def]
  module


-- @@ L101-105 verbatim
lemma continuous_hess {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K) : Continuous (hess f g K) := by
  have hφ := continuous_φ.comp hf
  unfold hess
  fun_prop


-- @@ L107-110 verbatim
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma cdf_bound [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ‖Φ (f x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact (Φ_lt_one _).le


-- @@ L112-115 verbatim
lemma grad_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : ∀ x, ‖g x‖ ≤ L) (x : E) : ‖grad f g x‖ ≤ φ 0*L := by
  rw [grad, norm_smul, Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact mul_le_mul (φ_le_zero _) (hL x) (norm_nonneg _) (φ_pos _).le


-- @@ L117-133 verbatim
lemma hess_bound {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E} {L D : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D) (x : E) :
    ‖hess f g K x‖ ≤ φ 0*(D+L^2) := by
  have hD0 : 0 ≤ D := (norm_nonneg (K x)).trans (hD x)
  calc
    ‖hess f g K x‖ ≤ ‖φ (f x) • K x‖ +
        ‖(f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))‖ := norm_sub_le _ _
    _ = φ (f x)*‖K x‖ + (|f x| *φ (f x))*‖g x‖^2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (φ_pos _), abs_mul, abs_of_pos (φ_pos _),
        ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      ring
    _ ≤ φ 0*D + φ 0*L^2 := add_le_add
      (mul_le_mul (φ_le_zero _) (hD x) (norm_nonneg _) (φ_pos _).le)
      (mul_le_mul (abs_mul_φ_le _) ((sq_le_sq₀ (norm_nonneg _) hL0).2 (hL x))
        (sq_nonneg _) (φ_pos _).le)
    _ = _ := by ring


-- @@ L135-135 verbatim
end GaussianPropeller.SmoothCDF


-- @@ L137-137 verbatim
end OAI
