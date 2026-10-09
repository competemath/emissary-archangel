import OAI.Analysis.LiebThirring.ActionBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory

-- @@ L7-7 verbatim
open scoped ENNReal Matrix.Norms.L2Operator

-- @@ L8-8 verbatim
open Matrix

-- @@ L9-9 verbatim
open Matrix Unitary MeasureTheory Set

-- @@ L10-10 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open Matrix Unitary MeasureTheory Set

-- @@ L13-13 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Set Filter

-- @@ L16-16 verbatim
open scoped Topology

-- @@ L17-17 verbatim
open scoped NNReal



-- @@ L20-20 verbatim
namespace SharpLiebThirring.ExtremizerProof

-- @@ L21-21 verbatim
open MeasureTheory Set Filter

-- @@ L22-22 verbatim
open scoped Topology ENNReal


-- @@ L24-25 verbatim
/-- The positive, unnormalized bound state. -/
def profile (r x : ℝ) : ℝ := (Real.cosh (r * x)) ^ (-1 / r)


-- @@ L27-27 verbatim
def potential (r x : ℝ) : ℝ := (r + 1) * (Real.cosh (r * x))⁻¹ ^ 2


-- @@ L29-29 verbatim
def profileDerivative (r x : ℝ) : ℝ := -Real.tanh (r * x) * profile r x


-- @@ L31-32 verbatim
lemma profile_pos (r x : ℝ) : 0 < profile r x :=
  Real.rpow_pos_of_pos (Real.cosh_pos _) _


-- @@ L34-36 verbatim
lemma profile_continuous (r : ℝ) : Continuous (profile r) := by
  exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).rpow_const
    (fun _ ↦ Or.inl (ne_of_gt (Real.cosh_pos _)))


-- @@ L38-40 verbatim
lemma profile_contDiff (r : ℝ) : ContDiff ℝ ⊤ (profile r) := by
  exact (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).rpow_const_of_ne
    (fun _ ↦ ne_of_gt (Real.cosh_pos _))


-- @@ L42-50 verbatim
lemma profile_hasDerivAt {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (profile r) (profileDerivative r x) x := by
  have hh := ((Real.hasDerivAt_cosh (r*x)).comp x ((hasDerivAt_id x).const_mul r)).rpow_const (p := -1 / r)
    (Or.inl (ne_of_gt (Real.cosh_pos _)))
  convert! hh using 1
  unfold profileDerivative profile
  simp only [Function.comp_apply]
  rw [Real.tanh_eq_sinh_div_cosh, Real.rpow_sub (Real.cosh_pos _), Real.rpow_one]
  field_simp


-- @@ L52-60 verbatim
lemma tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ 2) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  convert! hh using 1
  · funext t
    exact Real.tanh_eq_sinh_div_cosh t
  · have hx := Real.cosh_sq_sub_sinh_sq x
    field_simp
    nlinarith


-- @@ L62-68 verbatim
lemma tanh_sq_add_sech_sq (x : ℝ) :
    Real.tanh x ^ 2 + (Real.cosh x)⁻¹ ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hx := Real.cosh_sq_sub_sinh_sq x
  have hn : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith


-- @@ L70-78 verbatim
lemma profileDerivative_hasDerivAt {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (profileDerivative r) ((1 - potential r x) * profile r x) x := by
  have ht := (tanh_hasDerivAt (r*x)).comp x ((hasDerivAt_id x).const_mul r)
  have hh := ht.neg.mul (profile_hasDerivAt hr x)
  convert! hh using 1
  unfold profileDerivative potential
  simp only [Function.comp_apply, Pi.neg_apply, mul_one]
  have he := congrArg (fun y : ℝ ↦ y * profile r x) (tanh_sq_add_sech_sq (r*x))
  nlinarith


-- @@ L80-84 verbatim
lemma profileDerivative_continuous (r : ℝ) : Continuous (profileDerivative r) := by
  have ht : Continuous Real.tanh := continuous_iff_continuousAt.mpr
    (fun x ↦ (tanh_hasDerivAt x).continuousAt)
  exact ((ht.comp (continuous_const.mul continuous_id)).neg).mul
    (profile_continuous r)


-- @@ L86-89 verbatim
lemma potential_continuous (r : ℝ) : Continuous (potential r) := by
  unfold potential
  exact continuous_const.mul (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
    (fun _ ↦ ne_of_gt (Real.cosh_pos _))).pow 2)


-- @@ L91-93 verbatim
lemma potential_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 ≤ potential r x := by
  unfold potential
  positivity


-- @@ L95-98 verbatim
lemma cosh_lower_exponential (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs x, Real.cosh_eq]
  have hh := Real.exp_pos (-|x|)
  linarith


-- @@ L100-113 verbatim
lemma profile_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    profile r x ≤ 2 ^ (1 / r) * Real.exp (-|x|) := by
  have he : 0 < Real.exp |r*x| / 2 := by positivity
  have hp : -1 / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hr.le
  have hh := Real.rpow_le_rpow_of_nonpos he (cosh_lower_exponential (r*x)) hp
  change (Real.cosh (r*x)) ^ (-1 / r) ≤ _
  apply hh.trans_eq
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul,
    abs_mul, abs_of_pos hr]
  have hmul : r * |x| * (-1 / r) = -|x| := by field_simp
  rw [hmul]
  have hpow : (2 : ℝ) ^ (-1 / r) = (2 ^ (1 / r))⁻¹ := by
    rw [show -1 / r = -(1 / r) by ring, Real.rpow_neg (by norm_num)]
  rw [hpow, div_inv_eq_mul, mul_comm]


-- @@ L115-120 verbatim
lemma profileDerivative_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    |profileDerivative r x| ≤ 2 ^ (1 / r) * Real.exp (-|x|) := by
  unfold profileDerivative
  rw [abs_mul, abs_neg, abs_of_pos (profile_pos r x)]
  exact (mul_le_of_le_one_left (profile_pos r x).le (Real.abs_tanh_lt_one _).le).trans
    (profile_exponential_bound hr x)


-- @@ L122-139 verbatim
lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|)) := by
  have hp : IntegrableOn (fun x : ℝ ↦ Real.exp (-c * |x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0).congr_fun
    · intro x hx
      dsimp only
      rw [abs_of_pos (show 0 < x from hx)]
    · exact measurableSet_Ioi
  have hn : IntegrableOn (fun x : ℝ ↦ Real.exp (-c * |x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun
    · intro x hx
      dsimp only
      rw [abs_of_nonpos (show x ≤ 0 from hx)]
      congr 1
      ring
    · exact measurableSet_Iic
  have hh := hn.union hp
  simpa using hh


-- @@ L141-150 verbatim
lemma memLp_exp_neg_abs {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (fun x : ℝ ↦ Real.exp (-|x|)) p volume := by
  have hc : Continuous (fun x : ℝ ↦ Real.exp (-|x|)) := by fun_prop
  apply (integrable_norm_rpow_iff hc.aestronglyMeasurable hp hp').mp
  have hh := integrable_exp_neg_abs (ENNReal.toReal_pos hp hp')
  convert! hh using 1
  funext x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  ring


-- @@ L152-158 verbatim
lemma profile_memLp (r : ℝ) (hr : 0 < r) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (profile r) p volume := by
  apply ((memLp_exp_neg_abs hp hp').const_mul (2 ^ (1 / r))).mono'
    (profile_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (profile_pos r x)]
    exact profile_exponential_bound hr x)


-- @@ L160-164 verbatim
lemma profileDerivative_memLp (r : ℝ) (hr : 0 < r) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (profileDerivative r) p volume := by
  apply ((memLp_exp_neg_abs hp hp').const_mul (2 ^ (1 / r))).mono'
    (profileDerivative_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (profileDerivative_exponential_bound hr)


-- @@ L166-166 verbatim
end SharpLiebThirring.ExtremizerProof


-- @@ L168-168 verbatim
namespace SharpLiebThirring.SobolevProof

-- @@ L169-169 verbatim
open MeasureTheory Set Filter

-- @@ L170-170 verbatim
open scoped Topology ENNReal ContDiff


-- @@ L172-173 verbatim
/-- Fixed smooth compact cutoff, equal to one on [-1,1]. -/
def baseCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩


-- @@ L175-175 verbatim
def cutoff (n : ℕ) (x : ℝ) : ℝ := baseCutoff ((n + 1 : ℝ)⁻¹ * x)


-- @@ L177-178 verbatim
def cutoffDerivative (n : ℕ) (x : ℝ) : ℝ :=
  deriv (baseCutoff : ℝ → ℝ) ((n + 1 : ℝ)⁻¹ * x) * (n + 1 : ℝ)⁻¹


-- @@ L180-180 verbatim
lemma baseCutoff_smooth : ContDiff ℝ ∞ (baseCutoff : ℝ → ℝ) := baseCutoff.contDiff


-- @@ L182-182 verbatim
lemma scale_pos (n : ℕ) : 0 < (n + 1 : ℝ) := by positivity


-- @@ L184-185 verbatim
lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  baseCutoff_smooth.comp (contDiff_const.mul contDiff_id)


-- @@ L187-190 verbatim
lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  change HasCompactSupport (fun x : ℝ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * x))
  simpa only [smul_eq_mul] using baseCutoff.hasCompactSupport.comp_smul
    (inv_ne_zero (ne_of_gt (scale_pos n)))


-- @@ L192-198 verbatim
lemma cutoff_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n) (cutoffDerivative n x) x := by
  change HasDerivAt (fun y : ℝ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * y))
    (deriv (baseCutoff : ℝ → ℝ) ((n + 1 : ℝ)⁻¹ * x) * (n + 1 : ℝ)⁻¹) x
  convert!
    (((baseCutoff_smooth.differentiable (by norm_num)) _).hasDerivAt.comp x
      ((hasDerivAt_id x).const_mul (n + 1 : ℝ)⁻¹)) using 1; simp only [id_eq, mul_one]


-- @@ L200-202 verbatim
lemma cutoffDerivative_continuous (n : ℕ) : Continuous (cutoffDerivative n) := by
  exact (((baseCutoff_smooth.continuous_deriv (by norm_num)).comp
    (continuous_const.mul continuous_id)).mul continuous_const)


-- @@ L204-207 verbatim
lemma cutoff_bound (n : ℕ) (x : ℝ) : |cutoff n x| ≤ 1 := by
  unfold cutoff
  rw [abs_of_nonneg (baseCutoff.nonneg)]
  exact baseCutoff.le_one


-- @@ L209-210 verbatim
lemma scale_tendsto : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))


-- @@ L212-219 verbatim
lemma cutoff_tendsto (x : ℝ) : Tendsto (fun n : ℕ ↦ cutoff n x) atTop (𝓝 1) := by
  have hh := baseCutoff_smooth.continuous.continuousAt.tendsto.comp
    (scale_tendsto.mul_const x)
  have hb : (baseCutoff : ℝ → ℝ) 0 = 1 := by
    apply baseCutoff.one_of_mem_closedBall
    simp [baseCutoff, Metric.mem_closedBall]
  change Tendsto (fun n : ℕ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * x)) atTop (𝓝 1)
  convert! hh using 1; simp only [zero_mul, hb]


-- @@ L221-233 verbatim
lemma cutoffDerivative_uniform_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ n x, |cutoffDerivative n x| ≤ D := by
  obtain ⟨D, hD⟩ := baseCutoff.hasCompactSupport.deriv.exists_bound_of_continuous
    (baseCutoff_smooth.continuous_deriv (by norm_num))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨D, hD0, fun n x ↦ ?_⟩
  unfold cutoffDerivative
  rw [abs_mul, abs_of_pos (inv_pos.mpr (scale_pos n))]
  have hi : (n + 1 : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_num
  exact (mul_le_mul_of_nonneg_right (hD _) (inv_pos.mpr (scale_pos n)).le).trans
    (mul_le_of_le_one_right hD0 hi)


-- @@ L235-239 verbatim
lemma cutoffDerivative_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ ↦ cutoffDerivative n x) atTop (𝓝 0) := by
  have hh := (baseCutoff_smooth.continuous_deriv (by norm_num)).continuousAt.tendsto.comp
    (scale_tendsto.mul_const x)
  simpa [cutoffDerivative] using hh.mul scale_tendsto


-- @@ L241-254 verbatim
/-- Dominated convergence for a uniformly bounded multiplier of an L¹ function. -/
lemma integral_multiplier_tendsto {a : ℕ → ℝ → ℂ} {l : ℂ} {g : ℝ → ℂ}
    (hg : Integrable g) (ha : ∀ n, AEStronglyMeasurable (a n) volume)
    {D : ℝ} (_hD : 0 ≤ D) (hb : ∀ n x, ‖a n x‖ ≤ D)
    (hl : ∀ x, Tendsto (fun n ↦ a n x) atTop (𝓝 l)) :
    Tendsto (fun n ↦ ∫ x : ℝ, a n x * g x) atTop (𝓝 (∫ x : ℝ, l * g x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ D * ‖g x‖)
  · exact fun n ↦ (ha n).mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul D
  · intro n
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _))
  · exact Filter.Eventually.of_forall (fun x ↦ (hl x).mul_const (g x))


-- @@ L256-256 verbatim
end SharpLiebThirring.SobolevProof


-- @@ L258-258 verbatim
namespace SharpLiebThirring.SobolevProof

-- @@ L259-259 verbatim
open MeasureTheory Set Filter

-- @@ L260-260 verbatim
open scoped Topology ENNReal ContDiff


-- @@ L262-319 verbatim
/-- Extend the distributional H¹ identity from compactly supported tests to
smooth L² tests with L² classical derivative. No pointwise representative of
an arbitrary H¹ element is assumed. -/
lemma weak_derivative_smooth_L2 (v : H1) {f f' : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf2 : MemLp f 2 volume) (hf'2 : MemLp f' 2 volume) :
    (∫ x : ℝ, v.val x * f' x) = -(∫ x : ℝ, v.grad x * f x) := by
  have hg0 : Integrable (fun x ↦ v.val x * f x) := v.val_memLp.integrable_mul hf2
  have hg1 : Integrable (fun x ↦ v.val x * f' x) := v.val_memLp.integrable_mul hf'2
  have hg2 : Integrable (fun x ↦ v.grad x * f x) := v.grad_memLp.integrable_mul hf2
  obtain ⟨D, hD, hDb⟩ := cutoffDerivative_uniform_bound
  have hc (n : ℕ) : ContDiff ℝ ∞ (fun x ↦ (cutoff n x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (cutoff_contDiff n)
  have hcm (n : ℕ) : AEStronglyMeasurable (fun x ↦ (cutoff n x : ℂ)) volume :=
    (hc n).continuous.aestronglyMeasurable
  have hdm (n : ℕ) : AEStronglyMeasurable (fun x ↦ (cutoffDerivative n x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (cutoffDerivative_continuous n)).aestronglyMeasurable
  have hcb (n : ℕ) (x : ℝ) : ‖(cutoff n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using cutoff_bound n x
  have hdb (n : ℕ) (x : ℝ) : ‖(cutoffDerivative n x : ℂ)‖ ≤ D := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hDb n x
  have hcl (x : ℝ) : Tendsto (fun n ↦ (cutoff n x : ℂ)) atTop (𝓝 1) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoff_tendsto x)
  have hdl (x : ℝ) : Tendsto (fun n ↦ (cutoffDerivative n x : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoffDerivative_tendsto x)
  have h0 := integral_multiplier_tendsto hg0 hdm hD hdb hdl
  have h1 := integral_multiplier_tendsto hg1 hcm (by norm_num : (0 : ℝ) ≤ 1) hcb hcl
  have h2 := integral_multiplier_tendsto hg2 hcm (by norm_num : (0 : ℝ) ≤ 1) hcb hcl
  simp only [zero_mul, one_mul, integral_zero] at h0 h1 h2
  have heq (n : ℕ) :
      (∫ x : ℝ, (cutoffDerivative n x : ℂ) * (v.val x * f x)) +
      (∫ x : ℝ, (cutoff n x : ℂ) * (v.val x * f' x)) =
      -(∫ x : ℝ, (cutoff n x : ℂ) * (v.grad x * f x)) := by
    let φ : ℝ → ℂ := fun x ↦ (cutoff n x : ℂ) * f x
    have hφ : ContDiff ℝ ∞ φ := (hc n).mul hf
    have hcc : HasCompactSupport (fun x ↦ (cutoff n x : ℂ)) :=
      (cutoff_compact n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hφc : HasCompactSupport φ := hcc.mul_right
    have hφd (x : ℝ) : deriv φ x =
        (cutoffDerivative n x : ℂ) * f x + (cutoff n x : ℂ) * f' x := by
      exact (((cutoff_hasDerivAt n x).ofReal_comp).mul (hd x)).deriv
    have hh := v.weak_derivative φ hφ hφc
    have hi0 := hg0.bdd_mul (hdm n) (Filter.Eventually.of_forall (hdb n))
    have hi1 := hg1.bdd_mul (hcm n) (Filter.Eventually.of_forall (hcb n))
    rw [← integral_add hi0 hi1]
    calc
      _ = ∫ x : ℝ, v.val x * deriv φ x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp only; rw [hφd]; ring)
      _ = -(∫ x : ℝ, v.grad x * φ x) := hh
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp [φ]; ring)
  have he : Tendsto (fun n ↦ -(∫ x : ℝ, (cutoff n x : ℂ) * (v.grad x * f x)))
      atTop (𝓝 (∫ x : ℝ, v.val x * f' x)) := by
    simpa only [zero_add] using (h0.add h1).congr (fun n ↦ heq n)
  exact tendsto_nhds_unique he h2.neg


-- @@ L321-321 verbatim
end SharpLiebThirring.SobolevProof


-- @@ L323-323 verbatim
namespace SharpLiebThirring.SobolevProof

-- @@ L324-324 verbatim
open MeasureTheory

-- @@ L325-325 verbatim
open scoped ContDiff


-- @@ L327-343 verbatim
/-- Classical smooth L² functions with L² derivative belong to the exact weak H¹ domain. -/
def smoothH1 (f f' : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hfc : Continuous f')
    (hf2 : MemLp f 2 volume) (hf'2 : MemLp f' 2 volume) : H1 where
  val := f
  grad := f'
  val_memLp := hf2
  grad_memLp := hf'2
  weak_derivative := by
    intro φ hφ hφc
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
    · exact fun x _ ↦ hd x
    · exact fun x _ ↦ ((hφ.differentiable (by norm_num)) x).hasDerivAt
    · exact (hf.continuous.mul (hφ.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hφc.deriv.mul_left
    · exact (hfc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left


-- @@ L345-345 verbatim
end SharpLiebThirring.SobolevProof


-- @@ L347-347 verbatim
namespace SharpLiebThirring.ExtremizerProof

-- @@ L348-348 verbatim
open MeasureTheory Set Filter

-- @@ L349-349 verbatim
open scoped Topology ENNReal ContDiff


-- @@ L351-355 verbatim
lemma potential_le {r : ℝ} (hr : 0 < r) (x : ℝ) : potential r x ≤ r + 1 := by
  have hi : (Real.cosh (r*x))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh _)
  have hi0 : 0 ≤ (Real.cosh (r*x))⁻¹ := inv_nonneg.mpr (Real.cosh_pos _).le
  have hs : (Real.cosh (r*x))⁻¹ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_right (by linarith) hs


-- @@ L357-361 verbatim
lemma potential_contDiff (r : ℝ) : ContDiff ℝ ∞ (potential r) := by
  unfold potential
  exact contDiff_const.mul
    (((Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).inv
      (fun _ ↦ ne_of_gt (Real.cosh_pos _))).pow 2)


-- @@ L363-370 verbatim
lemma profileDerivative_contDiff (r : ℝ) : ContDiff ℝ ∞ (profileDerivative r) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    convert! (Real.contDiff_sinh.div Real.contDiff_cosh
      (fun _ ↦ ne_of_gt (Real.cosh_pos _))) using 1
    funext t
    exact Real.tanh_eq_sinh_div_cosh t
  exact ((ht.comp (contDiff_const.mul contDiff_id)).neg).mul
    ((profile_contDiff r).of_le le_top)


-- @@ L372-372 verbatim
def profileSecond (r x : ℝ) : ℝ := (1 - potential r x) * profile r x


-- @@ L374-375 verbatim
lemma profileSecond_continuous (r : ℝ) : Continuous (profileSecond r) :=
  (continuous_const.sub (potential_continuous r)).mul (profile_continuous r)


-- @@ L377-386 verbatim
lemma profileSecond_memLp (r : ℝ) (hr : 0 < r) : MemLp (profileSecond r) 2 volume := by
  apply ((profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).const_mul (r + 2)).mono'
    (profileSecond_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [profileSecond, Real.norm_eq_abs, abs_mul, abs_of_pos (profile_pos r x)]
    apply mul_le_mul_of_nonneg_right _ (profile_pos r x).le
    have hW := potential_nonneg hr x
    have hW' := potential_le hr x
    apply abs_le.mpr
    constructor <;> linarith)


-- @@ L388-395 verbatim
/-- The exact unnormalized extremizing bound state, as an element of the weak form domain. -/
def boundState (r : ℝ) (hr : 0 < r) : H1 :=
  SobolevProof.smoothH1 (fun x ↦ (profile r x : ℂ)) (fun x ↦ (profileDerivative r x : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((profile_contDiff r).of_le le_top))
    (fun x ↦ (profile_hasDerivAt hr x).ofReal_comp)
    (Complex.continuous_ofReal.comp (profileDerivative_continuous r))
    (profile_memLp r hr (by norm_num) (by norm_num)).ofReal
    (profileDerivative_memLp r hr (by norm_num) (by norm_num)).ofReal


-- @@ L397-411 verbatim
lemma boundState_weak_ode {r : ℝ} (hr : 0 < r) (v : H1) :
    (∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) =
    -(∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) := by
  have hh := SobolevProof.weak_derivative_smooth_L2 v
    (f := fun x ↦ (profileDerivative r x : ℂ))
    (f' := fun x ↦ (profileSecond r x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (profileDerivative_contDiff r))
    (fun x ↦ (profileDerivative_hasDerivAt hr x).ofReal_comp)
    (profileDerivative_memLp r hr (by norm_num) (by norm_num)).ofReal
    (profileSecond_memLp r hr).ofReal
  have hc := congrArg (starRingEnd ℂ) hh
  simp only [map_neg, ← integral_conj, map_mul, Complex.conj_ofReal] at hc
  change (∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) =
    -(∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) at hc
  exact (neg_eq_iff_eq_neg.mpr hc).symm


-- @@ L413-440 verbatim
lemma boundState_negativeEigenfunction {r : ℝ} (hr : 0 < r) :
    IsNegativeEigenfunction (potential r) 1 (boundState r hr) := by
  refine ⟨by norm_num, fun v ↦ ?_⟩
  have hψ := (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).ofReal (K := ℂ)
  have hi : Integrable (fun x ↦ star (v.val x) * (profile r x : ℂ)) :=
    v.val_memLp.star.integrable_mul hψ
  have hWm : AEStronglyMeasurable (fun x ↦ (potential r x : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (potential_continuous r)).aestronglyMeasurable
  have hWb : ∀ᵐ x : ℝ, ‖(potential r x : ℂ)‖ ≤ r + 1 := by
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hr x)]
      exact potential_le hr x)
  have hiW := hi.bdd_mul hWm hWb
  change (∫ x : ℝ, star (v.grad x) * (profileDerivative r x : ℂ)) -
    (∫ x : ℝ, (potential r x : ℂ) * star (v.val x) * (profile r x : ℂ)) =
    -(1 ^ 2 : ℝ) * (∫ x : ℝ, star (v.val x) * (profile r x : ℂ))
  rw [boundState_weak_ode hr]
  have hs : (∫ x : ℝ, star (v.val x) * (profileSecond r x : ℂ)) =
      (∫ x : ℝ, star (v.val x) * (profile r x : ℂ)) -
      (∫ x : ℝ, (potential r x : ℂ) * (star (v.val x) * (profile r x : ℂ))) := by
    rw [← integral_sub hi hiW]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      simp only [profileSecond, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
      ring)
  rw [hs]
  simp only [mul_assoc, one_pow, Complex.ofReal_one, neg_mul, one_mul]
  ring


-- @@ L442-442 verbatim
end SharpLiebThirring.ExtremizerProof


-- @@ L444-444 verbatim
namespace SharpLiebThirring

-- @@ L445-445 verbatim
open MeasureTheory


-- @@ L447-455 verbatim
/-- Scalar multiplication in the weak form domain, without choosing pointwise representatives. -/
def scaleH1 (c : ℂ) (u : H1) : H1 where
  val := fun x ↦ c * u.val x
  grad := fun x ↦ c * u.grad x
  val_memLp := u.val_memLp.const_mul c
  grad_memLp := u.grad_memLp.const_mul c
  weak_derivative := by
    intro φ hφ hφc
    simp only [mul_assoc, integral_const_mul, u.weak_derivative φ hφ hφc, mul_neg]


-- @@ L457-464 verbatim
lemma l2Pairing_scale_both (c : ℂ) (u : H1) :
    l2Pairing (scaleH1 c u) (scaleH1 c u) = star c * c * l2Pairing u u := by
  change (∫ x : ℝ, star (c * u.val x) * (c * u.val x)) = _
  simp only [star_mul]
  have he (x : ℝ) : star (u.val x) * star c * (c * u.val x) =
      (star c * c) * (star (u.val x) * u.val x) := by ring
  simp_rw [he]
  exact integral_const_mul _ _


-- @@ L466-470 verbatim
lemma l2Pairing_scale_right (c : ℂ) (v u : H1) :
    l2Pairing v (scaleH1 c u) = c * l2Pairing v u := by
  change (∫ x : ℝ, star (v.val x) * (c * u.val x)) = _
  simp_rw [show ∀ a b : ℂ, a * (c * b) = c * (a*b) by intros; ring]
  exact integral_const_mul _ _


-- @@ L472-478 verbatim
lemma schrodingerForm_scale_right (W : ℝ → ℝ) (c : ℂ) (v u : H1) :
    schrodingerForm W v (scaleH1 c u) = c * schrodingerForm W v u := by
  change (∫ x : ℝ, star (v.grad x) * (c * u.grad x)) -
    (∫ x : ℝ, (W x : ℂ) * star (v.val x) * (c * u.val x)) = _
  simp_rw [show ∀ a b : ℂ, a * (c * b) = c * (a*b) by intros; ring]
  rw [integral_const_mul, integral_const_mul]
  exact (mul_sub _ _ _).symm


-- @@ L480-485 verbatim
lemma IsNegativeEigenfunction.scale {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hu : IsNegativeEigenfunction W k u) (c : ℂ) :
    IsNegativeEigenfunction W k (scaleH1 c u) := by
  refine ⟨hu.1, fun v ↦ ?_⟩
  rw [schrodingerForm_scale_right, l2Pairing_scale_right, hu.2 v]
  ring


-- @@ L487-501 verbatim
lemma oneStateMoment_le_negativeMoment (γ : ℝ) (W : ℝ → ℝ) :
    oneStateMoment γ W ≤ negativeMoment γ W := by
  unfold oneStateMoment
  refine iSup_le (fun u ↦ iSup_le (fun k ↦ iSup_le (fun hnorm ↦ iSup_le (fun hneg ↦ ?_))))
  have hu : IsOrthonormalFamily (fun _ : Fin 1 ↦ u) := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, hnorm]
  unfold negativeMoment
  apply le_iSup_of_le 1
  apply le_iSup_of_le (fun _ : Fin 1 ↦ u)
  apply le_iSup_of_le (fun _ : Fin 1 ↦ k)
  apply le_iSup_of_le hu
  apply le_iSup_of_le (fun _ : Fin 1 ↦ hneg)
  simp


-- @@ L503-511 verbatim
lemma oneStateConstant_le_optimalConstant (γ : ℝ) :
    oneStateConstant γ ≤ optimalConstant γ := by
  unfold oneStateConstant
  refine iSup_le (fun W ↦ iSup_le (fun hW ↦ iSup_le (fun hpos ↦ ?_)))
  unfold optimalConstant
  apply le_iSup_of_le W
  apply le_iSup_of_le hW
  apply le_iSup_of_le hpos
  exact ENNReal.div_le_div_right (oneStateMoment_le_negativeMoment γ W) _


-- @@ L513-513 verbatim
end SharpLiebThirring


-- @@ L515-515 verbatim
namespace SharpLiebThirring.ExtremizerProof

-- @@ L516-516 verbatim
open MeasureTheory


-- @@ L518-524 verbatim
lemma profile_norm_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ profile r x ^ 2) := by
  convert!
    (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)).integrable_mul
      (profile_memLp r hr (p := 2) (by norm_num) (by norm_num)) using 1
  funext x
  simp only [pow_two, Pi.mul_apply]


-- @@ L526-534 verbatim
lemma profile_norm_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ x : ℝ, profile r x ^ 2 := by
  apply (integral_pos_iff_support_of_nonneg (fun x ↦ sq_nonneg _) (profile_norm_integrable hr)).mpr
  have hs : Function.support (fun x : ℝ ↦ profile r x ^ 2) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (sq_pos_of_pos (profile_pos r x)).ne'
  rw [hs]
  simp


-- @@ L536-545 verbatim
lemma boundState_l2Pairing {r : ℝ} (hr : 0 < r) :
    l2Pairing (boundState r hr) (boundState r hr) =
      ((∫ x : ℝ, profile r x ^ 2) : ℝ) := by
  change (∫ x : ℝ, star (profile r x : ℂ) * (profile r x : ℂ)) = _
  have ht : (fun x : ℝ ↦ star (profile r x : ℂ) * (profile r x : ℂ)) =
      (fun x : ℝ ↦ ((profile r x ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp only [Complex.star_def, Complex.conj_ofReal, pow_two, Complex.ofReal_mul]
  rw [ht]
  exact integral_ofReal (𝕜 := ℂ)


-- @@ L547-548 verbatim
def normalizedBoundState (r : ℝ) (hr : 0 < r) : H1 :=
  scaleH1 (((Real.sqrt (∫ x : ℝ, profile r x ^ 2))⁻¹ : ℝ) : ℂ) (boundState r hr)


-- @@ L550-559 verbatim
lemma normalizedBoundState_norm {r : ℝ} (hr : 0 < r) :
    l2Pairing (normalizedBoundState r hr) (normalizedBoundState r hr) = 1 := by
  rw [normalizedBoundState, l2Pairing_scale_both, boundState_l2Pairing hr]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  norm_cast
  have hpos := profile_norm_pos hr
  have hs := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (∫ x : ℝ, profile r x ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp
  nlinarith


-- @@ L561-563 verbatim
lemma normalizedBoundState_eigenfunction {r : ℝ} (hr : 0 < r) :
    IsNegativeEigenfunction (potential r) 1 (normalizedBoundState r hr) :=
  (boundState_negativeEigenfunction hr).scale _


-- @@ L565-572 verbatim
lemma one_le_oneStateMoment {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    1 ≤ oneStateMoment γ (potential r) := by
  unfold oneStateMoment
  apply le_iSup_of_le (normalizedBoundState r hr)
  apply le_iSup_of_le 1
  apply le_iSup_of_le (normalizedBoundState_norm hr)
  apply le_iSup_of_le (normalizedBoundState_eigenfunction hr)
  simp


-- @@ L574-576 verbatim
lemma one_le_negativeMoment {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    1 ≤ negativeMoment γ (potential r) :=
  (one_le_oneStateMoment hr γ).trans (oneStateMoment_le_negativeMoment γ (potential r))


-- @@ L578-578 verbatim
end SharpLiebThirring.ExtremizerProof


-- @@ L580-580 verbatim
namespace SharpLiebThirring.ExtremizerProof

-- @@ L581-581 verbatim
open MeasureTheory Set Filter

-- @@ L582-582 verbatim
open scoped ENNReal Topology


-- @@ L584-594 verbatim
lemma memLp_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (fun x : ℝ ↦ Real.exp (-c * |x|)) p volume := by
  have hm : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|)) := by fun_prop
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable hp hp').mp
  have hi := integrable_exp_neg_abs (mul_pos hc (ENNReal.toReal_pos hp hp'))
  convert! hi using 1
  funext x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  ring


-- @@ L596-601 verbatim
lemma cosh_inv_exponential_bound (x : ℝ) :
    (Real.cosh x)⁻¹ ≤ 2 * Real.exp (-|x|) := by
  apply (inv_le_iff_one_le_mul₀ (Real.cosh_pos x)).mpr
  have hh := mul_le_mul_of_nonneg_right (cosh_lower_exponential x) (Real.exp_pos (-|x|)).le
  have he : Real.exp |x| * Real.exp (-|x|) = 1 := by rw [← Real.exp_add]; simp
  nlinarith


-- @@ L603-611 verbatim
lemma potential_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    potential r x ≤ 4 * (r + 1) * Real.exp (-(2*r) * |x|) := by
  have hi0 : 0 ≤ (Real.cosh (r*x))⁻¹ := inv_nonneg.mpr (Real.cosh_pos _).le
  have hh := pow_le_pow_left₀ hi0 (cosh_inv_exponential_bound (r*x)) 2
  have he : (2 * Real.exp (-|r*x|)) ^ 2 = 4 * Real.exp (-(2*r) * |x|) := by
    rw [mul_pow, ← Real.exp_nat_mul, abs_mul, abs_of_pos hr]
    congr 2 <;> ring
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r + 1)).trans_eq (by ring)


-- @@ L613-619 verbatim
lemma potential_memLp {r : ℝ} (hr : 0 < r) {p : ℝ≥0∞}
    (hp : p ≠ 0) (hp' : p ≠ ⊤) : MemLp (potential r) p volume := by
  apply ((memLp_exp_neg_mul_abs (by positivity : 0 < 2*r) hp hp').const_mul
    (4 * (r + 1))).mono' (potential_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (potential_nonneg hr x)]
    exact potential_exponential_bound hr x)


-- @@ L621-626 verbatim
lemma equalityPotential_admissible {γ : ℝ} (hγ : 1 / 2 < γ) :
    Admissible γ (equalityPotential γ) := by
  have hr : 0 < (γ - 1 / 2)⁻¹ := inv_pos.mpr (by linarith)
  constructor
  · exact Filter.Eventually.of_forall (fun x ↦ potential_nonneg hr x)
  · exact potential_memLp hr (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top


-- @@ L628-630 verbatim
lemma potential_pos {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 < potential r x := by
  unfold potential
  positivity


-- @@ L632-643 verbatim
lemma potential_mass_pos {γ r : ℝ} (hr : 0 < r) :
    0 < potentialMass γ (potential r) := by
  unfold potentialMass
  have hm : Measurable (fun x : ℝ ↦ (ENNReal.ofReal (potential r x)) ^ (γ + 1/2)) :=
    ((potential_continuous r).measurable.ennreal_ofReal).pow_const _
  apply (lintegral_pos_iff_support hm).mpr
  have hs : Function.support (fun x : ℝ ↦ (ENNReal.ofReal (potential r x)) ^ (γ + 1/2)) = Set.univ := by
    apply Function.support_eq_univ
    intro x
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (potential_pos hr x)) ENNReal.ofReal_ne_top).ne'
  rw [hs]
  simp


-- @@ L645-645 verbatim
end SharpLiebThirring.ExtremizerProof


-- @@ L647-647 verbatim
end

-- @@ L648-648 verbatim
end

-- @@ L649-649 verbatim
end


-- @@ L651-651 verbatim
end OAI
