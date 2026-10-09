import OAI.Probability.GaussianPropeller.SpanReduction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uι


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

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L31-31 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L32-32 verbatim
open scoped RealInnerProductSpace Topology ENNReal


-- @@ L34-34 verbatim
open Metric

-- @@ L35-35 verbatim
namespace GaussianPropeller.Polar

-- @@ L36-36 verbatim
open Translation


-- @@ L38-38 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L39-39 verbatim
local notation "E" => EuclideanSpace ℝ ι

-- @@ L40-40 verbatim
local notation "S" => sphere (0 : E) 1

-- @@ L41-41 verbatim
local notation "V" => (volume : Measure E)


-- @@ L43-53 verbatim
lemma integral_volume_polar (f : E → ℝ) :
    ∫ x, f x = ∫ p : S × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
      ∂(V).toSphere.prod (Measure.volumeIoiPow (Fintype.card ι - 1)) := by
  have hh := (V).measurePreserving_homeomorphUnitSphereProd.integral_comp
    (homeomorphUnitSphereProd E).measurableEmbedding
    (fun p => f ((homeomorphUnitSphereProd E).symm p).val)
  simp only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
    finrank_euclideanSpace] at hh
  rw [integral_subtype_comap (measurableSet_singleton (0:E)).compl,
    restrict_compl_singleton] at hh
  exact hh


-- @@ L55-74 verbatim
lemma integral_stdGaussian_polar (f : E → ℝ) :
    ∫ x, f x ∂stdGaussian E = (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ p : S × Ioi (0 : ℝ), Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)
        ∂(V).toSphere.prod (Measure.volumeIoiPow (Fintype.card ι - 1)) := by
  rw [stdGaussian_density]
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul measurable_stdDensity.real_toNNReal]
  have heq : (fun x : E => (stdDensity x).toNNReal • f x) =
      fun x => stdDensity x * f x := by
    funext x
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (stdDensity_pos x).le, smul_eq_mul]
  rw [heq, integral_volume_polar, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [stdDensity_eq]
  have hn : ‖p.2.1 • p.1.1‖ = p.2.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.2,
      mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
  rw [hn]
  ring


-- @@ L76-88 verbatim
lemma integral_volumeIoiPow (d : ℕ) (g : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), g r.1 ∂Measure.volumeIoiPow d) =
      ∫ r in Ioi (0:ℝ), r^d * g r := by
  rw [Measure.volumeIoiPow]
  simp_rw [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (measurable_subtype_coe.pow_const d).real_toNNReal]
  have heq : (fun r : Ioi (0:ℝ) => (r.1^d).toNNReal • g r.1) =
      fun r => r.1^d * g r.1 := by
    funext r
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg r.2.le d), smul_eq_mul]
  rw [heq]
  exact integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^d * g r)


-- @@ L90-111 verbatim
lemma integral_homogeneous (f : E → ℝ) (q : ℕ)
    (hf : ∀ (r : ℝ), 0 < r → ∀ x, f (r • x) = r^q * f x) :
    ∫ x, f x ∂stdGaussian E =
      ((Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι - 1 + q) * Real.exp (-r^2/2)) *
      ∫ θ : S, f θ.1 ∂(V).toSphere := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)) =
      fun p => f p.1.1 * (p.2.1^q * Real.exp (-p.2.1^2/2)) := by
    funext p
    rw [hf _ p.2.2]
    ring
  rw [heq, integral_prod_mul (fun θ : S => f θ.1)
    (fun r : Ioi (0:ℝ) => r.1^q * Real.exp (-r.1^2/2)), integral_volumeIoiPow (Fintype.card ι - 1)
      (fun r : ℝ => r^q * Real.exp (-r^2/2))]
  have heq' : (fun r : ℝ => r^(Fintype.card ι-1) * (r^q * Real.exp (-r^2/2))) =
      fun r => r^(Fintype.card ι-1+q) * Real.exp (-r^2/2) := by
    funext r
    rw [pow_add]
    ring
  rw [heq']
  ring


-- @@ L113-113 verbatim
end GaussianPropeller.Polar


-- @@ L115-115 verbatim
namespace GaussianPropeller.Polar

-- @@ L116-116 verbatim
open Real

-- @@ L117-117 verbatim
noncomputable def radial (n : ℕ) (b : ℝ) : ℝ := ∫ r in Ioi (0:ℝ), r^n * exp (-b*r^2)


-- @@ L119-123 verbatim
lemma radial_eq (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = b ^ (-((n:ℝ)+1)/2) * (1/2) * Gamma (((n:ℝ)+1)/2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=n) (b:=b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hb
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_mul, radial] using hh


-- @@ L125-128 verbatim
lemma radial_integrable (n : ℕ) {b : ℝ} (hb : 0<b) :
    IntegrableOn (fun r : ℝ => r^n*exp (-b*r^2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hb (s:=(n:ℝ)) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  simpa only [Real.rpow_natCast] using h


-- @@ L130-133 verbatim
lemma radial_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<radial n b := by
  rw [radial_eq n hb]
  exact mul_pos (mul_pos (rpow_pos_of_pos hb _) (by norm_num))
    (Gamma_pos_of_pos (by positivity))


-- @@ L135-151 verbatim
lemma radial_scale (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = (sqrt (2*b))⁻¹ ^ (n+1) * radial n (1/2) := by
  have hp : 0<sqrt (2*b) := by positivity
  have hs := sq_sqrt (show 0≤2*b by positivity)
  have hh := integral_comp_mul_left_Ioi (fun r : ℝ => r^n*exp (-(1/2:ℝ)*r^2)) 0 hp
  rw [mul_zero] at hh
  have heq : (fun r : ℝ => (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) =
      fun r => sqrt (2*b)^n * (r^n*exp (-b*r^2)) := by
    funext r
    rw [mul_pow, show -(1/2:ℝ)*(sqrt (2*b)*r)^2 = -b*r^2 by rw [mul_pow,hs]; ring]
    ring
  change (∫ r in Ioi (0:ℝ), (sqrt (2*b)*r)^n * exp (-(1/2:ℝ)*(sqrt (2*b)*r)^2)) = _ at hh
  rw [heq, integral_const_mul] at hh
  change sqrt (2*b)^n*radial n b = (sqrt (2*b))⁻¹*radial n (1/2) at hh
  apply (mul_left_cancel₀ (pow_ne_zero n hp.ne'))
  rw [hh, pow_succ, mul_assoc, ← mul_assoc (sqrt (2*b)^n)]
  simp only [inv_pow, mul_inv_cancel₀ (pow_ne_zero n hp.ne'), one_mul]


-- @@ L153-154 verbatim
lemma radial_half_zero : radial 0 (1/2) = sqrt (2*Real.pi)/2 := by
  simpa [radial, sqrt_mul (by norm_num : (0:ℝ)≤2), mul_comm] using integral_gaussian_Ioi (1/2:ℝ)


-- @@ L156-158 verbatim
lemma radial_half_one : radial 1 (1/2) = 1 := by
  rw [radial_eq 1 (by norm_num)]
  norm_num


-- @@ L160-173 verbatim
lemma radial_half_two : radial 2 (1/2) = sqrt (2*Real.pi)/2 := by
  rw [radial_eq 2 (by norm_num)]
  have hg := Gamma_nat_add_one_add_half 0
  norm_num at hg ⊢
  rw [hg]
  rw [show (-((3:ℝ)/2))=-(1+(1/2:ℝ)) by ring, rpow_neg (by norm_num : (0:ℝ)≤1/2),
    rpow_add (by norm_num : (0:ℝ)<1/2), rpow_one, ← sqrt_eq_rpow]
  have h1 := sq_sqrt (by norm_num : (0:ℝ)≤1/2)
  have h2 := sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp1 := sqrt_pos.mpr (by norm_num : (0:ℝ)<1/2)
  have hp2 := sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have hh : sqrt (1/2:ℝ)*sqrt 2=1 := by rw [← sqrt_mul (by norm_num : (0:ℝ)≤1/2)]; norm_num
  field_simp
  nlinarith only [hh]


-- @@ L175-177 verbatim
lemma radial_half_three : radial 3 (1/2) = 2 := by
  rw [radial_eq 3 (by norm_num)]
  norm_num [Gamma_nat_eq_factorial, rpow_neg, rpow_natCast]


-- @@ L179-190 verbatim
lemma radial_half_four : radial 4 (1/2) = 3*sqrt (2*Real.pi)/2 := by
  have h2 := radial_half_two
  rw [radial_eq 2 (by norm_num)] at h2
  rw [radial_eq 4 (by norm_num)]
  have hg := Gamma_add_one (s:=(3/2:ℝ)) (by norm_num)
  norm_num at hg h2 ⊢
  rw [hg]
  have he : (1/2:ℝ)^(-((5:ℝ)/2)) = 2*(1/2:ℝ)^(-((3:ℝ)/2)) := by
    rw [show (-((5:ℝ)/2))=-(1:ℝ)+(-((3:ℝ)/2)) by ring, rpow_add (by norm_num : (0:ℝ)<1/2)]
    norm_num
  rw [he]
  nlinarith only [h2]


-- @@ L192-192 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L193-193 verbatim
local notation "E" => EuclideanSpace ℝ ι

-- @@ L194-194 verbatim
local notation "S" => Metric.sphere (0:E) 1


-- @@ L196-208 verbatim
lemma integral_radial (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      ((sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι * ∫ _ : S, (1:ℝ) ∂(volume : Measure E).toSphere) *
      ∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r := by
  rw [integral_stdGaussian_polar]
  have heq : (fun p : S × Ioi (0:ℝ) => exp (-p.2.1^2/2)*f ‖p.2.1•p.1.1‖) =
      fun p => (1:ℝ)*(exp (-p.2.1^2/2)*f p.2.1) := by
    funext p
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0<p.2.1 from p.2.2),
      mem_sphere_zero_iff_norm.mp p.1.2]
  rw [heq, integral_prod_mul (fun θ : S => (1:ℝ))
    (fun r : Ioi (0:ℝ) => exp (-r.1^2/2)*f r.1), integral_volumeIoiPow (Fintype.card ι-1) (fun r => exp (-r^2/2)*f r)]
  simp_rw [mul_assoc]


-- @@ L210-224 verbatim
lemma integral_radial_normalized (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂stdGaussian E =
      (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)*f r) /
      radial (Fintype.card ι-1) (1/2) := by
  have h1 := integral_radial (ι:=ι) (fun _ => (1:ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  have hi : (∫ r in Ioi (0:ℝ), r^(Fintype.card ι-1)*exp (-r^2/2)) = radial (Fintype.card ι-1) (1/2) := by
    unfold radial
    congr 1; funext r; congr 2; ring
  rw [hi] at h1
  rw [integral_radial]
  rw [← one_div_mul_eq_div]
  congr 1
  apply (eq_div_iff (radial_pos _ (by norm_num)).ne').mpr
  simpa using h1.symm


-- @@ L226-239 verbatim
lemma integral_norm_pow_exp (q : ℕ) {a : ℝ} (_ha : 0≤a) :
    ∫ x : E, ‖x‖^q*exp (-a*‖x‖^2) ∂stdGaussian E =
      radial (Fintype.card ι-1+q) (a+1/2)/radial (Fintype.card ι-1) (1/2) := by
  rw [integral_radial_normalized (fun r => r^q*exp (-a*r^2))]
  congr 1
  unfold radial
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [pow_add]
  rw [show r^(Fintype.card ι-1)*exp (-r^2/2)*(r^q*exp (-a*r^2)) =
    r^(Fintype.card ι-1)*r^q*(exp (-r^2/2)*exp (-a*r^2)) by ring, ← exp_add]
  congr 2
  ring


-- @@ L241-247 verbatim
lemma integral_norm (hd : Fintype.card ι = 3) :
    ∫ x : E, ‖x‖ ∂stdGaussian E = 4/sqrt (2*Real.pi) := by
  have h := integral_norm_pow_exp (ι:=ι) 1 (a:=0) (by norm_num)
  convert h using 1 <;> simp only [hd, zero_add, neg_zero, zero_mul, exp_zero, mul_one, pow_one,
    show (3-1+1:ℕ)=3 by decide, show (3-1:ℕ)=2 by decide,
    radial_half_three,radial_half_two]
  ring


-- @@ L249-249 verbatim
end GaussianPropeller.Polar


-- @@ L251-251 verbatim
end OAI
