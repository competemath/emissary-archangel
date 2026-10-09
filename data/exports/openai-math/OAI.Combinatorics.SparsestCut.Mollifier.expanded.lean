import OAI.Combinatorics.SparsestCut.Metric


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace UniformSparsestCut.ProductMollifier


-- @@ L12-12 verbatim
def bump : ContDiffBump (0:ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩

-- @@ L13-13 verbatim
def rho : ℝ → ℝ := bump.normed volume

-- @@ L14-14 verbatim
lemma rho_nonneg (x : ℝ) : 0 ≤ rho x := bump.nonneg_normed x

-- @@ L15-15 verbatim
lemma rho_integral : ∫ x, rho x = 1 := bump.integral_normed

-- @@ L16-16 verbatim
lemma rho_integrable : Integrable rho := bump.integrable_normed

-- @@ L17-17 verbatim
lemma rho_smooth : ContDiff ℝ (⊤:ℕ∞) rho := bump.contDiff_normed

-- @@ L18-18 verbatim
lemma rho_compact : HasCompactSupport rho := bump.hasCompactSupport_normed

-- @@ L19-19 verbatim
lemma rho_even (x : ℝ) : rho (-x) = rho x := bump.normed_neg x

-- @@ L20-23 verbatim
lemma rho_support {x : ℝ} (hx : rho x ≠ 0) : |x| < 1 := by
  have h : x ∈ Function.support rho := hx
  rw [rho,bump.support_normed_eq] at h
  simpa [bump,Metric.mem_ball,dist_eq_norm] using h

-- @@ L24-25 verbatim
lemma rho_deriv_integrable : Integrable (deriv rho) :=
  (rho_smooth.continuous_deriv (by simp)).integrable_of_hasCompactSupport rho_compact.deriv


-- @@ L27-27 verbatim
def density (ell : ℝ) (x : ℝ) : ℝ := ell⁻¹*rho (x/ell)

-- @@ L28-29 verbatim
lemma density_nonneg {ell : ℝ} (hell : 0 ≤ ell) (x : ℝ) : 0 ≤ density ell x := by
  exact mul_nonneg (inv_nonneg.mpr hell) (rho_nonneg _)

-- @@ L30-32 verbatim
lemma density_smooth (ell : ℝ) : ContDiff ℝ (⊤:ℕ∞) (density ell) := by
  unfold density
  exact contDiff_const.mul (rho_smooth.comp (contDiff_id.div_const ell))

-- @@ L33-36 verbatim
lemma density_integral {ell : ℝ} (hell : 0 < ell) : ∫ x, density ell x = 1 := by
  unfold density
  rw [integral_const_mul,Measure.integral_comp_div,rho_integral,smul_eq_mul,abs_of_pos hell]
  simp [hell.ne']

-- @@ L37-40 verbatim
lemma density_support {ell x : ℝ} (hell : 0 < ell) (hx : density ell x ≠ 0) : |x| < ell := by
  have hρ : rho (x/ell) ≠ 0 := by intro he; exact hx (by simp [density,he])
  have h := rho_support hρ
  rwa [abs_div,abs_of_pos hell,div_lt_one hell] at h

-- @@ L41-45 verbatim
lemma density_compact {ell : ℝ} (hell : 0 < ell) : HasCompactSupport (density ell) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -ell) (b := ell))
  intro x hx
  by_contra hn
  exact hx (abs_le.mp (density_support hell hn).le)

-- @@ L46-47 verbatim
lemma density_integrable {ell : ℝ} (hell : 0 < ell) : Integrable (density ell) :=
  (density_smooth ell).continuous.integrable_of_hasCompactSupport (density_compact hell)

-- @@ L48-53 verbatim
lemma density_hasDeriv {ell : ℝ} (x : ℝ) : HasDerivAt (density ell)
    (ell⁻¹/ell*deriv rho (x/ell)) x := by
  have hd := ((rho_smooth.differentiable (by simp) (x/ell)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const ell)).const_mul (ell⁻¹)
  convert hd using 1 <;> try rfl
  ring

-- @@ L54-59 verbatim
lemma density_deriv_integral {ell : ℝ} (hell : 0 < ell) :
    (∫ x, |deriv (density ell) x|) = ell⁻¹*(∫ x, |deriv rho x|) := by
  simp_rw [(density_hasDeriv (ell := ell) _).deriv,abs_mul,abs_of_pos (div_pos (inv_pos.mpr hell) hell)]
  rw [integral_const_mul]
  rw [Measure.integral_comp_div (fun t => |deriv rho t|),smul_eq_mul,abs_of_pos hell]
  field_simp


-- @@ L61-61 verbatim
variable {m : ℕ}

-- @@ L62-62 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L63-64 verbatim
def coordinate (i : Fin m) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap

-- @@ L65-65 verbatim
@[simp] lemma coordinate_apply (i : Fin m) (x : E) : coordinate i x = x i := rfl


-- @@ L67-67 verbatim
def kernel (φ : ℝ → ℝ) (x : E) : ℝ := ∏ i, φ (x i)

-- @@ L68-72 verbatim
lemma kernel_smooth (φ : ℝ → ℝ) {n : ℕ∞} (hc : ContDiff ℝ n φ) : ContDiff ℝ n (kernel (m := m) φ) := by
  unfold kernel
  apply contDiff_prod
  intro i _
  exact hc.comp (coordinate i).contDiff

-- @@ L73-74 verbatim
lemma kernel_nonneg {φ : ℝ → ℝ} (hn : ∀ t, 0 ≤ φ t) (x : E) : 0 ≤ kernel φ x :=
  Finset.prod_nonneg (fun _i _ => hn _)

-- @@ L75-77 verbatim
lemma kernel_integral (φ : ℝ → ℝ) : (∫ x : E, kernel φ x) = (∫ t, φ t)^m := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 _))]
  simpa only [kernel,Fintype.card_fin] using integral_fintype_prod_volume_eq_pow (ι := Fin m) φ

-- @@ L78-80 verbatim
lemma kernel_integrable {φ : ℝ → ℝ} (hi : Integrable φ) : Integrable (kernel (m := m) φ) := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integrable_comp_emb (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 _))]
  exact Integrable.fintype_prod (fun _ : Fin m => hi)


-- @@ L82-95 verbatim
lemma coordinate_norm_bound {R : ℝ} (hR : 0 ≤ R) (x : E) (hx : ∀ j, |x j| ≤ R) :
    ‖x‖ ≤ R*Real.sqrt m := by
  have hs : ‖x‖^2 ≤ (m:ℝ)*R^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, R^2 := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx j) _
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m)
  have hp : 0 ≤ R*Real.sqrt m := mul_nonneg hR (Real.sqrt_nonneg _)
  have he : (R*Real.sqrt m)^2 = (m:ℝ)*R^2 := by rw [mul_pow,hroot]; ring
  nlinarith [norm_nonneg x]


-- @@ L97-103 verbatim
lemma kernel_support_bound {φ : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hφ : ∀ t, φ t ≠ 0 → |t| ≤ R) {x : E} (hx : kernel φ x ≠ 0) : ‖x‖ ≤ R*Real.sqrt m := by
  apply coordinate_norm_bound hR x
  intro j
  apply hφ _
  intro hj
  exact hx (Finset.prod_eq_zero (Finset.mem_univ j) hj)


-- @@ L105-110 verbatim
lemma kernel_compact {φ : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hφ : ∀ t, φ t ≠ 0 → |t| ≤ R) : HasCompactSupport (kernel (m := m) φ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) (R*Real.sqrt m))
  intro x hx
  by_contra hn
  exact hx (by simpa using kernel_support_bound hR hφ hn)


-- @@ L112-118 verbatim
lemma kernel_hasFDeriv {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (x : E) :
    HasFDerivAt (kernel φ)
      (∑ i, ((∏ j ∈ Finset.univ.erase i, φ (x j))*φ' (x i)) • coordinate i) x := by
  have h (i : Fin m) : HasFDerivAt (fun x : E => φ (x i)) (φ' (x i) • coordinate i) x :=
    (hd (x i)).comp_hasFDerivAt x (coordinate i).hasFDerivAt
  convert! HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => h i) using 1
  simp only [smul_smul]


-- @@ L120-124 verbatim
lemma kernel_partial {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (x : E) (i : Fin m) :
    fderiv ℝ (kernel φ) x (EuclideanSpace.single i 1) =
      φ' (x i)*(∏ j ∈ Finset.univ.erase i, φ (x j)) := by
  rw [(kernel_hasFDeriv hd x).fderiv]
  simp [coordinate,mul_comm]


-- @@ L126-150 verbatim
lemma kernel_partial_integral {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hn : ∀ t, 0 ≤ φ t) (h1 : ∫ t, φ t = 1) (i : Fin m) :
    (∫ x : E, |fderiv ℝ (kernel φ) x (EuclideanSpace.single i 1)|) = ∫ t, |φ' t| := by
  classical
  simp_rw [kernel_partial hd,abs_mul,abs_of_nonneg (Finset.prod_nonneg (fun j _ => hn _))]
  let f : Fin m → ℝ → ℝ := fun j t => if j=i then |φ' t| else φ t
  have he (x : E) : |φ' (x i)| *(∏ j ∈ Finset.univ.erase i, φ (x j)) = ∏ j, f j (x j) := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) (fun j => f j (x j)) (Finset.mem_univ i)]
    simp only [f,ite_eq_left rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
    simp [hj]
  simp_rw [he]
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 _))]
  rw [integral_fintype_prod_volume_eq_prod]
  rw [← Finset.mul_prod_erase (s := Finset.univ) (fun j => ∫ t, f j t) (Finset.mem_univ i)]
  simp only [f,ite_eq_left rfl]
  have ho : (∏ j ∈ Finset.univ.erase i, ∫ t, if j=i then |φ' t| else φ t) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
    simpa [hj] using h1
  rw [ho,mul_one]


-- @@ L152-152 verbatim
end UniformSparsestCut.ProductMollifier


-- @@ L154-154 verbatim
end


-- @@ L156-156 verbatim
end OAI
