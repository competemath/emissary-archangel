import OAI.Geometry.PolarProducts.LensEstimates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u52 u53 u54


-- @@ L7-7 verbatim
section LowerBoundInline

-- @@ L8-8 verbatim
open Set Filter Function

-- @@ L9-9 verbatim
open scoped Topology ContDiff NNReal

-- @@ L10-10 verbatim
open Set Filter Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff

-- @@ L12-12 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L13-13 verbatim
open scoped Topology ContDiff NNReal

-- @@ L14-14 verbatim
open Set Filter Function

-- @@ L15-15 verbatim
open scoped Topology ContDiff

-- @@ L16-16 verbatim
open Set Filter Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff NNReal

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology ContDiff

-- @@ L20-20 verbatim
open Set Filter Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff

-- @@ L22-22 verbatim
open Set Filter Function

-- @@ L23-23 verbatim
open scoped ContDiff Topology

-- @@ L24-24 verbatim
open Set MeasureTheory

-- @@ L25-25 verbatim
open scoped ContDiff Interval Topology

-- @@ L26-26 verbatim
open Set

-- @@ L27-27 verbatim
open scoped Topology ContDiff

-- @@ L28-28 verbatim
open Set

-- @@ L29-29 verbatim
open Set MeasureTheory

-- @@ L30-30 verbatim
open scoped ContDiff Interval Topology

-- @@ L31-31 verbatim
open Set Filter Complex

-- @@ L32-32 verbatim
open scoped Topology ContDiff


-- @@ L34-34 verbatim
namespace SmoothPaths

-- @@ L35-35 verbatim
open Set Filter MeasureTheory

-- @@ L36-36 verbatim
open scoped Topology ContDiff

-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
universe u

-- @@ L40-42 verbatim
variable {E F : Type u} {H : Type u52} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]


-- @@ L44-45 verbatim
def integralPath : C(SmoothODE.Time, F) →L[ℝ] F :=
  (ContinuousMap.evalCLM ℝ ⟨1, by norm_num⟩).comp SmoothODE.primitiveCLM


-- @@ L47-48 verbatim
@[simp] theorem integralPath_apply (u : C(SmoothODE.Time, F)) :
    integralPath u = ∫ t in (0 : ℝ)..1, SmoothODE.extend u t := rfl


-- @@ L50-53 verbatim
theorem contDiff_integralPath {f : E → F} (hf : ContDiff ℝ ∞ f)
    (L : H →L[ℝ] C(SmoothODE.Time, E)) :
    ContDiff ℝ ∞ (fun z => integralPath (superpose hf.continuous (L z))) :=
  (integralPath (F := F)).contDiff.comp ((contDiff_superpose hf).comp L.contDiff)


-- @@ L55-55 verbatim
end

-- @@ L56-56 verbatim
end SmoothPaths


-- @@ L58-58 verbatim
namespace SmoothExtension

-- @@ L59-59 verbatim
open Set Filter

-- @@ L60-60 verbatim
open scoped Topology ContDiff Manifold

-- @@ L61-61 verbatim
noncomputable section


-- @@ L63-64 verbatim
variable {E : Type u53} {F : Type u54} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L66-83 verbatim
theorem exists_global_near_closed {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ f₁ : E → F, ContDiff ℝ ∞ f₁ ∧ f₁ =ᶠ[𝓝ˢ K] f := by
  obtain ⟨b, hb0, hb1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK
    (disjoint_left.mpr (by intro x hx hxK; exact hx (hKU hxK))) (n := ⊤)
  have hb : ContDiff ℝ ∞ b := contMDiff_iff_contDiff.mp b.contMDiff
  refine ⟨fun x => b x • f x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hh : ∀ᶠ y in 𝓝 x, b y = 0 := hb0.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hh] with y hy
      simp [hy]
  · filter_upwards [hb1] with x hx
    simp [hx]


-- @@ L85-85 verbatim
end

-- @@ L86-86 verbatim
end SmoothExtension


-- @@ L88-88 verbatim
namespace PlanarLens

-- @@ L89-89 verbatim
open Set Filter Complex MeasureTheory

-- @@ L90-90 verbatim
open scoped Topology ContDiff

-- @@ L91-91 verbatim
noncomputable section


-- @@ L93-93 verbatim
def density (k : ℕ) (z : ℂ) : ℝ := ‖g z‖^(2*k-2) * ‖deriv g z‖^2


-- @@ L95-95 verbatim
def J (k : ℕ) (v t : ℝ) : ℝ := (k : ℝ)^2 * ∫ h in 0..v, density k ((h : ℂ)+(t : ℂ)*I)


-- @@ L97-98 verbatim
theorem density_nonneg (k : ℕ) (z : ℂ) : 0 ≤ density k z := by
  unfold density; positivity


-- @@ L100-110 verbatim
theorem contDiffOn_density (k : ℕ) : ContDiffOn ℝ ∞ (density k) D := by
  have hg : ContDiffOn ℝ ∞ g D := (analyticOnNhd_g.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have hd : ContDiffOn ℝ ∞ (deriv g) D :=
    (analyticOnNhd_g.deriv.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have he : density k = fun z => (‖g z‖^2)^(k-1) * ‖deriv g z‖^2 := by
    funext z
    simp only [density, ← pow_mul]
    congr 2
    omega
  rw [he]
  exact ((hg.norm_sq ℂ).pow (k-1)).mul (hd.norm_sq ℂ)


-- @@ L112-113 verbatim
theorem continuousOn_density (k : ℕ) : ContinuousOn (density k) D :=
  (contDiffOn_density k).continuousOn


-- @@ L115-120 verbatim
theorem integrable_density {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume 0 v := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_density k).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem_signed hz hh


-- @@ L122-134 verbatim
theorem hasDerivAt_J {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    HasDerivAt (fun v => J k v t) ((k : ℝ)^2*density k ((v : ℂ)+(t : ℂ)*I)) v := by
  have hc : ContinuousAt (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v :=
    ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hz)).comp (f := fun h : ℝ => (h : ℂ)+(t : ℂ)*I)
      (show ContinuousAt (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) v from by fun_prop)
  have hm : StronglyMeasurableAtFilter
      (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (𝓝 v) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter
      (isOpen_D.preimage (show Continuous (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) from by fun_prop))
      (fun h hh => ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hh)).comp (f := fun a : ℝ => (a : ℂ)+(t : ℂ)*I)
        (show ContinuousAt (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) h from by fun_prop))
      v hz
  exact (intervalIntegral.integral_hasDerivAt_right (integrable_density hz k) hm hc).const_mul _


-- @@ L136-136 verbatim
@[simp] theorem J_zero (k : ℕ) (t : ℝ) : J k 0 t = 0 := by simp [J]


-- @@ L138-140 verbatim
theorem J_nonneg {v t : ℝ} (hv : 0 ≤ v) (k : ℕ) : 0 ≤ J k v t := by
  apply mul_nonneg (sq_nonneg _)
  exact intervalIntegral.integral_nonneg hv (fun _ _ => density_nonneg _ _)


-- @@ L142-158 verbatim
def horizontalPath : ℂ →L[ℝ] C(SmoothODE.Time, ℂ) := by
  let L : ℂ →ₗ[ℝ] C(SmoothODE.Time, ℂ) :=
    { toFun := fun z => ⟨fun a => ((a : ℝ)*z.re : ℝ) + (z.im : ℂ)*I, by fun_prop⟩
      map_add' := by intro z w; ext a; simp; ring
      map_smul' := by intro c z; ext a; simp; ring }
  apply L.mkContinuous 2
  intro z
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖(((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I‖ ≤ _
  calc
    _ ≤ ‖(((a : ℝ)*z.re : ℝ) : ℂ)‖ + ‖(z.im : ℂ)*I‖ := norm_add_le _ _
    _ = |(a : ℝ)| * |z.re| + |z.im| := by simp
    _ ≤ |z.re| + |z.im| := by
      rw [abs_of_nonneg a.2.1]
      nlinarith [a.2.2, abs_nonneg z.re]
    _ ≤ 2*‖z‖ := by linarith [abs_re_le_norm z, abs_im_le_norm z]


-- @@ L160-161 verbatim
@[simp] theorem horizontalPath_apply (z : ℂ) (a : SmoothODE.Time) :
    horizontalPath z a = (((a : ℝ)*z.re : ℝ) : ℂ)+(z.im : ℂ)*I := rfl


-- @@ L163-169 verbatim
theorem J_affine (k : ℕ) (v t : ℝ) :
    J k v t = (k : ℝ)^2*v*∫ a in (0 : ℝ)..1, density k (((a*v : ℝ) : ℂ)+(t : ℂ)*I) := by
  rw [J, mul_assoc]
  congr 1
  have hh := intervalIntegral.smul_integral_comp_mul_right
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v (a := 0) (b := 1)
  simpa only [smul_eq_mul, zero_mul, one_mul] using hh.symm


-- @@ L171-208 verbatim
theorem contDiffOn_J (k : ℕ) : ContDiffOn ℝ ∞ (fun z : ℂ => J k z.re z.im) D := by
  intro z hz
  let C := (fun a : ℝ => (((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)) '' Icc (0 : ℝ) 1
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCD : C ⊆ D := by
    rintro _ ⟨a, ha, rfl⟩
    apply horizontal_segment_mem_signed (v := z.re) (t := z.im)
      (by simpa only [re_add_im] using hz)
    by_cases hv : 0 ≤ z.re
    · rw [uIcc_of_le hv]
      constructor <;> nlinarith [ha.1, ha.2]
    · rw [uIcc_of_ge (le_of_not_ge hv)]
      constructor <;> nlinarith [ha.1, ha.2]
  obtain ⟨f, hf, he⟩ := SmoothExtension.exists_global_near_closed isOpen_D hCc.isClosed hCD
    (contDiffOn_density k)
  have hglob : ContDiff ℝ ∞ (fun w : ℂ =>
      (k : ℝ)^2*w.re*SmoothPaths.integralPath (SmoothPaths.superpose hf.continuous (horizontalPath w))) :=
    (contDiff_const.mul Complex.reCLM.contDiff).mul
      (SmoothPaths.contDiff_integralPath hf horizontalPath)
  have heq : ∀ᶠ w in 𝓝 z, ∀ a ∈ Icc (0 : ℝ) 1,
      f ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) = density k ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro a ha
    have hs : ∀ᶠ y in 𝓝 ((((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)), f y = density k y :=
      he.filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ ha))
    exact (show ContinuousAt (fun p : ℂ×ℝ => (((p.2*p.1.re : ℝ) : ℂ)+(p.1.im : ℂ)*I)) (z,a)
      from by fun_prop) hs
  apply ContDiffAt.contDiffWithinAt
  apply hglob.contDiffAt.congr_of_eventuallyEq
  filter_upwards [heq] with w hw
  rw [J_affine, SmoothPaths.integralPath_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
  have hp : projIcc (0 : ℝ) 1 zero_le_one a = ⟨a, ha⟩ := by exact projIcc_of_mem zero_le_one ha
  simp only [SmoothODE.extend, hp, SmoothPaths.superpose_apply, horizontalPath_apply]
  exact (hw a ha).symm


-- @@ L210-210 verbatim
end

-- @@ L211-211 verbatim
end PlanarLens


-- @@ L213-213 verbatim
namespace PlanarLens

-- @@ L214-214 verbatim
open Set Filter Complex MeasureTheory

-- @@ L215-215 verbatim
open scoped Topology ContDiff

-- @@ L216-216 verbatim
noncomputable section


-- @@ L218-218 verbatim
def rho (t h : ℝ) : ℝ := ‖g ((h : ℂ)+(t : ℂ)*I)‖

-- @@ L219-220 verbatim
def rhoD (t h : ℝ) : ℝ := A (g ((h : ℂ)+(t : ℂ)*I)) /
  (rho t h * ‖deriv F (g ((h : ℂ)+(t : ℂ)*I))‖^2)


-- @@ L222-227 verbatim
theorem rho_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rho t h := by
  apply norm_pos_iff.mpr
  intro he
  have hre := re_g_pos hz (by simpa using hh)
  rw [he] at hre
  simp at hre


-- @@ L229-239 verbatim
theorem hasDerivAt_rho {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    HasDerivAt (rho t) (rhoD t h) h := by
  have hn := rho_pos hz hh
  have hd := (horizontal_normSq_deriv hz).sqrt (ne_of_gt (sq_pos_of_pos hn))
  have he : (fun x : ℝ => Real.sqrt (‖g ((x : ℂ)+(t : ℂ)*I)‖^2)) = rho t := by
    funext x; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hd
  convert hd using 1
  rw [Real.sqrt_sq (norm_nonneg _)]
  dsimp [rhoD, rho]
  ring


-- @@ L241-243 verbatim
theorem rhoD_pos {t h : ℝ} (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) : 0 < rhoD t h := by
  apply div_pos (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  exact mul_pos (rho_pos hz hh) (sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))))


-- @@ L245-249 verbatim
theorem continuousOn_rho {t v : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hv : 0 ≤ v) :
    ContinuousOn (rho t) (Icc 0 v) := by
  apply (continuousOn_g.norm).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem hz hv hh


-- @@ L251-264 verbatim
theorem density_radial {k : ℕ} (hk : 1 ≤ k) {t h : ℝ}
    (hz : (h : ℂ)+(t : ℂ)*I ∈ D) (hh : 0 < h) :
    density k ((h : ℂ)+(t : ℂ)*I) =
      (rho t h)^(2*k-1) * (1/A (g ((h : ℂ)+(t : ℂ)*I))) * rhoD t h := by
  have hA := ne_of_gt (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hh)))
  have hr := ne_of_gt (rho_pos hz hh)
  have hF := norm_ne_zero_iff.mpr (deriv_F_ne_zero (norm_g_lt hz))
  have he : deriv g ((h : ℂ)+(t : ℂ)*I) = (deriv F (g ((h : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [density, he, norm_inv]
  rw [show 2*k-1 = (2*k-2)+1 by omega, pow_succ]
  dsimp [rhoD, rho] at *
  field_simp
  rw [pow_succ]


-- @@ L266-272 verbatim
theorem deriv_F_neg {w : ℂ} (hw : ‖w‖ < 1) : deriv F (-w) = deriv F w := by
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  congr 1
  apply tsum_congr
  intro n
  simp only [termDeriv]
  rw [(show Even (2*n) from ⟨n, by omega⟩).neg_pow]


-- @@ L274-282 verbatim
theorem deriv_F_conj {w : ℂ} (hw : ‖w‖ < 1) :
    deriv F ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv F w) := by
  have he : (fun n : ℕ => termDeriv n ((starRingEnd ℂ) w)) =
      fun n : ℕ => conjCLE (termDeriv n w) := by
    funext n
    simp [termDeriv, map_ofNat]
  rw [(hasDerivAt_F (by simpa using hw)).deriv, (hasDerivAt_F hw).deriv]
  simp only [he, ← conjCLE.map_tsum]
  simp [map_ofNat]


-- @@ L284-290 verbatim
theorem density_neg_conj {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    density k (-(starRingEnd ℂ) z) = density k z := by
  have hd (w : ℂ) (hw : w ∈ D) : deriv g w = (deriv F (g w))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hw), F_g hw]
  rw [density, density, hd _ (neg_conj_mem_D hz), hd _ hz, g_neg_conj hz,
    deriv_F_neg (by simpa using norm_g_lt hz), deriv_F_conj (norm_g_lt hz)]
  simp


-- @@ L292-308 verbatim
theorem J_neg {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    J k (-v) t = -J k v t := by
  have he (h : ℝ) : -(starRingEnd ℂ) ((h : ℂ)+(t : ℂ)*I) = ((-h : ℝ) : ℂ)+(t : ℂ)*I := by
    apply Complex.ext <;> simp
  have hsub := intervalIntegral.integral_comp_neg
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (a := 0) (b := v)
  simp only [neg_zero] at hsub
  have hi : (∫ h in (0 : ℝ)..v, density k (((-h : ℝ) : ℂ)+(t : ℂ)*I)) =
      ∫ h in (0 : ℝ)..v, density k ((h : ℂ)+(t : ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro h hh
    dsimp only
    rw [← he, density_neg_conj (horizontal_segment_mem_signed hz hh)]
  rw [hi, intervalIntegral.integral_symm (a := 0) (b := -v)] at hsub
  rw [J, J, ← mul_neg]
  congr 1
  linarith


-- @@ L310-310 verbatim
end

-- @@ L311-311 verbatim
end PlanarLens


-- @@ L313-313 verbatim
end LowerBoundInline


-- @@ L315-315 verbatim
end OAI
