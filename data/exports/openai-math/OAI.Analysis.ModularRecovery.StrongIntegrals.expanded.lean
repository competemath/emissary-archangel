import OAI.Analysis.ModularRecovery.KernelContinuity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Strong operator integrals and positivity under Gaussian integration. -/


-- @@ L7-7 verbatim
universe uE uX uY


-- @@ L9-9 verbatim
open Filter MeasureTheory Set

-- @@ L10-10 verbatim
open scoped Topology ComplexConjugate


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
open MeasureTheory Set Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
namespace BoundedRecovery

-- @@ L16-16 verbatim
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


-- @@ L18-27 verbatim
omit [CompleteSpace E] in
lemma integrable_smul_bounded_orbit {k : ℝ → ℂ} (hk : Integrable k)
    {F : ℝ → E} (hF : Continuous F) {C : ℝ} (hbound : ∀ t, ‖F t‖ ≤ C) :
    Integrable (fun t => k t • F t) := by
  apply (hk.norm.mul_const C).mono'
    (hk.aestronglyMeasurable.smul hF.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖k t • F t‖ ≤ ‖k t‖ * C
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)


-- @@ L29-38 verbatim
omit [CompleteSpace E] in
lemma norm_integral_smul_bounded_orbit {k : ℝ → ℂ} (hk : Integrable k)
    {F : ℝ → E} {C : ℝ} (hbound : ∀ t, ‖F t‖ ≤ C) :
    ‖∫ t, k t • F t‖ ≤ (∫ t, ‖k t‖) * C := by
  calc
    _ ≤ ∫ t, ‖k t‖ * C := norm_integral_le_of_norm_le (hk.norm.mul_const C)
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)))
    _ = _ := integral_mul_const C _


-- @@ L40-62 verbatim
def strongIntegral (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C) :
    E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ t, k t • F t h
      map_add' := by
        intro h g
        simp only [map_add, smul_add]
        exact integral_add
          (integrable_smul_bounded_orbit hk (hF h)
            (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))))
          (integrable_smul_bounded_orbit hk (hF g)
            (fun t => (F t).le_opNorm g |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))))
      map_smul' := by
        intro c h
        simp only [map_smul, smul_comm (k _) c]
        exact integral_smul c _ }
    ((∫ t, ‖k t‖) * C) (by
      intro h
      calc
        _ ≤ (∫ t, ‖k t‖) * (C * ‖h‖) := norm_integral_smul_bounded_orbit hk
          (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))
        _ = _ := (mul_assoc _ _ _).symm)


-- @@ L64-67 verbatim
omit [CompleteSpace E] in
@[simp] lemma strongIntegral_apply (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C) (h : E) :
    strongIntegral k hk F hF C hbound h = ∫ t, k t • F t h := rfl


-- @@ L69-78 verbatim
omit [CompleteSpace E] in
lemma norm_strongIntegral_le (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ‖F t‖ ≤ C) :
    ‖strongIntegral k hk F hF C hbound‖ ≤ (∫ t, ‖k t‖) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (integral_nonneg (fun _ => norm_nonneg _)) hC)
  intro h
  exact (norm_integral_smul_bounded_orbit hk
    (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))).trans_eq
      (mul_assoc _ _ _).symm


-- @@ L80-80 verbatim
end BoundedRecovery


-- @@ L82-82 verbatim
noncomputable section

-- @@ L83-83 verbatim
open MeasureTheory Set Filter

-- @@ L84-84 verbatim
open scoped Topology ComplexConjugate

-- @@ L85-85 verbatim
namespace BoundedRecovery


-- @@ L87-106 verbatim
lemma integral_comp_simple {X : Type uX} {Y : Type uY} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] (q : SimpleFunc X Y) (f : Y → E) :
    ∫ x, f (q x) ∂μ = ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • f y := by
  classical
  have he : (fun x => f (q x)) = fun x => ∑ y ∈ q.range,
      (q ⁻¹' {y}).indicator (fun _ => f y) x := by
    funext x
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro hn
      exact (hn (q.mem_range_self x)).elim
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_indicator (q.measurableSet_preimage _),setIntegral_const]
  · intro y _
    exact (integrable_const _).indicator (q.measurableSet_preimage _)


-- @@ L108-156 verbatim
lemma integral_positive_kernel {X : Type uX} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (x₀ : X) (μ : Measure X) [IsFiniteMeasure μ]
    (K : X → X → ℂ) (hcont : Continuous (fun p : X × X => K p.1 p.2))
    (C : ℝ) (hbound : ∀ x y, ‖K x y‖ ≤ C)
    (hpos : ∀ (n : Type uX) [Fintype n] (x : n → X) (c : n → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * K (x i) (x j)).re) :
    0 ≤ (∫ x, ∫ y, K x y ∂μ ∂μ).re := by
  classical
  let q (n : ℕ) : SimpleFunc X X := SimpleFunc.approxOn id measurable_id univ x₀ (mem_univ _) n
  have hq (x : X) : Tendsto (fun n => q n x) atTop (𝓝 x) := by
    exact SimpleFunc.tendsto_approxOn measurable_id (mem_univ x₀) (by simp)
  let F (n : ℕ) (p : X × X) : ℂ := K (q n p.1) (q n p.2)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) (μ.prod μ) :=
    (hcont.measurable.comp ((q n).measurable.comp measurable_fst |>.prodMk
      ((q n).measurable.comp measurable_snd))).aestronglyMeasurable
  have ht : Tendsto (fun n => ∫ p, F n p ∂μ.prod μ) atTop
      (𝓝 (∫ p : X × X, K p.1 p.2 ∂μ.prod μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C) hF
      (integrable_const C)
    · exact fun n => ae_of_all _ (fun p => hbound _ _)
    · exact ae_of_all _ (fun p => hcont.continuousAt.tendsto.comp ((hq p.1).prodMk_nhds (hq p.2)))
  have hfi (n : ℕ) : Integrable (F n) (μ.prod μ) :=
    (integrable_const C).mono' (hF n) (ae_of_all _ (fun _ => hbound _ _))
  have hki : Integrable (fun p : X × X => K p.1 p.2) (μ.prod μ) :=
    (integrable_const C).mono' hcont.aestronglyMeasurable (ae_of_all _ (fun _ => hbound _ _))
  rw [integral_prod _ hki] at ht
  apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
  apply Eventually.of_forall
  intro n
  change 0 ≤ (∫ p, F n p ∂μ.prod μ).re
  rw [integral_prod _ (hfi n)]
  change 0 ≤ (∫ x, ∫ y, K (q n x) (q n y) ∂μ ∂μ).re
  simp_rw [integral_comp_simple μ (q n)]
  rw [integral_comp_simple μ (q n) (fun x => ∑ y ∈ (q n).range, μ.real (q n ⁻¹' {y}) • K x y)]
  have hp := hpos (q n).range (fun i => (i:X))
    (fun i => (μ.real (q n ⁻¹' {(i:X)}):ℂ))
  simp only [Complex.conj_ofReal] at hp
  rw [Finset.sum_coe_sort (q n).range (fun i : X =>
    ∑ j : (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
      (μ.real (q n ⁻¹' {(j:X)}):ℂ) * K i j)] at hp
  have hs (i : X) : (∑ j : (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
      (μ.real (q n ⁻¹' {(j:X)}):ℂ) * K i j) =
      ∑ j ∈ (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
        (μ.real (q n ⁻¹' {j}):ℂ) * K i j :=
    Finset.sum_coe_sort (q n).range (fun j : X =>
      (μ.real (q n ⁻¹' {i}):ℂ) * (μ.real (q n ⁻¹' {j}):ℂ) * K i j)
  simp_rw [hs] at hp
  convert hp using 1
  simp only [Finset.smul_sum,Complex.real_smul,mul_assoc]


-- @@ L158-158 verbatim
end BoundedRecovery


-- @@ L160-160 verbatim
noncomputable section

-- @@ L161-161 verbatim
open Set Filter MeasureTheory ProbabilityTheory

-- @@ L162-162 verbatim
open scoped Topology ComplexConjugate NNReal

-- @@ L163-163 verbatim
namespace BoundedRecovery


-- @@ L165-178 verbatim
lemma gaussian_double_sub_integral {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (v : ℝ≥0) (f : ℝ → E)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C) :
    (∫ x, ∫ y, f (x-y) ∂gaussianReal 0 v ∂gaussianReal 0 v) =
      ∫ r, f r ∂gaussianReal 0 (v+v) := by
  have he (x : ℝ) : (∫ y, f (x-y) ∂gaussianReal 0 v) =
      ∫ y, f (x+y) ∂gaussianReal 0 v := by
    have ht := integral_map (μ := gaussianReal 0 v) (φ := fun y : ℝ => -y)
      (f := fun y => f (x+y)) (by fun_prop) (by fun_prop)
    simpa only [gaussianReal_map_neg,neg_zero,sub_eq_add_neg] using ht.symm
  simp_rw [he]
  rw [← integral_conv]
  · rw [gaussianReal_conv_gaussianReal,zero_add]
  · exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)


-- @@ L180-187 verbatim
lemma gaussian_positive_definite (v : ℝ≥0) (f : ℝ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hpos : ∀ (n : Type) [Fintype n] (r : n → ℝ) (c : n → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * f (r i-r j)).re) :
    0 ≤ (∫ r, f r ∂gaussianReal 0 (v+v)).re := by
  rw [← gaussian_double_sub_integral v f hf C hC]
  exact integral_positive_kernel 0 (gaussianReal 0 v) (fun x y => f (x-y))
    (hf.comp (continuous_fst.sub continuous_snd)) C (fun _ _ => hC _) hpos


-- @@ L189-189 verbatim
end BoundedRecovery


-- @@ L191-191 verbatim
noncomputable section

-- @@ L192-192 verbatim
open Set Filter MeasureTheory ProbabilityTheory

-- @@ L193-193 verbatim
open scoped Topology ComplexConjugate NNReal

-- @@ L194-194 verbatim
namespace BoundedRecovery


-- @@ L196-196 verbatim
def gaussianCutoff (n : ℕ) (r : ℝ) : ℝ := Real.exp (-r^2/(4*((n:ℝ)+1)))


-- @@ L198-198 verbatim
def gaussianVariance (n : ℕ) : ℝ≥0 := n+1


-- @@ L200-201 verbatim
def gaussianNormalization (n : ℕ) : ℝ :=
  (gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) 0)⁻¹


-- @@ L203-205 verbatim
lemma gaussianVariance_pos (n : ℕ) : 0 < gaussianVariance n := by
  unfold gaussianVariance
  positivity


-- @@ L207-209 verbatim
lemma gaussianNormalization_pos (n : ℕ) : 0 < gaussianNormalization n := by
  apply inv_pos.mpr
  exact gaussianPDFReal_pos _ _ _ (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)))


-- @@ L211-211 verbatim
lemma gaussianCutoff_pos (n : ℕ) (r : ℝ) : 0 < gaussianCutoff n r := Real.exp_pos _


-- @@ L213-215 verbatim
lemma gaussianCutoff_le_one (n : ℕ) (r : ℝ) : gaussianCutoff n r ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)


-- @@ L217-219 verbatim
lemma continuous_gaussianCutoff (n : ℕ) : Continuous (gaussianCutoff n) := by
  unfold gaussianCutoff
  fun_prop


-- @@ L221-227 verbatim
lemma integrable_gaussianCutoff (n : ℕ) : Integrable (gaussianCutoff n) := by
  have ht := integrable_exp_neg_mul_sq (by positivity : 0 < (4*((n:ℝ)+1))⁻¹)
  convert ht using 1
  ext r
  unfold gaussianCutoff
  congr 1
  ring


-- @@ L229-234 verbatim
lemma gaussianCutoff_tendsto (r : ℝ) : Tendsto (fun n => gaussianCutoff n r) atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ => 4*((n:ℝ)+1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have he := Real.continuous_exp.tendsto 0 |>.comp (tendsto_const_nhds.div_atTop hd :
    Tendsto (fun n : ℕ => -r^2/(4*((n:ℝ)+1))) atTop (𝓝 0))
  simpa only [gaussianCutoff,Real.exp_zero, Function.comp_def] using he


-- @@ L236-250 verbatim
lemma gaussianNormalization_pdf (n : ℕ) (r : ℝ) :
    gaussianNormalization n * gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) r =
      gaussianCutoff n r := by
  unfold gaussianNormalization gaussianPDFReal
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one]
  rw [inv_inv,mul_inv_cancel_left₀]
  · unfold gaussianCutoff
    congr 1
    simp only [gaussianVariance,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    congr 1
    ring
  · apply Real.sqrt_ne_zero'.mpr
    have hv : (0:ℝ) < (gaussianVariance n+gaussianVariance n:ℝ≥0) :=
      by exact_mod_cast add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)
    positivity


-- @@ L252-258 verbatim
lemma integral_gaussianCutoff_eq {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) :
    (∫ r, gaussianCutoff n r • f r) = gaussianNormalization n •
      ∫ r, f r ∂gaussianReal 0 (gaussianVariance n+gaussianVariance n) := by
  rw [integral_gaussianReal_eq_integral_smul
    (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n))), ← integral_smul]
  simp_rw [smul_smul,gaussianNormalization_pdf]


-- @@ L260-269 verbatim
lemma gaussianCutoff_positive_definite (n : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hpos : ∀ (ι : Type) [Fintype ι] (r : ι → ℝ) (c : ι → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * f (r i-r j)).re) :
    0 ≤ (∫ r, (gaussianCutoff n r:ℂ)*f r).re := by
  change 0 ≤ (∫ r, gaussianCutoff n r • f r).re
  rw [integral_gaussianCutoff_eq]
  rw [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (gaussianNormalization_pos n).le
    (gaussian_positive_definite (gaussianVariance n) f hf C hC hpos)


-- @@ L271-271 verbatim
end BoundedRecovery


-- @@ L273-273 verbatim
end

-- @@ L274-274 verbatim
end

-- @@ L275-275 verbatim
end

-- @@ L276-276 verbatim
end


-- @@ L278-278 verbatim
end OAI
