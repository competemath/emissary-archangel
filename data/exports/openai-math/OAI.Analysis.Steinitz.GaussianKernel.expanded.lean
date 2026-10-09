import OAI.Analysis.Steinitz.Survival


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Diagonal Gaussian kernels and their densities. -/


-- @@ L7-7 verbatim
section


-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory Set WithLp

-- @@ L10-10 verbatim
open scoped ENNReal NNReal

-- @@ L11-11 verbatim
namespace GaussianKernel


-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-16 verbatim
noncomputable def diagonalLaw (v : ι → ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun i => gaussianReal 0 (v i))).map (toLp 2)


-- @@ L18-21 verbatim
instance (v : ι → ℝ≥0) : IsProbabilityMeasure (diagonalLaw v) :=
  by
  unfold diagonalLaw
  infer_instance


-- @@ L23-24 verbatim
noncomputable def density (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 (v i) (x i)


-- @@ L26-27 verbatim
lemma density_nonneg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : 0 ≤ density v x := by
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i)


-- @@ L29-31 verbatim
lemma density_continuous (v : ι → ℝ≥0) : Continuous (density v) := by
  unfold density gaussianPDFReal
  fun_prop


-- @@ L33-47 verbatim
lemma pi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (Measure.pi fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      ((show Integrable (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 (v i) (x i)) volume from
        by simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))).restrict)
      (ae_of_all _ fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i))),
    volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 (v i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (hv i) (s i)).symm


-- @@ L49-64 verbatim
lemma diagonalLaw_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalLaw v = volume.withDensity (fun x => ENNReal.ofReal (density v x)) := by
  apply Measure.ext
  intro s hs
  rw [diagonalLaw, Measure.map_apply (PiLp.volume_preserving_toLp ι).measurable hs,
    pi_density v hv, withDensity_apply _ (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    ← lintegral_indicator hs]
  have he (x : ι → ℝ) :
      ((toLp 2) ⁻¹' s).indicator (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) x =
      s.indicator (fun x => ENNReal.ofReal (density v x)) (toLp 2 x) := by
    by_cases hx : toLp 2 x ∈ s <;> simp [hx, density]
  simp_rw [he]
  exact (PiLp.volume_preserving_toLp ι).lintegral_comp
    ((density_continuous v).measurable.ennreal_ofReal.indicator hs)


-- @@ L66-68 verbatim
lemma density_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (x : EuclideanSpace ℝ ι) :
    0 < density v x := by
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 (v i) (x i) (hv i)


-- @@ L70-74 verbatim
lemma density_neg (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v (-x) = density v x := by
  unfold density
  apply Finset.prod_congr rfl
  intro i _
  simp [gaussianPDFReal]


-- @@ L76-86 verbatim
lemma density_le_zero (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : density v x ≤ density v 0 := by
  unfold density
  apply Finset.prod_le_prod₀
  · intro i _
    exact gaussianPDFReal_nonneg _ _ _
  · intro i _
    simp only [gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, Real.exp_zero, mul_one]
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)


-- @@ L88-96 verbatim
lemma charFun_diagonalLaw (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) :
    charFun (diagonalLaw v) ξ = (Real.exp (-(∑ i, (v i : ℝ)*(ξ i)^2)/2) : ℂ) := by
  rw [diagonalLaw, charFun_pi]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Finset.sum_neg_distrib]
  rw [← Finset.sum_div, neg_div]


-- @@ L98-98 verbatim
section Scale

-- @@ L99-99 verbatim
variable [DecidableEq ι]


-- @@ L101-102 verbatim
noncomputable def scaleMap (v : ι → ℝ≥0) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ)))


-- @@ L104-107 verbatim
lemma scaleMap_apply (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) (i : ι) :
    scaleMap v x i = Real.sqrt (v i : ℝ) * x i := by
  change (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ))).mulVec x.ofLp i = _
  simp only [Matrix.mulVec_diagonal]


-- @@ L109-127 verbatim
lemma stdGaussian_map_scale (v : ι → ℝ≥0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v) = diagonalLaw v := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (scaleMap v).measurable
    (PiLp.volume_preserving_toLp ι).measurable]
  have he : (scaleMap v) ∘ (toLp 2) =
      (toLp 2) ∘ (fun x : ι → ℝ => fun i => Real.sqrt (v i : ℝ)*x i) := by
    ext x i
    exact scaleMap_apply v (toLp 2 x) i
  rw [he, ← Measure.map_map (PiLp.volume_preserving_toLp ι).measurable (by fun_prop),
    Measure.pi_map_pi (f := fun i (x : ℝ) => Real.sqrt (v i : ℝ)*x)
      (fun i => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  apply congrArg Measure.pi
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (v i).coe_nonneg]


-- @@ L129-129 verbatim
end Scale


-- @@ L131-131 verbatim
end GaussianKernel

-- @@ L132-132 verbatim
open MeasureTheory ProbabilityTheory Set WithLp

-- @@ L133-133 verbatim
open scoped ENNReal NNReal

-- @@ L134-134 verbatim
namespace GaussianKernel

-- @@ L135-135 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L137-141 verbatim
lemma density_exp (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density v x = density v 0 * Real.exp (-(∑ i, (x i)^2 / (2*(v i : ℝ)))) := by
  simp only [density, gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero, mul_one,
    Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]


-- @@ L143-143 verbatim
end GaussianKernel


-- @@ L145-145 verbatim
end


-- @@ L147-147 verbatim
section


-- @@ L149-149 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L150-150 verbatim
open scoped ENNReal NNReal

-- @@ L151-151 verbatim
namespace GaussianKernel

-- @@ L152-152 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L154-158 verbatim
lemma density_integrable (v : ι → ℝ≥0) : Integrable (density v) := by
  apply ((PiLp.volume_preserving_toLp ι).integrable_comp
    (density_continuous v).aestronglyMeasurable).mp
  change Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal 0 (v i) (x i))
  simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))


-- @@ L160-163 verbatim
lemma stdGaussian_eq_density : stdGaussian (EuclideanSpace ℝ ι) =
    volume.withDensity (fun x => ENNReal.ofReal (density (fun _ : ι => 1) x)) := by
  rw [← diagonalLaw_density (fun _ : ι => 1) (fun _ => by simp)]
  exact map_pi_eq_stdGaussian.symm


-- @@ L165-173 verbatim
lemma linear_image_density (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) :
    (stdGaussian (EuclideanSpace ℝ ι)).map e S =
      ENNReal.ofReal (∫ x in S, |e.symm.toContinuousLinearMap.det| *
        density (fun _ => 1) (e.symm x)) := by
  rw [stdGaussian_eq_density]
  exact e.symm.toHomeomorph.toMeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    volume hS (ae_of_all _ fun _ _ => density_nonneg _ _) (density_integrable _).integrableOn
    (fun x _ => e.symm.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)


-- @@ L175-175 verbatim
end GaussianKernel


-- @@ L177-177 verbatim
end


-- @@ L179-179 verbatim
end OAI
