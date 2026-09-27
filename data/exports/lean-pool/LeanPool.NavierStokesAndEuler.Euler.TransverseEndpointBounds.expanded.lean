/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointParameter
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey


-- @@ L12-16 verbatim
/-!
Coefficient-only estimates for the nonzero-terminal transverse construction.
Both primitives, the actual affine trial, and the fixed-coordinate form are
estimated in their genuine Bochner and operator norms.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section



-- @@ L24-24 verbatim
namespace EulerTransverseEndpointBounds


-- @@ L26-32 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeH1FrameTransport
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerTransverseVariationalInverse EulerTransverseFixedSpaceInverse
  EulerTransverseEndpointEnergy EulerTransverseFixedEndpoint
  EulerTransverseEndpointParameter EulerCoerciveProjection


-- @@ L34-37 verbatim
variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L39-39 verbatim
variable (T : ℝ) (hT : 0 ≤ T)


-- @@ L41-48 verbatim
omit [CompleteSpace E] in
theorem initialPrimitive_norm_le_time : ‖initialPrimitiveTimeLp (E := E) T hT‖ ≤ T := by
  apply opNorm_le_bound _ hT
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))).1
  rw [mul_pow]
  exact (initialPrimitiveTimeLp_norm_sq_le T hT u).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg T]) (sq_nonneg ‖u‖))


-- @@ L50-61 verbatim
omit [CompleteSpace U] in
theorem constantFieldOperator_norm_le : ‖constantFieldOperator (E := U) T hT‖ ≤ 1 + T := by
  apply opNorm_le_bound _ (by linarith)
  intro u
  have he : ‖constantFieldOperator T hT u‖ ^ 2 = T * ‖u‖ ^ 2 := by
    change ‖pathLp T hT (ContinuousMap.const _ u)‖ ^ 2 = _
    rw [pathLp_norm_sq]
    simp only [extendPath, ContinuousMap.const_apply, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).1
  rw [he, mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg T, hT]) (sq_nonneg ‖u‖)


-- @@ L63-68 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem multiplier_sub_norm_le (A B : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖timeMultiplier T hT A - timeMultiplier T hT B‖ ≤ ‖A-B‖ := by
  change ‖coefficientMap T hT A - coefficientMap T hT B‖ ≤ _
  rw [← map_sub]
  exact timeMultiplier_norm T hT (A-B)


-- @@ L70-77 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem product_norm_le (J : TimeLp T U →L[ℝ] TimeLp T U) (hJ : ‖J‖ ≤ T)
    (A A₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖(timeMultiplier T hT A₁).comp J + timeMultiplier T hT A‖ ≤ T * ‖A₁‖ + ‖A‖ := by
  apply ((norm_add_le _ _).trans (add_le_add ((opNorm_comp_le _ _).trans
    (mul_le_mul (timeMultiplier_norm T hT A₁) hJ (by positivity) (by positivity)))
      (timeMultiplier_norm T hT A))).trans_eq
  ring


-- @@ L79-97 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem product_sub_norm_le (J : TimeLp T U →L[ℝ] TimeLp T U) (hJ : ‖J‖ ≤ T)
    (A A₁ B B₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖((timeMultiplier T hT A₁).comp J + timeMultiplier T hT A) -
      ((timeMultiplier T hT B₁).comp J + timeMultiplier T hT B)‖ ≤
        T * ‖A₁-B₁‖ + ‖A-B‖ := by
  have he : ((timeMultiplier T hT A₁).comp J + timeMultiplier T hT A) -
      ((timeMultiplier T hT B₁).comp J + timeMultiplier T hT B) =
      ((timeMultiplier T hT A₁ - timeMultiplier T hT B₁).comp J) +
        (timeMultiplier T hT A - timeMultiplier T hT B) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [comp_apply, add_apply, sub_apply]
    abel
  rw [he]
  apply ((norm_add_le _ _).trans (add_le_add ((opNorm_comp_le _ _).trans
    (mul_le_mul (multiplier_sub_norm_le T hT A₁ B₁) hJ (by positivity) (by positivity)))
      (multiplier_sub_norm_le T hT A B))).trans_eq
  ring


-- @@ L99-107 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem fixedFrameDerivative_norm_le (A A₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖fixedFrameDerivative T hT A A₁‖ ≤ T * ‖A₁‖ + ‖A‖ := by
  apply (opNorm_comp_le _ _).trans
  have h := mul_le_mul
    (product_norm_le T hT (primitiveTimeLp T hT) (primitive_norm_le_time T hT) A A₁)
    (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le
    (by positivity) (by positivity)
  simpa only [mul_one, productDerivative] using h


-- @@ L109-120 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem fixedFrameDerivative_sub_norm_le (A A₁ B B₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖fixedFrameDerivative T hT A A₁ - fixedFrameDerivative T hT B B₁‖ ≤
      T * ‖A₁-B₁‖ + ‖A-B‖ := by
  change ‖(productDerivative T hT A A₁).comp _ - (productDerivative T hT B B₁).comp _‖ ≤ _
  rw [← sub_comp]
  apply (opNorm_comp_le _ _).trans
  have h := mul_le_mul
    (product_sub_norm_le T hT (primitiveTimeLp T hT) (primitive_norm_le_time T hT) A A₁ B B₁)
    (zeroTraceDerivatives (U := U) T hT).norm_subtypeL_le
    (by positivity) (by positivity)
  simpa only [mul_one, productDerivative] using h


-- @@ L122-129 verbatim
theorem potential_norm_le (J : TimeLp T E →L[ℝ] TimeLp T E) (hJ : ‖J‖ ≤ T)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖J.adjoint.comp ((timeMultiplier T hT H).comp J)‖ ≤ T ^ 2 * ‖H‖ := by
  have hi := (opNorm_comp_le (timeMultiplier T hT H) J).trans
    (mul_le_mul (timeMultiplier_norm T hT H) hJ (by positivity) (by positivity))
  apply ((opNorm_comp_le _ _).trans (mul_le_mul
    (by simpa only [LinearIsometryEquiv.norm_map] using hJ) hi (norm_nonneg _) hT)).trans_eq
  ring


-- @@ L131-134 verbatim
theorem dirichlet_norm_le (J : TimeLp T E →L[ℝ] TimeLp T E) (hJ : ‖J‖ ≤ T)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖dirichletOperator J (timeMultiplier T hT H)‖ ≤ 1 + T ^ 2 * ‖H‖ :=
  (norm_sub_le _ _).trans (add_le_add norm_id_le (potential_norm_le T hT J hJ H))


-- @@ L136-149 verbatim
theorem dirichlet_sub_norm_le (J : TimeLp T E →L[ℝ] TimeLp T E) (hJ : ‖J‖ ≤ T)
    (H H' : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖dirichletOperator J (timeMultiplier T hT H) -
      dirichletOperator J (timeMultiplier T hT H')‖ ≤ T ^ 2 * ‖H-H'‖ := by
  have he : dirichletOperator J (timeMultiplier T hT H) -
      dirichletOperator J (timeMultiplier T hT H') =
      -(J.adjoint.comp ((timeMultiplier T hT (H-H')).comp J)) := by
    change (ContinuousLinearMap.id ℝ _ - J.adjoint.comp ((coefficientMap T hT H).comp J)) -
      (ContinuousLinearMap.id ℝ _ - J.adjoint.comp ((coefficientMap T hT H').comp J)) = _
    change _ = -(J.adjoint.comp ((coefficientMap T hT (H-H')).comp J))
    rw [map_sub, sub_comp, comp_sub]
    abel
  rw [he, norm_neg]
  exact potential_norm_le T hT J hJ (H-H')


-- @@ L151-153 verbatim
theorem energyOperator_norm_le (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖energyOperator T hT H‖ ≤ 1 + T ^ 2 * ‖H‖ :=
  dirichlet_norm_le T hT _ (initialPrimitive_norm_le_time T hT) H


-- @@ L155-157 verbatim
theorem energyOperator_sub_norm_le (H H' : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    ‖energyOperator T hT H - energyOperator T hT H'‖ ≤ T ^ 2 * ‖H-H'‖ :=
  dirichlet_sub_norm_le T hT _ (initialPrimitive_norm_le_time T hT) H H'


-- @@ L159-160 verbatim
/-- The affine coordinate trial costs a fixed polynomial in time and its reciprocal. -/
def affineCost (T : ℝ) : ℝ := (1+T) * |T⁻¹|


-- @@ L162-176 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem affineTrial_norm_le (A A₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖affineTrial T hT A A₁‖ ≤ affineCost T * (T * ‖A₁‖ + ‖A‖) := by
  have hconst : ‖(constantFieldOperator T hT).comp (T⁻¹ • ContinuousLinearMap.id ℝ U)‖ ≤
      affineCost T := by
    have hscale : ‖T⁻¹ • ContinuousLinearMap.id ℝ U‖ ≤ |T⁻¹| := by
      rw [norm_smul, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_id_le (𝕜 := ℝ) (E := U))
          (abs_nonneg T⁻¹)
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul (constantFieldOperator_norm_le T hT) hscale (norm_nonneg _) (by linarith))
  apply ((opNorm_comp_le _ _).trans (mul_le_mul
    (product_norm_le T hT _ (initialPrimitive_norm_le_time T hT) A A₁)
    hconst (norm_nonneg _) (by positivity))).trans_eq
  ring


-- @@ L178-195 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem affineTrial_sub_norm_le (A A₁ B B₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    ‖affineTrial T hT A A₁ - affineTrial T hT B B₁‖ ≤
      affineCost T * (T * ‖A₁-B₁‖ + ‖A-B‖) := by
  have hconst : ‖(constantFieldOperator T hT).comp (T⁻¹ • ContinuousLinearMap.id ℝ U)‖ ≤
      affineCost T := by
    have hscale : ‖T⁻¹ • ContinuousLinearMap.id ℝ U‖ ≤ |T⁻¹| := by
      rw [norm_smul, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_id_le (𝕜 := ℝ) (E := U))
          (abs_nonneg T⁻¹)
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul (constantFieldOperator_norm_le T hT) hscale (norm_nonneg _) (by linarith))
  unfold affineTrial
  rw [← sub_comp]
  apply ((opNorm_comp_le _ _).trans (mul_le_mul
    (product_sub_norm_le T hT _ (initialPrimitive_norm_le_time T hT) A A₁ B B₁)
    hconst (norm_nonneg _) (by positivity))).trans_eq
  ring


-- @@ L197-197 verbatim
end EulerTransverseEndpointBounds
