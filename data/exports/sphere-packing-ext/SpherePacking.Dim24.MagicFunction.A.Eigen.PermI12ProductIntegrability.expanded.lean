/-
Product integrability for the Fubini swap.
-/
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Integrability
import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import Mathlib.Tactic.Ring.RingNF
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds



-- @@ L13-23 verbatim
/-!
# Product integrability for the `I₁/I₂` kernels

This file proves that the kernels `permI1Kernel` and `permI2Kernel` are integrable on the product
measure `((volume : Measure ℝ²⁴).prod μIoc01)`. These are the hypotheses needed to justify
swapping the `x` and `t` integrals in the Fourier permutation argument.

## Main statements
* `integrable_permI1Kernel`
* `integrable_permI2Kernel`
-/


-- @@ L25-25 verbatim
open Complex Real


-- @@ L27-27 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L29-29 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L30-30 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L31-31 verbatim
open SpherePacking.ForMathlib

-- @@ L32-32 verbatim
open SpherePacking.Integration (μIoc01)

-- @@ L33-33 verbatim
open SpherePacking.Contour

-- @@ L34-34 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
open MagicFunction.Parametrisations

-- @@ L39-39 verbatim
open scoped Interval



-- @@ L42-49 expanded
/-- Product integrability of the kernel `permI1Kernel w` on `ℝ²⁴ × Ioc (0, 1]`. -/
public lemma integrable_permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (permI1Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  have hmeas :
    AEStronglyMeasurable (permI1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
    permI1Kernel_measurable (w := w)
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
          μIoc01) hmeas).2
      ?_
  exact ⟨ae_integrable_permI1Kernel_slice (w := w), integrable_integral_norm_permI1Kernel (w := w)⟩


-- @@ L51-68 expanded
lemma norm_permI2Kernel (w : EuclideanSpace ℝ (Fin 24)) (x : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    ‖permI2Kernel w (x, t)‖ =
      ‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖ *
        rexp (-(Real.pi * (‖x‖ ^ 2))) :=
  by
  calc
    ‖permI2Kernel w (x, t)‖ = ‖Φ₁' (‖x‖ ^ 2) (z₂line t)‖ := by
      simpa [permI2Kernel] using (norm_phase_mul (w := w) (x := x) (z := Φ₁' (‖x‖ ^ 2) (z₂line t)))
    _ =
        ‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖ *
          ‖cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₂line t)‖ :=
      by simp [Φ₁']
    _ =
        ‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖ *
          rexp (-(Real.pi * (‖x‖ ^ 2))) :=
      by
      rw [norm_cexp_pi_mul_I_mul_sq (z := z₂line t) (x := x)]
      simp [mul_assoc, mul_left_comm, mul_comm]


-- @@ L70-99 verbatim
lemma continuousOn_varphi'_neg_one_div_z₂line_add_one_Icc :
    ContinuousOn (fun t : ℝ => varphi' (-1 / (z₂line t + 1))) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  let s : Set ℝ := Icc (0 : ℝ) 1
  let Z : s → ℍ := fun t =>
    ⟨(-1 : ℂ) / (z₂line (t : ℝ) + 1), by
      exact neg_one_div_z₂line_add_one_im_pos (t := (t : ℝ))⟩
  have hZ : Continuous Z := by
    have hbase : Continuous fun t : s => (-1 : ℂ) / (z₂line (t : ℝ) + 1) := by
      have hcont_z₂line : Continuous z₂line := by
        simpa using SpherePacking.Contour.continuous_z₂line
      have hz : Continuous fun t : s => z₂line (t : ℝ) :=
        hcont_z₂line.comp continuous_subtype_val
      have hz1 : Continuous fun t : s => z₂line (t : ℝ) + 1 := hz.add continuous_const
      have hne : ∀ t : s, z₂line (t : ℝ) + 1 ≠ 0 := by
        intro t
        have him : (z₂line (t : ℝ) + 1).im = (1 : ℝ) := by
          simp
        intro h0
        have him0 : (z₂line (t : ℝ) + 1).im = 0 := by
          simpa using congrArg Complex.im h0
        have : (1 : ℝ) = 0 := him.symm.trans him0
        exact one_ne_zero this
      exact (continuous_const.div hz1 hne)
    exact Continuous.upperHalfPlaneMk hbase fun x => neg_one_div_z₂line_add_one_im_pos ↑x
  have hvarphi : Continuous fun t : s => varphi (Z t) :=
    VarphiExpBounds.continuous_varphi.comp hZ
  refine hvarphi.congr ?_
  intro t
  simpa [Z, s] using (SpherePacking.Dim24.varphi'_coe_upperHalfPlane (z := Z t)).symm


-- @@ L101-116 verbatim
lemma exists_bound_coeff_permI2 :
    ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖ ≤ M := by
  let coeff : ℝ → ℝ := fun t =>
    ‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖
  have hcont : ContinuousOn coeff (Icc (0 : ℝ) 1) := by
    refine (continuousOn_varphi'_neg_one_div_z₂line_add_one_Icc.norm).mul ?_
    have hcont_z₂line : Continuous z₂line := by
      simpa using SpherePacking.Contour.continuous_z₂line
    exact (((hcont_z₂line.add continuous_const).pow 10).norm.continuousOn)
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by constructor <;> norm_num⟩
  rcases (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_isMaxOn hne hcont with
    ⟨t0, ht0, htmax⟩
  refine ⟨coeff t0, ?_⟩
  intro t ht
  exact htmax ⟨le_of_lt ht.1, ht.2⟩


-- @@ L118-160 expanded
lemma integrable_integral_norm_permI2Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permI2Kernel w (x, t)‖) μIoc01 :=
  by
  rcases exists_bound_coeff_permI2 with ⟨Mcoeff, hMcoeff⟩
  let Cgauss : ℝ := ∫ x : EuclideanSpace ℝ (Fin 24), rexp (-(Real.pi * (‖x‖ ^ 2)))
  have hCgauss : 0 ≤ Cgauss := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    positivity
  have hmeas :
    AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permI2Kernel w (x, t)‖)
      μIoc01 :=
    by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := μIoc01) (ν :=
        (volume : Measure (EuclideanSpace ℝ (Fin 24))))
        ((permI2Kernel_measurable (w := w)).norm.prod_swap))
  have hmajor : Integrable (fun _t : ℝ => (Mcoeff : ℝ) * Cgauss) μIoc01 := by
    simpa using (integrable_const (α := ℝ) (μ := μIoc01) ((Mcoeff : ℝ) * Cgauss))
  refine Integrable.mono' hmajor hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  have hfun :
    (fun x : EuclideanSpace ℝ (Fin 24) => ‖permI2Kernel w (x, t)‖) =
      fun x : EuclideanSpace ℝ (Fin 24) =>
      (‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖) *
        rexp (-(Real.pi * (‖x‖ ^ 2))) :=
    by
    funext x
    simpa [mul_assoc] using (norm_permI2Kernel (w := w) (x := x) (t := t))
  have hInt :
    (∫ x : EuclideanSpace ℝ (Fin 24), ‖permI2Kernel w (x, t)‖) =
      (‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖) * Cgauss :=
    by
    simpa [hfun, Cgauss, mul_assoc] using
      (MeasureTheory.integral_const_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (r :=
        (‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖)) (f :=
        fun x : EuclideanSpace ℝ (Fin 24) => rexp (-(Real.pi * (‖x‖ ^ 2)))))
  have hcoeff_le : (‖varphi' (-1 / (z₂line t + 1))‖ * ‖(z₂line t + 1) ^ (10 : ℕ)‖) ≤ Mcoeff :=
    hMcoeff t ht
  have hbound :
    (∫ x : EuclideanSpace ℝ (Fin 24), ‖permI2Kernel w (x, t)‖) ≤ (Mcoeff : ℝ) * Cgauss :=
    by
    have := mul_le_mul_of_nonneg_right hcoeff_le hCgauss
    simpa [hInt, mul_assoc] using this
  have hn0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permI2Kernel w (x, t)‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  simpa [Real.norm_of_nonneg hn0] using hbound


-- @@ L162-168 expanded
/-- Product integrability of the kernel `permI2Kernel w` on `ℝ²⁴ × Ioc (0, 1]`. -/
public lemma integrable_permI2Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (permI2Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
          μIoc01) (permI2Kernel_measurable (w := w))).2
      ?_
  exact ⟨ae_integrable_permI2Kernel_slice (w := w), integrable_integral_norm_permI2Kernel (w := w)⟩


-- @@ L171-171 verbatim
end


-- @@ L173-173 verbatim
end SpherePacking.Dim24.AFourier
