module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Measurability
import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import Mathlib.Tactic.Ring.RingNF
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.Integration.EndpointIntegrability
import SpherePacking.ForMathlib.GaussianRexpIntegral



-- @@ L12-22 verbatim
/-!
# Integrability for the `I₁/I₂` kernels

This file proves integrability estimates for the kernels `permI1Kernel` and `permI2Kernel`
needed to justify Fubini/Tonelli in the Fourier permutation argument.

## Main statements
* `integrable_phase_mul_gaussian`
* `ae_integrable_permI1Kernel_slice`, `ae_integrable_permI2Kernel_slice`
* `integrable_integral_norm_permI1Kernel`
-/


-- @@ L24-24 verbatim
open Complex Real


-- @@ L26-26 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L28-28 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L29-29 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L30-30 verbatim
open SpherePacking.ForMathlib

-- @@ L31-31 verbatim
open SpherePacking.Integration (μIoc01)

-- @@ L32-32 verbatim
open SpherePacking.Contour

-- @@ L33-33 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
open MagicFunction.Parametrisations

-- @@ L38-38 verbatim
open scoped Interval


-- @@ L40-49 expanded
/-- Integrability of a Gaussian times the Fourier phase factor in `ℝ²⁴`. -/
public lemma integrable_phase_mul_gaussian (w : EuclideanSpace ℝ (Fin 24)) (z : ℂ) (hz : 0 < z.im) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) =>
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  simpa [mul_assoc] using
    (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (V := EuclideanSpace ℝ (Fin 24))
          z hz).bdd_mul
      (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))


-- @@ L51-55 expanded
lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin 24), rexp (-Real.pi * (‖x‖ ^ 2) * t)) = (1 / t) ^ (12 : ℕ) := by
  simpa [div_eq_mul_inv, one_div, mul_assoc, mul_comm] using
    (SpherePacking.ForMathlib.integral_gaussian_rexp_even (k := 12) (s := (1 / t))
      (one_div_pos.2 ht))


-- @@ L57-71 expanded
lemma norm_permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) (x : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    ‖permI1Kernel w (x, t)‖ =
      ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
        rexp (-Real.pi * (‖x‖ ^ 2) * t) :=
  by
  calc
    ‖permI1Kernel w (x, t)‖ = ‖Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by
      simpa [permI1Kernel, mul_assoc] using
        (norm_phase_mul (w := w) (x := x) (z := (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)))
    _ =
        ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
          ‖cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₁line t)‖ :=
      by simp [Φ₁']
    _ =
        ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
          rexp (-Real.pi * (‖x‖ ^ 2) * t) :=
      by
      rw [norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]
      simp [mul_assoc, mul_comm]


-- @@ L73-80 expanded
lemma integrable_permI1Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permI1Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  have hz : 0 < (z₁line t).im := by simpa using (z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (varphi' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ (10 : ℕ))
  refine ((integrable_phase_mul_gaussian (w := w) (z := z₁line t) hz).const_mul c).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp [permI1Kernel, Φ₁', c, mul_assoc]
  ac_rfl


-- @@ L82-89 expanded
lemma integrable_permI2Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permI2Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := varphi' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ (10 : ℕ)
  refine ((integrable_phase_mul_gaussian (w := w) (z := z₂line t) hz).const_mul c).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp [permI2Kernel, Φ₁', c, mul_assoc]
  ac_rfl


-- @@ L91-96 expanded
/-- For almost every `t ∈ (0, 1]`, the slice `x ↦ permI1Kernel w (x,t)` is integrable. -/
public lemma ae_integrable_permI1Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permI1Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 24)))) :=
  by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  exact integrable_permI1Kernel_slice (w := w) (t := t) ht


-- @@ L98-103 expanded
/-- For almost every `t ∈ (0, 1]`, the slice `x ↦ permI2Kernel w (x,t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permI2Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 24)))) :=
  by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t _ => ?_
  exact integrable_permI2Kernel_slice (w := w) (t := t)


-- @@ L105-118 expanded
lemma integral_norm_permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 24), ‖permI1Kernel w (x, t)‖) =
      ‖varphi' (-1 / (z₁line t + 1))‖ * (1 / t ^ (2 : ℕ)) :=
  by
  have hnorm :
    (fun x : EuclideanSpace ℝ (Fin 24) => ‖permI1Kernel w (x, t)‖) =
      fun x : EuclideanSpace ℝ (Fin 24) =>
      (‖varphi' (-1 / (z₁line t + 1))‖ * t ^ (10 : ℕ)) * rexp (-Real.pi * (‖x‖ ^ 2) * t) :=
    by
    funext x
    have hpowz : ‖(z₁line t + 1) ^ (10 : ℕ)‖ = t ^ (10 : ℕ) := by
      simp [Complex.norm_real, abs_of_nonneg ht.1.le]
    simpa only [hpowz] using (norm_permI1Kernel (w := w) (x := x) (t := t))
  rw [hnorm, MeasureTheory.integral_const_mul, integral_rexp_neg_pi_mul_sq_norm (t := t) ht.1]
  grind only [= mem_Ioc]


-- @@ L120-125 expanded
lemma aestronglyMeasurable_integral_norm_permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permI1Kernel w (x, t)‖)
      μIoc01 :=
  by
  simpa using
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := μIoc01) (ν :=
      (volume : Measure (EuclideanSpace ℝ (Fin 24))))
      ((permI1Kernel_measurable (w := w)).norm.prod_swap))


-- @@ L127-133 verbatim
lemma norm_varphi'_neg_one_div_z₁line_add_one_le {Cφ : ℝ}
    (hCφ : ∀ t : ℝ, 1 ≤ t → ‖varphi.resToImagAxis t‖ ≤ Cφ * rexp (-(2 * Real.pi) * t))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖varphi' (-1 / (z₁line t + 1))‖ ≤ Cφ * rexp (-(2 * Real.pi) / t) := by
  have hs : 1 ≤ (1 / t : ℝ) := one_le_one_div ht.1 ht.2
  have h := (congrArg norm (varphi'_neg_one_div_z₁line_add_one_eq t ht)).symm ▸ hCφ (1 / t) hs
  simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using h


-- @@ L135-153 expanded
/-- Integrability of `t ↦ ∫ ‖permI1Kernel w (x,t)‖ dx` on `t ∈ (0, 1]`. -/
public lemma integrable_integral_norm_permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permI1Kernel w (x, t)‖) μIoc01 :=
  by
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hmajor :
    Integrable (fun t : ℝ ↦ (Cφ : ℝ) * ((1 / t ^ 2) * rexp (-(2 * Real.pi) / t))) μIoc01 := by
    simpa [μIoc01, IntegrableOn, mul_assoc] using
      (SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div (c := 2 * Real.pi)
            (by positivity [Real.pi_pos])).const_mul
        (Cφ : ℝ)
  refine Integrable.mono' hmajor (aestronglyMeasurable_integral_norm_permI1Kernel (w := w)) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)),
    integral_norm_permI1Kernel (w := w) (t := t) ht]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right (norm_varphi'_neg_one_div_z₁line_add_one_le (hCφ := hCφ) (t := t) ht)
      (by positivity : 0 ≤ (1 / t ^ (2 : ℕ) : ℝ))


-- @@ L156-156 verbatim
end


-- @@ L158-158 verbatim
end SpherePacking.Dim24.AFourier
