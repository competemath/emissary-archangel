module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12CurveIntegrals
public import SpherePacking.Contour.Segments
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import Mathlib.Tactic.Ring.RingNF



-- @@ L9-21 verbatim
/-!
# Fourier kernels for `I₁` and `I₂`

This file defines the kernels that appear when rewriting the Fourier transforms of `I₁` and `I₂`
as iterated `(x,t)` integrals, and evaluates the inner integrals in terms of `Φ₁_fourier`.

## Main definitions
* `permI1Kernel`, `permI2Kernel`

## Main statements
* `integral_permI1Kernel_x`
* `integral_permI2Kernel_x`
-/


-- @@ L23-23 verbatim
open Complex Real


-- @@ L25-25 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L27-27 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L28-28 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L29-29 verbatim
open SpherePacking.ForMathlib

-- @@ L30-30 verbatim
open SpherePacking.Contour

-- @@ L31-31 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open MagicFunction.Parametrisations

-- @@ L36-36 verbatim
open scoped Interval



-- @@ L39-39 verbatim
open MeasureTheory Set Complex Real


-- @@ L41-44 expanded
/-- The integrand in the `(x,t)` representation of the Fourier transform of `I₁`. -/
@[expose]
public def permI1Kernel (w : EuclideanSpace ℝ (Fin 24)) : EuclideanSpace ℝ (Fin 24) × ℝ → ℂ :=
  fun p => cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖p.1‖ ^ 2) (z₁line p.2))


-- @@ L46-49 expanded
/-- The integrand in the `(x,t)` representation of the Fourier transform of `I₂`. -/
@[expose]
public def permI2Kernel (w : EuclideanSpace ℝ (Fin 24)) : EuclideanSpace ℝ (Fin 24) × ℝ → ℂ :=
  fun p => cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * (Φ₁' (‖p.1‖ ^ 2) (z₂line p.2))


-- @@ L51-81 expanded
/-- Evaluate `∫ permI1Kernel w (x,t) dx` as the Fourier-modified integrand `Φ₁_fourier`. -/
public lemma integral_permI1Kernel_x (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 24), permI1Kernel w (x, t)) =
      (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) :=
  by
  have hz : 0 < (z₁line t).im := by
    simpa using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (varphi' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ (10 : ℕ))
  have hfactor :
    (fun x : EuclideanSpace ℝ (Fin 24) => permI1Kernel w (x, t)) =
      fun x : EuclideanSpace ℝ (Fin 24) =>
      c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) :=
    by
    funext x
    dsimp [permI1Kernel, Φ₁', mul_assoc, c]
    ac_rfl
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24), permI1Kernel w (x, t)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) :=
      by
      simpa using
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
          hfactor
    _ =
        c *
          ((((I : ℂ) / (z₁line t)) ^ (12 : ℕ)) *
            cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₁line t))) :=
      by
      simpa using
        (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k := 12) (w :=
          w) (z := z₁line t) hz (c := c))
    _ = (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
      simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


-- @@ L83-112 expanded
/-- Evaluate `∫ permI2Kernel w (x,t) dx` as the Fourier-modified integrand `Φ₁_fourier`. -/
public lemma integral_permI2Kernel_x (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 24), permI2Kernel w (x, t)) = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) :=
  by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := varphi' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ (10 : ℕ)
  have hfactor :
    (fun x : EuclideanSpace ℝ (Fin 24) => permI2Kernel w (x, t)) =
      fun x : EuclideanSpace ℝ (Fin 24) =>
      c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) :=
    by
    funext x
    dsimp [permI2Kernel, Φ₁', mul_assoc, c]
    ac_rfl
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24), permI2Kernel w (x, t)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) :=
      by
      simpa using
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
          hfactor
    _ =
        c *
          ((((I : ℂ) / (z₂line t)) ^ (12 : ℕ)) *
            cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₂line t))) :=
      by
      simpa using
        (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k := 12) (w :=
          w) (z := z₂line t) hz (c := c))
    _ = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
      simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end SpherePacking.Dim24.AFourier
