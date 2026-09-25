module
public import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12Fourier
import SpherePacking.Contour.Segments
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import Mathlib.Tactic.Ring.RingNF



-- @@ L9-18 verbatim
/-!
# Inner integrals for the `I₁/I₂` kernels

We compute the inner `x`-integrals of `permI1Kernel` and `permI2Kernel`, reducing them to the
Fourier-side integrand `Φ₁_fourier`.

## Main statements
* `integral_permI1Kernel_x`
* `integral_permI2Kernel_x`
-/


-- @@ L20-20 verbatim
namespace MagicFunction.a.Fourier


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open scoped FourierTransform RealInnerProductSpace Topology

-- @@ L25-25 verbatim
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter


-- @@ L27-27 verbatim
section Integral_Permutations


-- @@ L29-29 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L31-31 verbatim
section PermI12Fourier_Aux


-- @@ L33-33 verbatim
open MeasureTheory Set Complex Real

-- @@ L34-34 verbatim
open SpherePacking.ForMathlib

-- @@ L35-35 verbatim
open SpherePacking.Contour

-- @@ L36-36 verbatim
open scoped Interval


-- @@ L38-63 verbatim
/-- The `x`-integral of `permI1Kernel` is `Φ₁_fourier` evaluated at `z₁line t`. -/
public lemma integral_permI1Kernel_x (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
      (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by
    simpa using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (φ₀'' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ 2)
  have hfactor :
      (fun x : ℝ⁸ => permI1Kernel w (x, t)) =
        fun x : ℝ⁸ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) := by
    funext x
    dsimp [permI1Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]
    ac_rfl
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₁line t) hz (c := c)
  calc
    (∫ x : ℝ⁸, permI1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₁line t))) := by
          simpa [hfactor] using hgauss
    _ = (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


-- @@ L65-89 verbatim
/-- The `x`-integral of `permI2Kernel` is `Φ₁_fourier` evaluated at `z₂line t`. -/
public lemma integral_permI2Kernel_x (w : ℝ⁸) (t : ℝ) :
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
      Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := φ₀'' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ 2
  have hfactor :
      (fun x : ℝ⁸ => permI2Kernel w (x, t)) =
        fun x : ℝ⁸ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) := by
    funext x
    dsimp [permI2Kernel, MagicFunction.a.ComplexIntegrands.Φ₁', c]
    ac_rfl
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₂line t) hz (c := c)
  calc
    (∫ x : ℝ⁸, permI2Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₂line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₂line t))) := by
          simpa [hfactor] using hgauss
    _ = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


-- @@ L91-91 verbatim
end Integral_Permutations.PermI12Fourier_Aux

-- @@ L92-92 verbatim
end

-- @@ L93-93 verbatim
end MagicFunction.a.Fourier
