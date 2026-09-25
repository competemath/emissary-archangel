module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12CurveIntegrals
import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12ProductIntegrability
import SpherePacking.Integration.Measure
import SpherePacking.Integration.FubiniIoc01



-- @@ L8-17 verbatim
/-!
# Fourier transforms of `I₁` and `I₂` as curve integrals

This file expresses the Fourier transforms of the Schwartz functions `I₁` and `I₂` as contour
integrals of `Φ₁_fourier` along the two segments forming the path from `-1` to `i`.

## Main statements
* `fourier_I₁_eq_curveIntegral`
* `fourier_I₂_eq_curveIntegral`
-/


-- @@ L19-19 verbatim
open scoped FourierTransform

-- @@ L20-20 verbatim
open Complex Real


-- @@ L22-22 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L24-24 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L25-25 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L26-26 verbatim
open SpherePacking.Integration

-- @@ L27-27 verbatim
open SpherePacking.Contour

-- @@ L28-28 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
open MagicFunction.Parametrisations

-- @@ L33-33 verbatim
open MagicFunction

-- @@ L34-34 verbatim
open scoped Interval



-- @@ L37-110 expanded
/-- The Fourier transform of `I₁` as a contour integral along the segment from `-1` to `-1 + i`. -/
public lemma fourier_I₁_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 24)) :
    𝓕 (I₁ : EuclideanSpace ℝ (Fin 24) → ℂ) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
  by
  rw [fourier_eq' (I₁ : EuclideanSpace ℝ (Fin 24) → ℂ) w]
  simp only [smul_eq_mul, I₁_apply, mul_assoc]
  have hI₁' (x : EuclideanSpace ℝ (Fin 24)) :
    RealIntegrals.I₁' (‖x‖ ^ 2) = ∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t) :=
    by
    rw [I₁'_eq_curveIntegral_segment (r := ‖x‖ ^ 2)]
    rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) (-1 : ℂ) ((-1 : ℂ) + I)]
    rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)
        (by norm_num)]
    have hdir : (((-1 : ℂ) + I) - (-1 : ℂ)) = (I : ℂ) := SpherePacking.Contour.dir_z₁line
    simp [scalarOneForm_apply, z₁line, hdir, SpherePacking.Contour.lineMap_z₁line]
  have hmul :
    (fun x : EuclideanSpace ℝ (Fin 24) ↦
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          (∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t))) =
      fun x : EuclideanSpace ℝ (Fin 24) ↦
      ∫ t in Ioc (0 : ℝ) 1,
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)) :=
    by
    funext x
    simpa [μIoc01] using
      (MeasureTheory.integral_const_mul (μ := μIoc01) (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I)) (f :=
          fun t : ℝ ↦ (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t))).symm
  let f : EuclideanSpace ℝ (Fin 24) → ℝ → ℂ := fun x t => permI1Kernel w (x, t)
  let g : ℝ → ℂ := fun t : ℝ => (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t)
  have hint :
    Integrable (Function.uncurry f) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
    by
    have hint' :
      Integrable (permI1Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
      integrable_permI1Kernel (w := w)
    simpa [f, Function.uncurry] using hint'
  have hswapEq : (∫ x : EuclideanSpace ℝ (Fin 24), ∫ t : ℝ, f x t ∂μIoc01) = ∫ t : ℝ, g t ∂μIoc01 :=
    by
    refine
      SpherePacking.Integration.integral_integral_swap_muIoc01 (V := EuclideanSpace ℝ (Fin 24))
        (f := f) (g := g) hint ?_
    intro t ht
    simpa [f, g] using (integral_permI1Kernel_x (w := w) (t := t) ht)
  have hcurve :
    (∫ t : ℝ, g t ∂μIoc01) =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I), scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
    by
    have hzline : ∀ t : ℝ, AffineMap.lineMap (-1 : ℂ) ((-1 : ℂ) + I) t = z₁line t :=
      by
      intro t
      simpa using (SpherePacking.Contour.lineMap_z₁line (t := t))
    simpa [g, SpherePacking.Contour.dir_z₁line] using
      (SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment (F :=
        Φ₁_fourier (‖w‖ ^ 2)) (a := (-1 : ℂ)) (b := (-1 : ℂ) + I) (zline := z₁line) hzline)
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24),
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₁' (‖x‖ ^ 2)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (∫ t in Ioc (0 : ℝ) 1, (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)) :=
      by
      refine MeasureTheory.integral_congr_ae ?_
      refine ae_of_all _ ?_
      intro x
      simp [hI₁' x, mul_assoc]
    _ =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          ∫ t in Ioc (0 : ℝ) 1,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)) :=
      by
      exact
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
          hmul
    _ = ∫ x : EuclideanSpace ℝ (Fin 24), ∫ t : ℝ, f x t ∂μIoc01 := by
      simp [f, permI1Kernel, μIoc01, mul_assoc]
    _ = ∫ t : ℝ, g t ∂μIoc01 := hswapEq
    _ = (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I), scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
      hcurve


-- @@ L112-183 expanded
/-- The Fourier transform of `I₂` as a contour integral along the segment from `-1 + i` to `i`. -/
public lemma fourier_I₂_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 24)) :
    𝓕 (I₂ : EuclideanSpace ℝ (Fin 24) → ℂ) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
  by
  rw [fourier_eq' (I₂ : EuclideanSpace ℝ (Fin 24) → ℂ) w]
  simp only [smul_eq_mul, I₂_apply, mul_assoc]
  have hI₂' (x : EuclideanSpace ℝ (Fin 24)) :
    RealIntegrals.I₂' (‖x‖ ^ 2) = ∫ t in Ioc (0 : ℝ) 1, Φ₁' (‖x‖ ^ 2) (z₂line t) :=
    by
    rw [I₂'_eq_curveIntegral_segment (r := ‖x‖ ^ 2)]
    rw [curveIntegral_segment (ω := scalarOneForm (Φ₁' (‖x‖ ^ 2))) ((-1 : ℂ) + I) I]
    rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)
        (by norm_num)]
    have hdir : (I - ((-1 : ℂ) + I)) = (1 : ℂ) := SpherePacking.Contour.dir_z₂line
    simp [scalarOneForm_apply, z₂line, hdir, SpherePacking.Contour.lineMap_z₂line]
  have hmul :
    (fun x : EuclideanSpace ℝ (Fin 24) ↦
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * (∫ t in Ioc (0 : ℝ) 1, Φ₁' (‖x‖ ^ 2) (z₂line t))) =
      fun x : EuclideanSpace ℝ (Fin 24) ↦
      ∫ t in Ioc (0 : ℝ) 1, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * (Φ₁' (‖x‖ ^ 2) (z₂line t)) :=
    by
    funext x
    simpa [μIoc01] using
      (MeasureTheory.integral_const_mul (μ := μIoc01) (r := cexp (↑(-2 * (π * ⟪x, w⟫)) * I)) (f :=
          fun t : ℝ ↦ Φ₁' (‖x‖ ^ 2) (z₂line t))).symm
  let f : EuclideanSpace ℝ (Fin 24) → ℝ → ℂ := fun x t => permI2Kernel w (x, t)
  let g : ℝ → ℂ := fun t : ℝ => Φ₁_fourier (‖w‖ ^ 2) (z₂line t)
  have hint :
    Integrable (Function.uncurry f) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
    by
    have hint' :
      Integrable (permI2Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
      integrable_permI2Kernel (w := w)
    simpa [f, Function.uncurry] using hint'
  have hswapEq : (∫ x : EuclideanSpace ℝ (Fin 24), ∫ t : ℝ, f x t ∂μIoc01) = ∫ t : ℝ, g t ∂μIoc01 :=
    by
    refine
      SpherePacking.Integration.integral_integral_swap_muIoc01 (V := EuclideanSpace ℝ (Fin 24))
        (f := f) (g := g) hint ?_
    intro t ht
    simpa [f, g] using (integral_permI2Kernel_x (w := w) (t := t))
  have hcurve :
    (∫ t : ℝ, g t ∂μIoc01) =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I, scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
    by
    have hzline : ∀ t : ℝ, AffineMap.lineMap ((-1 : ℂ) + I) I t = z₂line t :=
      by
      intro t
      simpa using (SpherePacking.Contour.lineMap_z₂line (t := t))
    simpa [g, SpherePacking.Contour.dir_z₂line] using
      (SpherePacking.Integration.integral_dir_mul_muIoc01_eq_curveIntegral_segment (F :=
        Φ₁_fourier (‖w‖ ^ 2)) (a := (-1 : ℂ) + I) (b := I) (zline := z₂line) hzline)
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24),
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * RealIntegrals.I₂' (‖x‖ ^ 2)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * (∫ t in Ioc (0 : ℝ) 1, Φ₁' (‖x‖ ^ 2) (z₂line t)) :=
      by
      refine MeasureTheory.integral_congr_ae ?_
      refine ae_of_all _ ?_
      intro x
      simp [hI₂' x, mul_assoc]
    _ =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          ∫ t in Ioc (0 : ℝ) 1, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * (Φ₁' (‖x‖ ^ 2) (z₂line t)) :=
      (congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
        hmul)
    _ = ∫ x : EuclideanSpace ℝ (Fin 24), ∫ t : ℝ, f x t ∂μIoc01 := by
      simp [f, permI2Kernel, μIoc01, mul_assoc]
    _ = ∫ t : ℝ, g t ∂μIoc01 := hswapEq
    _ = (∫ᶜ z in Path.segment ((-1 : ℂ) + I) I, scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) := hcurve


-- @@ L186-186 verbatim
end


-- @@ L188-188 verbatim
end SpherePacking.Dim24.AFourier
