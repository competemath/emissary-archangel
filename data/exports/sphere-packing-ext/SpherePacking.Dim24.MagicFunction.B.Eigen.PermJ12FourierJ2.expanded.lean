module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12FourierJ1
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.Integration.FubiniIoc01
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Integration.UpperHalfPlaneComp



-- @@ L12-21 verbatim
/-!
# Fourier transform of `J₂` as a curve integral

This file proves the curve-integral formula for the Fourier transform of the contour piece `J₂`.
As in the `J₁` case, we introduce an auxiliary kernel and use a Fubini argument to reduce to a
Gaussian Fourier transform computation.

## Main statements
* `fourier_J₂_eq_curveIntegral`
-/


-- @@ L23-23 verbatim
open scoped FourierTransform

-- @@ L24-24 verbatim
open scoped Real


-- @@ L26-26 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L28-28 verbatim
namespace SpherePacking.Dim24.BFourier

-- @@ L29-29 verbatim
open MeasureTheory Set Filter

-- @@ L30-30 verbatim
open SpherePacking.ForMathlib

-- @@ L31-31 verbatim
open SpherePacking.Contour

-- @@ L32-32 verbatim
open SpherePacking.Integration

-- @@ L33-33 verbatim
open scoped Interval RealInnerProductSpace UpperHalfPlane


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
open MagicFunction



-- @@ L40-40 verbatim
section PermJ12


-- @@ L42-46 expanded
def permJ2Kernel (w : EuclideanSpace ℝ (Fin 24)) : EuclideanSpace ℝ (Fin 24) × ℝ → ℂ := fun p =>
  Complex.exp (↑(-2 * (π * ⟪p.1, w⟫)) * Complex.I) *
    (ψT' (z₂line p.2) * Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)))


-- @@ L48-76 expanded
lemma phase_mul_J₂'_eq_integral_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 24)) :
    Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) * RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 :=
  by
  have hJ₂μ :
    RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ,
        ψT' (z₂line t) *
          Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)) ∂μIoc01 :=
    by simpa [μIoc01] using (J₂'_eq_integral_z₂line (r := (‖x‖ ^ (2 : ℕ))))
  calc
    Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) * RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
        Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          ∫ t : ℝ,
            ψT' (z₂line t) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)) ∂μIoc01 :=
      by simp [hJ₂μ, mul_assoc]
    _ =
        ∫ t : ℝ,
          Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
            (ψT' (z₂line t) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t))) ∂μIoc01 :=
      by
      exact
        Eq.symm
          (integral_const_mul (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)) fun a =>
            ψT' (z₂line a) * Complex.exp (↑π * Complex.I * ↑(‖x‖ ^ 2) * z₂line a))
    _ = ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 := by simp [permJ2Kernel, mul_assoc]


-- @@ L78-87 expanded
lemma norm_permJ2Kernel (w x : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * Real.exp (-(π * ‖x‖ ^ 2)) :=
  by
  have hgauss :
    ‖Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ =
      Real.exp (-(π * ‖x‖ ^ 2)) :=
    by
    simpa [z₂line, neg_mul, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.ForMathlib.norm_cexp_pi_mul_I_mul_sq (V := EuclideanSpace ℝ (Fin 24)) (z :=
        z₂line t) (x := x))
  dsimp [permJ2Kernel]
  rw [norm_mul, norm_phase_eq_one (w := w) (x := x)]
  simp_all


-- @@ L89-104 expanded
lemma integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permJ2Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  have hgauss :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦
        Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₂line t) hz
  have hgauss' :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦
        ψT' (z₂line t) * Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by simpa [mul_assoc] using hgauss.const_mul (ψT' (z₂line t))
  simpa [permJ2Kernel, mul_assoc] using
    hgauss'.bdd_mul (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))


-- @@ L106-108 expanded
lemma ae_integrable_permJ2Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) :
    ∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permJ2Kernel w (x, t))
        (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by exact Filter.Eventually.of_forall fun t => integrable_permJ2Kernel_slice (w := w) (t := t)


-- @@ L110-138 expanded
lemma integral_permJ2Kernel_x (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 24), permJ2Kernel w (x, t)) = Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) :=
  by
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  let c : ℂ := ψT' (z₂line t)
  have hfactor :
    (fun x : EuclideanSpace ℝ (Fin 24) ↦ permJ2Kernel w (x, t)) =
      fun x : EuclideanSpace ℝ (Fin 24) ↦
      c *
        (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
          Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))) :=
    by
    funext x
    dsimp [permJ2Kernel, c]
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24), permJ2Kernel w (x, t)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          c *
            (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))) :=
      by
      simpa using
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
          hfactor
    _ =
        c *
          ((((Complex.I : ℂ) / (z₂line t)) ^ (12 : ℕ)) *
            Complex.exp ((π : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₂line t)))) :=
      by
      simpa using
        (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k := 12) (w :=
          w) (z := z₂line t) hz (c := c))
    _ = Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
      simp [c, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


-- @@ L140-148 verbatim
lemma continuous_ψT'_z₂line : Continuous fun t : ℝ => ψT' (z₂line t) := by
  have hz2 : Continuous z₂line :=
    continuous_z₂line
  refine
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := ψT) (ψT' := ψT') (SpherePacking.Dim24.continuous_ψT)
      (z := z₂line) hz2 (fun t => by simp [z₂line]) ?_
  intro t
  simp [ψT', z₂line]


-- @@ L150-157 verbatim
lemma exists_bound_norm_ψT'_z₂line :
    ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, ‖ψT' (z₂line t)‖ ≤ M := by
  rcases
      SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
        (f := fun t : ℝ => ψT' (z₂line t)) continuous_ψT'_z₂line with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  grind only [= uIoc_of_le]


-- @@ L159-198 expanded
lemma integrable_integral_norm_permJ2Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permJ2Kernel w (x, t)‖) μIoc01 :=
  by
  rcases exists_bound_norm_ψT'_z₂line with ⟨Mψ, hMψ⟩
  let Cgauss : ℝ := ∫ x : EuclideanSpace ℝ (Fin 24), Real.exp (-(π * ‖x‖ ^ 2))
  have hCgauss : 0 ≤ Cgauss :=
    by
    have : 0 ≤ fun x : EuclideanSpace ℝ (Fin 24) => Real.exp (-(π * ‖x‖ ^ 2)) := by intro x;
      positivity
    simpa [Cgauss] using MeasureTheory.integral_nonneg this
  let g : ℝ → ℝ := fun t => ‖ψT' (z₂line t)‖ * Cgauss
  have hAE : (fun t : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖permJ2Kernel w (x, t)‖) =ᵐ[μIoc01] g :=
    by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have hfun :
      (fun x : EuclideanSpace ℝ (Fin 24) => ‖permJ2Kernel w (x, t)‖) =
        fun x : EuclideanSpace ℝ (Fin 24) => ‖ψT' (z₂line t)‖ * Real.exp (-(π * ‖x‖ ^ 2)) :=
      by
      funext x
      simpa [mul_assoc] using (norm_permJ2Kernel (w := w) (x := x) (t := t))
    have hInt :
      (∫ x : EuclideanSpace ℝ (Fin 24), ‖permJ2Kernel w (x, t)‖) = ‖ψT' (z₂line t)‖ * Cgauss := by
      simpa [hfun, Cgauss, mul_assoc] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24))))
          (r := ‖ψT' (z₂line t)‖) (f := fun x : EuclideanSpace ℝ (Fin 24) =>
          Real.exp (-(π * ‖x‖ ^ 2))))
    simpa [g] using hInt
  have hmeas_g : AEStronglyMeasurable g μIoc01 :=
    by
    have hmeas : Measurable g := (continuous_ψT'_z₂line.norm.mul continuous_const).measurable
    exact hmeas.aestronglyMeasurable
  have hg_bound : ∀ᵐ t : ℝ ∂μIoc01, ‖g t‖ ≤ (Mψ : ℝ) * Cgauss :=
    by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have hψle : ‖ψT' (z₂line t)‖ ≤ Mψ := hMψ t ht
    have hgt0 : 0 ≤ g t := mul_nonneg (norm_nonneg _) hCgauss
    have hnorm_g : ‖g t‖ = g t := by simp [Real.norm_eq_abs, abs_of_nonneg hgt0]
    have : g t ≤ (Mψ : ℝ) * Cgauss := mul_le_mul_of_nonneg_right hψle hCgauss
    simpa [hnorm_g] using this
  have hmajor : Integrable (fun _t : ℝ => (Mψ : ℝ) * Cgauss) μIoc01 := by
    simpa using (integrable_const (α := ℝ) (μ := μIoc01) ((Mψ : ℝ) * Cgauss))
  have hg_int : Integrable g μIoc01 := Integrable.mono' hmajor hmeas_g hg_bound
  exact hg_int.congr hAE.symm


-- @@ L200-256 expanded
lemma integrable_permJ2Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (permJ2Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  let sProd : Set (EuclideanSpace ℝ (Fin 24) × ℝ) :=
    (Set.univ : Set (EuclideanSpace ℝ (Fin 24))) ×ˢ (Ioc (0 : ℝ) 1)
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas :
    AEStronglyMeasurable (permJ2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
    by
    let μProd : Measure (EuclideanSpace ℝ (Fin 24) × ℝ) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)
    have hμ : ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) = μProd.restrict sProd :=
      by
      simpa [μProd, sProd] using
        (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ :=
          (volume : Measure (EuclideanSpace ℝ (Fin 24)))))
    have hcont : ContinuousOn (permJ2Kernel w) sProd :=
      by
      have hphase :
        Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          Complex.exp (↑(-2 * π * ⟪p.1, w⟫) * Complex.I) :=
        by
        have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (⟪p.1, w⟫ : ℝ) := by
          simpa using (continuous_fst.inner continuous_const)
        have hreal :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (-2 * π) * (⟪p.1, w⟫ : ℝ) :=
          continuous_const.mul hinner
        have harg :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (↑(((-2 * π) * (⟪p.1, w⟫ : ℝ))) : ℂ) * (Complex.I : ℂ) :=
          by exact (Complex.continuous_ofReal.comp hreal).mul continuous_const
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg)
      have hψ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ψT' (z₂line p.2)) sProd :=
        by
        have hcont : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ψT' (z₂line p.2) :=
          continuous_ψT'_z₂line.comp continuous_snd
        exact hcont.continuousOn
      have hgauss :
        Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) :=
        by
        have hnormsq : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
          (continuous_fst.norm.pow 2)
        have hz₂line : Continuous z₂line := continuous_z₂line
        have hz : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => z₂line p.2 :=
          hz₂line.comp continuous_snd
        have harg' :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (π : ℂ) * Complex.I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) :=
          by
          exact
            (continuous_const.mul continuous_const).mul
              ((Complex.continuous_ofReal.comp hnormsq).mul hz)
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
      have hmul :
        ContinuousOn
          (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (ψT' (z₂line p.2)) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)))
          sProd :=
        hψ.mul hgauss.continuousOn
      refine (hphase.continuousOn.mul hmul).congr ?_
      intro p _hp
      simp [permJ2Kernel, mul_assoc]
    have hker : AEStronglyMeasurable (permJ2Kernel w) (μProd.restrict sProd) := by
      simpa [μProd] using (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
    simpa [hμ] using hker
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
          μIoc01) hmeas).2
      ?_
  exact ⟨ae_integrable_permJ2Kernel_slice (w := w), integrable_integral_norm_permJ2Kernel (w := w)⟩


-- @@ L258-267 expanded
private lemma integral_permJ2Kernel_x_ae (w : EuclideanSpace ℝ (Fin 24)) :
    (fun t : ℝ =>
        (∫ x : EuclideanSpace ℝ (Fin 24), permJ2Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) :=
  by
  change
    (∀ᵐ t : ℝ ∂μIoc01,
      (∫ x : EuclideanSpace ℝ (Fin 24), permJ2Kernel w (x, t) ∂(volume : Measure _)) =
        Ψ₁_fourier (‖w‖ ^ 2) (z₂line t))
  refine Filter.Eventually.of_forall ?_
  intro t
  simpa using (integral_permJ2Kernel_x (w := w) (t := t))


-- @@ L269-278 expanded
/-- Fourier transform of `J₂` as a curve integral along the segment from `-1 + i` to `i`. -/
public lemma fourier_J₂_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 24)) :
    (𝓕 (J₂ : EuclideanSpace ℝ (Fin 24) → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) :=
  by
  simpa using
    SpherePacking.Contour.fourier_J₂_eq_curveIntegral_of
      (fun x => by simpa using (J₂_apply (x := x))) phase_mul_J₂'_eq_integral_permJ2Kernel
      integrable_permJ2Kernel integral_permJ2Kernel_x_ae
      (fun w' => by simpa using (integral_muIoc01_z₂line (F := Ψ₁_fourier (‖w'‖ ^ 2)))) w


-- @@ L281-281 verbatim
end PermJ12



-- @@ L284-284 verbatim
end

-- @@ L285-285 verbatim
end SpherePacking.Dim24.BFourier
