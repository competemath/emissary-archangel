module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12CurveIntegrals
public import SpherePacking.Integration.Measure
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.Integration.FubiniIoc01
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12Measurability



-- @@ L9-18 verbatim
/-!
# Fourier transform of `J₁` as a curve integral

We justify a Fubini argument for the auxiliary kernel `permJ1Kernel` and use it to rewrite the
Fourier transform of the contour piece `J₁` as a curve integral of `Ψ₁_fourier` along the segment
from `-1` to `-1 + i`.

## Main statements
* `fourier_J₁_eq_curveIntegral`
-/


-- @@ L20-20 verbatim
open scoped FourierTransform

-- @@ L21-21 verbatim
open scoped Real


-- @@ L23-23 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L25-25 verbatim
namespace SpherePacking.Dim24.BFourier

-- @@ L26-26 verbatim
open MeasureTheory Set Filter

-- @@ L27-27 verbatim
open SpherePacking.Integration

-- @@ L28-28 verbatim
open SpherePacking.Contour

-- @@ L29-29 verbatim
open scoped RealInnerProductSpace


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open MagicFunction



-- @@ L36-36 verbatim
section PermJ12


-- @@ L38-102 expanded
lemma integrable_permJ1Kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (permJ1Kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  let sProd : Set (EuclideanSpace ℝ (Fin 24) × ℝ) :=
    (Set.univ : Set (EuclideanSpace ℝ (Fin 24))) ×ˢ (Ioc (0 : ℝ) 1)
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas :
    AEStronglyMeasurable (permJ1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
    by
    let μProd : Measure (EuclideanSpace ℝ (Fin 24) × ℝ) :=
      (volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)
    have hμ : ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) = μProd.restrict sProd :=
      by
      simpa [μProd, sProd] using
        (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ :=
          (volume : Measure (EuclideanSpace ℝ (Fin 24)))))
    have hcont : ContinuousOn (permJ1Kernel w) sProd :=
      by
      have hphase :
        Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          Complex.exp (↑(-2 * (π * ⟪p.1, w⟫)) * Complex.I) :=
        by
        have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (⟪p.1, w⟫ : ℝ) := by
          simpa using (continuous_fst.inner continuous_const)
        have hreal :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)) :=
          continuous_const.mul (continuous_const.mul hinner)
        have harg :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) * (Complex.I : ℂ) :=
          (Complex.continuous_ofReal.comp hreal).mul continuous_const
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg)
      have hψ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ψT' (z₁line p.2)) sProd :=
        by
        refine continuousOn_ψT'_z₁line.comp continuousOn_snd ?_
        intro p hp
        exact (Set.mem_prod.mp hp).2
      have hgauss :
        Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) :=
        by
        have hnormsq : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
          (continuous_fst.norm.pow 2)
        have hz₁line : Continuous z₁line := by
          simpa [z₁line] using
            (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
        have hz : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => z₁line p.2 :=
          hz₁line.comp continuous_snd
        have harg' :
          Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            (π : ℂ) * Complex.I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) :=
          (continuous_const.mul continuous_const).mul
            ((Complex.continuous_ofReal.comp hnormsq).mul hz)
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
      have hconst :
        ContinuousOn (fun _p : EuclideanSpace ℝ (Fin 24) × ℝ => (Complex.I : ℂ)) sProd :=
        continuousOn_const
      have hmul1 :
        ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (Complex.I : ℂ) * ψT' (z₁line p.2))
          sProd :=
        hconst.mul hψ
      have hmul2 :
        ContinuousOn
          (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
            ((Complex.I : ℂ) * ψT' (z₁line p.2)) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)))
          sProd :=
        hmul1.mul hgauss.continuousOn
      refine (hphase.continuousOn.mul hmul2).congr ?_
      intro p _hp
      simp [permJ1Kernel, mul_assoc]
    have hker : AEStronglyMeasurable (permJ1Kernel w) (μProd.restrict sProd) := by
      simpa [μProd] using (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
    simpa [hμ] using hker
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
          μIoc01) hmeas).2
      ?_
  exact ⟨ae_integrable_permJ1Kernel_slice (w := w), integrable_integral_norm_permJ1Kernel (w := w)⟩


-- @@ L104-124 expanded
private lemma integral_permJ1Kernel_x_ae (w : EuclideanSpace ℝ (Fin 24)) :
    (fun t : ℝ =>
        (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) :=
  by
  change
    (∀ᵐ t : ℝ ∂μIoc01,
      (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t) ∂(volume : Measure _)) =
        (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t))
  have hall :
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      t ∈ Ioc (0 : ℝ) 1 →
        (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t) ∂(volume : Measure _)) =
          (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) :=
    by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    simpa using (integral_permJ1Kernel_x (w := w) (t := t) ht)
  have hrestrict :
    (∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
      (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t) ∂(volume : Measure _)) =
        (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t)) :=
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc).2 hall
  simpa [SpherePacking.Integration.μIoc01] using hrestrict


-- @@ L126-135 expanded
/-- Fourier transform of `J₁` as a curve integral along the segment from `-1` to `-1 + i`. -/
public lemma fourier_J₁_eq_curveIntegral (w : EuclideanSpace ℝ (Fin 24)) :
    𝓕 (J₁ : EuclideanSpace ℝ (Fin 24) → ℂ) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) :=
  by
  simpa using
    SpherePacking.Contour.fourier_J₁_eq_curveIntegral_of
      (fun x => by simpa using (J₁_apply (x := x))) phase_mul_J₁'_eq_integral_permJ1Kernel
      integrable_permJ1Kernel integral_permJ1Kernel_x_ae
      (fun w' => by simpa using (integral_I_mul_muIoc01_z₁line (F := Ψ₁_fourier (‖w'‖ ^ 2)))) w


-- @@ L138-138 verbatim
end PermJ12



-- @@ L141-141 verbatim
end

-- @@ L142-142 verbatim
end SpherePacking.Dim24.BFourier
