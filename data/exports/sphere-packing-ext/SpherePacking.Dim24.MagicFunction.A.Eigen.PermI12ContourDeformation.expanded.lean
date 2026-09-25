module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12FourierCurveIntegrals
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Regularity
import SpherePacking.Contour.MobiusInv.WedgeSetContour


-- @@ L6-17 verbatim
/-!
# Contour deformation for the `I₁/I₂` permutation

This file proves the key contour-deformation identity `perm_I12_contour` and uses it to
derive the permutation identities `perm_I₁_I₂` and `perm_I₃_I₄`.
The geometric contour-deformation input is provided by
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean`.

## Main statements
* `perm_I₁_I₂`
* `perm_I₃_I₄`
-/


-- @@ L19-19 verbatim
open scoped FourierTransform


-- @@ L21-21 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L23-23 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L24-24 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L25-25 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open MagicFunction.Parametrisations

-- @@ L30-30 verbatim
open MagicFunction

-- @@ L31-31 verbatim
open scoped Interval


-- @@ L33-52 verbatim
/-- Contour deformation relating the two segment integrals in the `I₁/I₂` permutation argument. -/
lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Φ₃' r) z := by
  simpa using
    (SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Φ₁_fourier)
      (Ψ₁' := Φ₃')
      (Ψ₁_fourier_eq_deriv_mul := by
        intro r z hz
        simpa using (Φ₁_fourier_eq_deriv_mul (r := r) (z := z) hz))
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))


-- @@ L54-73 expanded
/-- Fourier permutation identity: `𝓕 (I₁ + I₂) = I₃ + I₄`. -/
public theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)
        (I₁ + I₂ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) =
      (I₃ + I₄ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) :=
  by
  ext w
  simp only [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, SchwartzMap.add_apply]
  have hFI₁ :
    (𝓕 I₁) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
    by simpa [SchwartzMap.fourier_coe] using (fourier_I₁_eq_curveIntegral (w := w))
  have hFI₂ :
    (𝓕 I₂) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₁_fourier (‖w‖ ^ 2)) z) :=
    by simpa [SchwartzMap.fourier_coe] using (fourier_I₂_eq_curveIntegral (w := w))
  rw [hFI₁, hFI₂]
  rw [perm_I12_contour (r := ‖w‖ ^ 2)]
  simpa [I₃_apply, I₄_apply] using (I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)).symm


-- @@ L75-87 expanded
/-- Fourier permutation identity: `𝓕 (I₃ + I₄) = I₁ + I₂`. -/
public theorem perm_I₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)
        (I₃ + I₄ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) =
      (I₁ + I₂ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) :=
  by
  have heven : (fun x : EuclideanSpace ℝ (Fin 24) ↦ (I₃ + I₄) (-x)) = fun x ↦ (I₃ + I₄) x :=
    by
    funext x
    simp [I₃, I₄, mkRadial]
  have hsymm :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm (I₃ + I₄) =
      FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) (I₃ + I₄) :=
    fourierTransformCLE_symm_eq_of_even (f := I₃ + I₄) heven
  have h :=
    congrArg (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm
      perm_I₁_I₂
  simp_all


-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
end SpherePacking.Dim24.AFourier
