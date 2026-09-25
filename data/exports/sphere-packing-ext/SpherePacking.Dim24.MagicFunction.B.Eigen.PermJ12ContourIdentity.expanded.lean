module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12DiffContOnCl
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12FourierJ2
public import SpherePacking.Contour.PermJ12Contour
public import SpherePacking.Contour.MobiusInv.Segments
import SpherePacking.Dim24.MagicFunction.A.Eigen.GaussianFourier
import SpherePacking.Contour.MobiusInv.ContourChange
import SpherePacking.Contour.MobiusInv.WedgeSet
import SpherePacking.Contour.MobiusInv.LineMap
import SpherePacking.Contour.PermJ12Fourier
import SpherePacking.Contour.Segments
import SpherePacking.Contour.MobiusInv.WedgeSetContour



-- @@ L15-25 verbatim
/-!
# Contour deformation identity for `perm_J₁_J₂`

This file provides the contour-deformation step used to permute the first four contour pieces
`J₁, J₂, J₃, J₄` under the Fourier transform in the construction of the `-1` eigenfunction `b`.

## Main statements
* `perm_J12_contour`
* `perm_J₁_J₂`
* `perm_J₃_J₄`
-/


-- @@ L27-27 verbatim
open scoped FourierTransform


-- @@ L29-29 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L30-30 expanded
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)


-- @@ L32-32 verbatim
namespace SpherePacking.Dim24.BFourier


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
open MagicFunction



-- @@ L39-39 verbatim
section PermJ12


-- @@ L41-60 verbatim
/-- Contour deformation identity for the `J₁/J₂` segments in terms of `Ψ₁_fourier` and `Ψ₁'`. -/
public lemma perm_J12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁_fourier r) z =
      -((∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (Ψ₁' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (Ψ₁' r) z) := by
  simpa using
    (SpherePacking.perm_J12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (Ψ₁_fourier_eq_neg_deriv_mul := by
        intro r z hz
        simpa using (Ψ₁_fourier_eq_neg_deriv_mul (r := r) (z := z) hz))
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))


-- @@ L62-62 verbatim
end PermJ12


-- @@ L64-86 expanded
/-- Fourier permutation identity: `FT (J₁ + J₂) = -(J₃ + J₄)`. -/
public theorem perm_J₁_J₂ :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ))
        ((J₁ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) + J₂) =
      -((J₃ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) + J₄) :=
  by
  refine
    SpherePacking.Contour.perm_J₁_J₂_of (J₁ := (J₁ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ))
      (J₂ := J₂) (J₃ := (J₃ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) (J₄ := J₄) (Ψ₁_fourier :=
      Ψ₁_fourier) (Ψ₁' := Ψ₁') (h :=
      by
      refine ⟨perm_J12_contour, ?_, ?_, ?_⟩
      · intro w
        simpa [SchwartzMap.fourier_coe] using (fourier_J₁_eq_curveIntegral (w := w))
      · intro w
        simpa [SchwartzMap.fourier_coe] using (fourier_J₂_eq_curveIntegral (w := w))
      · intro w
        have hJ₃ : RealIntegrals.J₃' (‖w‖ ^ (2 : ℕ)) = (J₃ : EuclideanSpace ℝ (Fin 24) → ℂ) w := by
          simpa using (J₃_apply (x := w)).symm
        have hJ₄ : RealIntegrals.J₄' (‖w‖ ^ (2 : ℕ)) = (J₄ : EuclideanSpace ℝ (Fin 24) → ℂ) w := by
          simpa using (J₄_apply (x := w)).symm
        have hcurve := (J₃'_add_J₄'_eq_curveIntegral_segments (r := ‖w‖ ^ (2 : ℕ))).symm
        simpa [hJ₃, hJ₄, add_assoc, add_left_comm, add_comm] using hcurve)


-- @@ L89-105 expanded
/-- Fourier permutation identity: `FT (J₃ + J₄) = -(J₁ + J₂)`. -/
public theorem perm_J₃_J₄ :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ))
        ((J₃ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) + J₄) =
      -((J₁ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) + J₂) :=
  by
  have heven : (fun x : EuclideanSpace ℝ (Fin 24) ↦ (J₃ + J₄) (-x)) = fun x ↦ (J₃ + J₄) x :=
    by
    funext x
    simp [J₃, J₄, mkRadial]
  have hsymm :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm (J₃ + J₄) =
      (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) (J₃ + J₄) :=
    AFourier.fourierTransformCLE_symm_eq_of_even (f := J₃ + J₄) heven
  simpa using
    (SpherePacking.Contour.perm_J₃_J₄_of (J₁ := (J₁ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ))
      (J₂ := J₂) (J₃ := (J₃ : SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) (J₄ := J₄) (hsymm :=
      hsymm) (perm_J₁_J₂ := perm_J₁_J₂))


-- @@ L108-108 verbatim
end

-- @@ L109-109 verbatim
end SpherePacking.Dim24.BFourier
