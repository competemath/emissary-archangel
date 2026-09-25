module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.Prelude



-- @@ L5-14 verbatim
/-!
# Gaussian Fourier lemmas

This file contains small Fourier-transform identities for Gaussians in dimension `24`
used in the permutation arguments.

## Main statements
* `fourierTransformCLE_symm_eq_of_even`
* `zpow_neg_twelve_mul_pow_twelve`
-/


-- @@ L16-16 verbatim
open scoped SchwartzMap


-- @@ L18-18 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L20-20 verbatim
namespace SpherePacking.Dim24.AFourier


-- @@ L22-22 verbatim
noncomputable section



-- @@ L25-32 expanded
/-- For an even Schwartz function, the inverse Fourier transform equals the Fourier transform. -/
public lemma fourierTransformCLE_symm_eq_of_even (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (heven : (fun x : EuclideanSpace ℝ (Fin 24) ↦ f (-x)) = fun x ↦ f x) :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm f =
      FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ) f :=
  by
  ext x
  simp [FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
    SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg, heven]


-- @@ L34-38 verbatim
/-- A zpow/pow cancellation used when simplifying Gaussian prefactors. -/
public lemma zpow_neg_twelve_mul_pow_twelve (s : ℝ) (hs : s ≠ 0) :
    ((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ) = 1 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simpa using (zpow_add₀ hsC (-12 : ℤ) (12 : ℤ)).symm


-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end SpherePacking.Dim24.AFourier
