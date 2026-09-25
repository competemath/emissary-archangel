module
public import SpherePacking.Dim8.MagicFunction.a.Schwartz.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI5Kernel
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12ContourMain
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12FourierMain
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12Prelude


-- @@ L9-17 verbatim
/-!
# Fourier Permutations

We show that the Fourier transform permutes the integral pieces defining `a`, and deduce that `a`
is a Fourier eigenfunction.

## Main statements
* `eig_a`
-/


-- @@ L19-19 verbatim
namespace MagicFunction.a.Fourier


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open scoped FourierTransform RealInnerProductSpace Topology

-- @@ L24-24 verbatim
open MagicFunction.a.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap Filter


-- @@ L26-26 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L28-28 verbatim
section Integral_Permutations


-- @@ L30-30 verbatim
open MeasureTheory Set Complex Real


-- @@ L32-43 verbatim
theorem perm_I₁_I₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) =
      (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) := by
  ext w
  simp only
    [FourierTransform.fourierCLE_apply, FourierAdd.fourier_add, add_apply, I₃_apply, I₄_apply,
      fourier_coe]
  rw [fourier_I₁_eq_curveIntegral (w := w), fourier_I₂_eq_curveIntegral (w := w),
    I₃'_add_I₄'_eq_curveIntegral_segments (r := ‖w‖ ^ 2)]
  simpa using (perm_I12_contour (r := ‖w‖ ^ 2))

-- Should use results from `RadialSchwartz.Radial` to prove the reverse.


-- @@ L45-51 verbatim
theorem perm_₃_I₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) (I₃ + I₄ : SchwartzMap ℝ⁸ ℂ) =
      (I₁ + I₂ : SchwartzMap ℝ⁸ ℂ) := by
  rw [← perm_I₁_I₂]
  simpa using radial_inversion (I₁ + I₂) (fun _ => by simp [I₁, I₂])

-- should use fourier_involution and the radial symmetry of I₅

-- @@ L52-54 verbatim
theorem perm_I₆ : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) I₆ = I₅ := by
  simpa [← perm_I₅] using radial_inversion I₅ (fun _ => by
    simp [I₅, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply])


-- @@ L56-56 verbatim
end Integral_Permutations


-- @@ L58-58 verbatim
section Eigenfunction


-- @@ L60-65 verbatim
/-- The magic function `a` is invariant under the Fourier transform. -/
public theorem eig_a : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) a = a := by
  rw [a_eq_sum_integrals_SchwartzIntegrals,
    show I₁ + I₂ + I₃ + I₄ + I₅ + I₆ = (I₁ + I₂) + (I₃ + I₄) + I₅ + I₆ by ac_rfl,
    map_add, map_add, map_add, perm_I₁_I₂, perm_I₅, perm_₃_I₄, perm_I₆]
  ac_rfl


-- @@ L67-67 verbatim
end Eigenfunction

-- @@ L68-68 verbatim
end

-- @@ L69-69 verbatim
end MagicFunction.a.Fourier
