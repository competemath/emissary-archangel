module
public import SpherePacking.Dim8.MagicFunction.g.Basic
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.PureImaginary
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.FourierPermutations



-- @@ L8-17 verbatim
/-!
# Real-valuedness of `g`

This file proves that `g` and its Fourier transform are real-valued. These lemmas are part of
blueprint Theorem `thm:g1` / `thm:g`.

## Main statements
* `MagicFunction.g.CohnElkies.g_real`
* `MagicFunction.g.CohnElkies.g_real_fourier`
-/


-- @@ L19-19 verbatim
namespace MagicFunction.g.CohnElkies


-- @@ L21-21 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L22-22 verbatim
open Real Complex


-- @@ L24-24 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L26-26 verbatim
open MagicFunction.FourierEigenfunctions


-- @@ L28-28 verbatim
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)


-- @@ L30-31 verbatim
private theorem ofReal_re_eq (z : ℂ) (hz : z.im = 0) : (↑z.re : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])


-- @@ L33-39 verbatim
/-- The magic function `g` is real-valued. -/
public theorem g_real : ∀ x : ℝ⁸, (↑(g x).re : ℂ) = g x := by
  intro x
  refine ofReal_re_eq (g x) ?_
  simp [g, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.sub_im, Complex.mul_im, a_pureImag (x := x), b_pureImag (x := x),
    div_eq_mul_inv, Complex.mul_re]


-- @@ L41-52 verbatim
/-- The Fourier transform `𝓕 g` is real-valued. -/
public theorem g_real_fourier : ∀ x : ℝ⁸, (↑((𝓕 g x).re : ℂ)) = (𝓕 g x) := by
  intro x
  refine ofReal_re_eq (𝓕 g x) ?_
  have hFg : FT g = ((↑π * I) / 8640) • a + (I / (240 * (↑π))) • b := by
    simp [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
      -FourierTransform.fourierCLE_apply]
  have hF : (𝓕 g) = FT g := by simp
  change ((𝓕 g) x).im = 0
  rw [hF, hFg]
  simp [SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
    a_pureImag (x := x), b_pureImag (x := x), div_eq_mul_inv, Complex.mul_re]


-- @@ L54-54 verbatim
end MagicFunction.g.CohnElkies
