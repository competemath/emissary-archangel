module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI56FourierPermutation


-- @@ L6-14 verbatim
/-!
# Fourier eigenfunction in dimension 24

This file packages the permutation identities into the statement that the dimension-24
magic function `a` is a Fourier eigenfunction.

## Main statement
* `eig_a`
-/


-- @@ L16-16 verbatim
section

-- @@ L17-17 verbatim
namespace SpherePacking.Dim24


-- @@ L19-19 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L20-20 verbatim
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)


-- @@ L22-36 verbatim
/-- The Fourier transform of the magic function `a` is `a`. -/
public theorem eig_a : FT a = a := by
  -- Expand `a` and use the permutation identities term-by-term.
  have ha :
      a =
        (AFourier.I₁ + AFourier.I₂) + (AFourier.I₃ + AFourier.I₄) + AFourier.I₅ + AFourier.I₆ := by
    refine (AFourier.a_eq_sum_integrals.trans ?_)
    abel
  rw [ha]
  have hperm :
      FT ((AFourier.I₁ + AFourier.I₂) + (AFourier.I₃ + AFourier.I₄) + AFourier.I₅ + AFourier.I₆) =
        (AFourier.I₃ + AFourier.I₄) + (AFourier.I₁ + AFourier.I₂) + AFourier.I₆ + AFourier.I₅ := by
    rw [map_add, map_add, map_add, AFourier.perm_I₁_I₂, AFourier.perm_I₃_I₄,
      AFourier.PermI56.perm_I₅, AFourier.PermI56.perm_I₆]
  simpa [ha] using hperm.trans (by abel)

-- @@ L37-37 verbatim
end SpherePacking.Dim24

-- @@ L38-38 verbatim
end
