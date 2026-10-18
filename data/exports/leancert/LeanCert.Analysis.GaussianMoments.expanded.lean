import LeanCert.Analysis.PolynomialDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


-- @@ L4-4 verbatim
/-! Integrable polynomial-weighted Gaussian majorants on the positive half-line. -/

-- @@ L5-5 verbatim
namespace LeanCert.Analysis

-- @@ L6-6 verbatim
open MeasureTheory Set


-- @@ L8-12 verbatim
theorem integrableOn_gaussian_moment (m : ℕ) :
    IntegrableOn (fun u : ℝ => u^m * Real.exp (-u^2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (show (-1 : ℝ) < (m : ℝ) by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  simpa using h


-- @@ L14-14 verbatim
end LeanCert.Analysis
