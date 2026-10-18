import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic


-- @@ L4-4 verbatim
/-! Elementary complex trigonometric majorants for integral certification. -/

-- @@ L5-5 verbatim
namespace LeanCert.Analysis


-- @@ L7-13 verbatim
theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z*Complex.I)) (Complex.exp (-z*Complex.I))
  rw [← Complex.two_cos, norm_mul] at h
  have h1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  norm_num [Complex.norm_exp, Complex.mul_re] at h
  linarith


-- @@ L15-15 verbatim
end LeanCert.Analysis
