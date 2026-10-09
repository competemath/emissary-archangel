import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
/-! Symbolic estimates for the sixteen-vertex labeling union bound. -/


-- @@ L9-9 verbatim
namespace Paper320


-- @@ L11-16 verbatim
theorem le_ceil_sqrt_sq (M : ℕ) : M ≤ (Nat.ceil (Real.sqrt M))^2 := by
  have hs := Nat.le_ceil (Real.sqrt (M : ℝ))
  have hr := Real.sqrt_nonneg (M : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh : (M : ℝ) ≤ (Nat.ceil (Real.sqrt M) : ℝ)^2 := by nlinarith
  exact_mod_cast hh


-- @@ L18-21 verbatim
theorem labeling_space_large {M : ℕ} (hM : 3 ≤ M) :
    120 ≤ (2*M^2+1)*(2*M^2+1) := by
  have : 19 ≤ 2*M^2+1 := by nlinarith
  nlinarith


-- @@ L23-23 verbatim
end Paper320


-- @@ L25-25 verbatim
end OAI
