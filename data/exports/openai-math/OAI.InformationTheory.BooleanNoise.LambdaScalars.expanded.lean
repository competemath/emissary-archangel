import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped BigOperators Topology

-- @@ L10-10 verbatim
open Set Filter


-- @@ L12-12 verbatim
namespace LeanBlast.CourtadeKumar


-- @@ L14-14 verbatim
def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z


-- @@ L16-16 verbatim
@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]


-- @@ L18-19 verbatim
theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]


-- @@ L21-25 verbatim
theorem mul_lambda (z : ℝ) : z * lambda z = -Real.log (1 - z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [lambda_of_ne_zero hz]
    field_simp


-- @@ L27-41 verbatim
theorem hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by
  by_cases hz : z = 0
  · subst z
    rw [lambda_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  · have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |z| < 1 by rwa [abs_of_nonneg hz0])).div_const z
    rw [lambda_of_ne_zero hz]
    convert hlog using 1
    ext j
    rw [pow_succ]
    field_simp


-- @@ L43-45 verbatim
theorem summable_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) :=
  (hasSum_lambda hz0 hz1).summable


-- @@ L47-51 verbatim
theorem monotoneOn_lambda : MonotoneOn lambda (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply hasSum_le _ (hasSum_lambda hx.1 hx.2) (hasSum_lambda hy.1 hy.2)
  intro j
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hxy j) (by positivity)


-- @@ L53-54 verbatim
theorem one_le_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 1 ≤ lambda z := by
  simpa using monotoneOn_lambda (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hz0, hz1⟩ hz0


-- @@ L56-57 verbatim
theorem lambda_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 ≤ lambda z :=
  zero_le_one.trans (one_le_lambda hz0 hz1)


-- @@ L59-59 verbatim
end LeanBlast.CourtadeKumar


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
