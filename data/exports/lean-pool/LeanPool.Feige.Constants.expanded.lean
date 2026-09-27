/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds


-- @@ L11-20 verbatim
/-!
# The sharp finite-dimensional constant

This file records the elementary real-analysis facts about

`bₙ,₁ = (n / (n + 1))ⁿ`

which is the `δ = 1` value of the second branch in (1.1).  The
probability-theoretic proof is kept in later modules.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Feige


-- @@ L26-26 verbatim
open Filter Topology


-- @@ L28-30 verbatim
/-- The unit-slack sharp constant `bₙ,₁` in dimension `n`. -/
noncomputable def sharpConstant (n : ℕ) : ℝ :=
  ((n : ℝ) / (n + 1)) ^ n


-- @@ L32-33 verbatim
@[simp] theorem sharpConstant_zero : sharpConstant 0 = 1 := by
  simp [sharpConstant]


-- @@ L35-41 verbatim
/-- The sharp constant is positive in every dimension, including dimension zero. -/
theorem sharpConstant_pos (n : ℕ) : 0 < sharpConstant n := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [sharpConstant]
      positivity


-- @@ L43-45 verbatim
/-- The sharp constant is nonnegative. -/
theorem sharpConstant_nonneg (n : ℕ) : 0 ≤ sharpConstant n :=
  (sharpConstant_pos n).le


-- @@ L47-52 verbatim
/-- The sharp constant is at most one. -/
theorem sharpConstant_le_one (n : ℕ) : sharpConstant n ≤ 1 := by
  simp only [sharpConstant]
  apply pow_le_one₀
  · positivity
  · exact (div_le_one (by positivity)).2 (by norm_num)


-- @@ L54-60 verbatim
/-- For positive `n`, the sharp constant is the reciprocal of the standard
sequence converging to `exp 1`. -/
private theorem sharpConstant_eq_inv (n : ℕ) (hn : n ≠ 0) :
    sharpConstant n = ((1 + (1 : ℝ) / n) ^ n)⁻¹ := by
  rw [sharpConstant, ← inv_pow]
  congr 1
  field_simp


-- @@ L62-79 verbatim
/-- The finite-dimensional sharp constant is strictly larger than `exp (-1)`. -/
theorem exp_neg_one_lt_sharpConstant {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) < sharpConstant n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase :
      (1 + (1 : ℝ) / n) ^ n < (Real.exp ((1 : ℝ) / n)) ^ n := by
    apply pow_lt_pow_left₀
    · simpa [add_comm] using Real.add_one_lt_exp (one_div_ne_zero hnR.ne')
    · positivity
    · exact hn0
  have hexp : (Real.exp ((1 : ℝ) / n)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [sharpConstant_eq_inv n hn0, Real.exp_neg]
  apply inv_lt_inv₀ (Real.exp_pos 1) (by positivity) |>.2
  exact hbase.trans_eq hexp


-- @@ L81-89 verbatim
/-- The finite-dimensional sharp constants converge to `exp (-1)`. -/
theorem tendsto_sharpConstant :
    Tendsto sharpConstant atTop (𝓝 (Real.exp (-1))) := by
  have h :=
    (Real.tendsto_one_add_div_pow_exp 1).inv₀ (Real.exp_ne_zero 1)
  rw [← Real.exp_neg] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (sharpConstant_eq_inv n hn).symm


-- @@ L91-91 verbatim
end Feige
