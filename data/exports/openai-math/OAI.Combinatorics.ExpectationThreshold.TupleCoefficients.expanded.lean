import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


-- @@ L9-9 verbatim
namespace OAI


-- @@ L11-17 verbatim
/-!
# Coefficients for the finite tuple estimate

Replacing `e` by `3` gives the coefficients `3 / 64^(i+1)`. Their finite
sum has an explicit positive remainder below `1 / 21`. A finite product
inequality then bounds the product of their complements from below.
-/


-- @@ L19-19 verbatim
namespace TalagrandThreshold


-- @@ L21-21 verbatim
open scoped BigOperators


-- @@ L23-25 verbatim
/-- The convenient rational upper bound on the selector's coefficient. -/
noncomputable def tupleCoefficient (i : ℕ) : ℝ :=
  3 / 64 ^ (i + 1)


-- @@ L27-31 verbatim
theorem tupleCoefficient_eq (i : ℕ) :
    tupleCoefficient i = (3 / 64 : ℝ) * (1 / 64 : ℝ) ^ i := by
  simp only [tupleCoefficient, pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul,
    inv_pow]
  ring


-- @@ L33-35 verbatim
theorem tupleCoefficient_pos (i : ℕ) : 0 < tupleCoefficient i := by
  unfold tupleCoefficient
  positivity


-- @@ L37-38 verbatim
theorem tupleCoefficient_nonneg (i : ℕ) : 0 ≤ tupleCoefficient i :=
  (tupleCoefficient_pos i).le


-- @@ L40-44 verbatim
theorem tupleCoefficient_le_first (i : ℕ) : tupleCoefficient i ≤ 3 / 64 := by
  rw [tupleCoefficient_eq]
  have hpow : (1 / 64 : ℝ) ^ i ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith


-- @@ L46-47 verbatim
theorem tupleCoefficient_lt_one (i : ℕ) : tupleCoefficient i < 1 :=
  lt_of_le_of_lt (tupleCoefficient_le_first i) (by norm_num)


-- @@ L49-59 verbatim
/-- The exact finite geometric identity, including the empty sum. -/
theorem sum_tupleCoefficient_add_remainder (s : ℕ) :
    (∑ i : Fin s, tupleCoefficient i.val) +
      (1 / 21 : ℝ) * (1 / 64 : ℝ) ^ s = 1 / 21 := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [tupleCoefficient_eq s, pow_succ]
    nlinarith [ih]


-- @@ L61-64 verbatim
theorem sum_tupleCoefficient_lt (s : ℕ) :
    (∑ i : Fin s, tupleCoefficient i.val) < 1 / 21 := by
  have hrem : 0 < (1 / 21 : ℝ) * (1 / 64 : ℝ) ^ s := by positivity
  linarith [sum_tupleCoefficient_add_remainder s]


-- @@ L66-68 verbatim
theorem sum_tupleCoefficient_le (s : ℕ) :
    (∑ i : Fin s, tupleCoefficient i.val) ≤ 1 / 21 :=
  (sum_tupleCoefficient_lt s).le


-- @@ L70-86 verbatim
/-- A finite product loses at most the sum of its factors' deficits. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (h0 : ∀ i, 0 ≤ c i) (h1 : ∀ i, c i ≤ 1) :
    1 - ∑ i, c i ≤ ∏ i, (1 - c i) := by
  classical
  suffices h : ∀ s : Finset ι,
      1 - ∑ i ∈ s, c i ≤ ∏ i ∈ s, (1 - c i) by
    exact h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, c i :=
      Finset.sum_nonneg (fun i _ => h0 i)
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (h1 a))
    nlinarith [mul_nonneg (h0 a) hs]


-- @@ L88-93 verbatim
theorem prod_one_sub_tupleCoefficient_gt (s : ℕ) :
    (20 / 21 : ℝ) < ∏ i : Fin s, (1 - tupleCoefficient i.val) := by
  have hprod := one_sub_sum_le_prod_one_sub (fun i : Fin s => tupleCoefficient i.val)
    (fun i => tupleCoefficient_nonneg i.val) (fun i => (tupleCoefficient_lt_one i.val).le)
  have hsum := sum_tupleCoefficient_lt s
  linarith


-- @@ L95-95 verbatim
end TalagrandThreshold


-- @@ L97-97 verbatim
end OAI
