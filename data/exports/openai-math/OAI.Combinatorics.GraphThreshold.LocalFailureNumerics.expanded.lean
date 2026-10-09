import OAI.Combinatorics.GraphThreshold.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open Finset


-- @@ L12-12 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L14-14 verbatim
theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two


-- @@ L16-16 verbatim
theorem exp_one_lt_three : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three


-- @@ L18-27 verbatim
/-- The strict numerical estimate used to rule out large maximizing
predecessors in the graph hierarchy. -/
theorem predecessor_power_lt_one {r : ℕ} (hr : 1 ≤ r) :
    2 * (17 * Real.exp 1 / 128) ^ r < 1 := by
  have hbase0 : 0 ≤ 17 * Real.exp 1 / 128 := by positivity
  have hbase : 17 * Real.exp 1 / 128 < (1 / 2 : ℝ) := by
    nlinarith [exp_one_lt_three]
  have hp : (17 * Real.exp 1 / 128) ^ r ≤ 17 * Real.exp 1 / 128 :=
    pow_le_of_le_one hbase0 (by linarith) (by omega)
  linarith


-- @@ L29-30 verbatim
theorem exp_neg_fifty_lt_one : Real.exp (-50) < 1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)


-- @@ L32-34 verbatim
theorem one_add_le_exp_one_of_le_exp_neg_fifty {q : ℝ}
    (hq : q ≤ Real.exp (-50)) : 1 + q ≤ Real.exp 1 := by
  linarith [exp_neg_fifty_lt_one, two_lt_exp_one]


-- @@ L36-42 verbatim
theorem one_add_pow_le_exp_nat {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-50)) (m : ℕ) :
    (1 + q) ^ m ≤ Real.exp (m : ℝ) := by
  calc
    (1 + q) ^ m ≤ Real.exp 1 ^ m :=
      pow_le_pow_left₀ (by positivity) (one_add_le_exp_one_of_le_exp_neg_fifty hq) m
    _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul]; simp


-- @@ L44-47 verbatim
theorem two_pow_le_exp_nat (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  calc
    (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) two_lt_exp_one.le m
    _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul]; simp


-- @@ L49-57 verbatim
/-- A term beyond half the capacity has the required exponential decay. -/
theorem large_intersection_power_le {m r : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-50)) (hr : m < 2 * r) :
    q ^ r ≤ Real.exp (-25 * (m : ℝ)) := by
  have hr' : (m : ℝ) < 2 * (r : ℝ) := by exact_mod_cast hr
  calc
    q ^ r ≤ Real.exp (-50) ^ r := pow_le_pow_left₀ hq0 hq r
    _ = Real.exp ((r : ℝ) * (-50)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-25 * (m : ℝ)) := Real.exp_le_exp.mpr (by linarith)


-- @@ L59-61 verbatim
/-- The finite binomial upper tail used by the resampling argument. -/
def largeIntersectionTail (m : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ range (m + 1), if m < 2 * r then (m.choose r : ℝ) * q ^ r else 0


-- @@ L63-77 verbatim
theorem largeIntersectionTail_le {m : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-50)) :
    largeIntersectionTail m q ≤ (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by
  have hsum : (∑ r ∈ range (m + 1), (m.choose r : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  unfold largeIntersectionTail
  calc
    (∑ r ∈ range (m + 1), if m < 2 * r then (m.choose r : ℝ) * q ^ r else 0) ≤
        ∑ r ∈ range (m + 1), (m.choose r : ℝ) * Real.exp (-25 * (m : ℝ)) := by
      apply sum_le_sum
      intro r hr
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (large_intersection_power_le hq0 hq h) (by positivity)
      · positivity
    _ = (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by rw [← sum_mul, hsum]


-- @@ L79-101 verbatim
theorem local_failure_exponential_combine {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
      Real.exp (-9 * (m : ℝ)) := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hterm : Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m *
      Real.exp (-25 * (m : ℝ)) ≤ Real.exp (-10 * (m : ℝ)) := by
    calc
      Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
          Real.exp (10 * (m : ℝ)) * Real.exp (m : ℝ) * Real.exp (-25 * (m : ℝ)) := by
        gcongr
        exact two_pow_le_exp_nat m
      _ = Real.exp (-14 * (m : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-10 * (m : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp (m : ℝ) :=
    two_lt_exp_one.le.trans (Real.exp_le_exp.mpr hm1)
  calc
    Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
      2 * Real.exp (-10 * (m : ℝ)) := by linarith
    _ ≤ Real.exp (m : ℝ) * Real.exp (-10 * (m : ℝ)) := by gcongr
    _ = Real.exp (-9 * (m : ℝ)) := by rw [← Real.exp_add]; congr 1; ring


-- @@ L103-103 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L105-105 verbatim
end


-- @@ L107-107 verbatim
end OAI
