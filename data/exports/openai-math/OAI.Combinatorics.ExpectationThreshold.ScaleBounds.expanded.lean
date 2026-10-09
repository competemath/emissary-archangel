import OAI.Combinatorics.ExpectationThreshold.ProbabilityColors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega


-- @@ L10-10 verbatim
namespace OAI


-- @@ L12-19 verbatim
/-!
# The largest admissible scale

The cutoff is constructed as the first index whose next scale fails.
Its existence follows from the Archimedean property and the elementary
lower bound `scaleSum s ≥ s`. No finite search bound or computed large
power is used.
-/


-- @@ L21-21 verbatim
namespace TalagrandThreshold


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-27 verbatim
theorem scaleSum_succ (s : ℕ) :
    scaleSum (s + 1) = scaleSum s + (256 : ℝ) ^ (s + 1) := by
  simp only [scaleSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]


-- @@ L29-33 verbatim
theorem scaleSum_monotone : Monotone scaleSum := by
  apply monotone_nat_of_le_succ
  intro s
  rw [scaleSum_succ]
  exact le_add_of_nonneg_right (by positivity)


-- @@ L35-40 verbatim
theorem scaleSum_ge_nat (s : ℕ) : (s : ℝ) ≤ scaleSum s := by
  calc
    (s : ℝ) = ∑ _i : Fin s, (1 : ℝ) := by simp
    _ ≤ scaleSum s := by
      unfold scaleSum
      exact Finset.sum_le_sum fun _ _ => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 256)


-- @@ L42-49 verbatim
/-- The finite geometric sum is at most twice its largest power. -/
theorem scaleSum_le_two_pow (s : ℕ) : scaleSum s ≤ 2 * (256 : ℝ) ^ s := by
  induction s with
  | zero => simp [scaleSum_zero]
  | succ s ih =>
      rw [scaleSum_succ, pow_succ (256 : ℝ) s]
      have hpow : 0 ≤ (256 : ℝ) ^ s := by positivity
      nlinarith


-- @@ L51-58 verbatim
private theorem half_geometric_sum_identity (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) + (1 / 2 : ℝ) ^ s = 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      rw [pow_succ (1 / 2 : ℝ) s]
      nlinarith


-- @@ L60-64 verbatim
theorem half_geometric_sum_le_one (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) ≤ 1 := by
  have h := half_geometric_sum_identity s
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
  linarith


-- @@ L66-78 verbatim
/-- Some next scale fails whenever the density is positive. -/
theorem scale_next_fail_exists {p : ℝ} (hp : 0 < p) :
    ∃ s : ℕ, 1 / 2 < p * scaleSum (s + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 / 2 : ℝ) / p)
  refine ⟨n, ?_⟩
  have hnp : (1 / 2 : ℝ) < (n : ℝ) * p := (div_lt_iff₀ hp).mp hn
  have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    (1 / 2 : ℝ) < p * (n : ℝ) := by simpa only [mul_comm] using hnp
    _ ≤ p * scaleSum (n + 1) :=
      mul_le_mul_of_nonneg_left (hcast.trans (scaleSum_ge_nat (n + 1))) hp.le


-- @@ L80-83 verbatim
/-- The largest admissible scale; its irrelevant nonpositive-density value is zero. -/
noncomputable def maxScale (p : ℝ) : ℕ := by
  classical
  exact if hp : 0 < p then Nat.find (scale_next_fail_exists hp) else 0


-- @@ L85-88 verbatim
private theorem maxScale_eq_find {p : ℝ} (hp : 0 < p) :
    maxScale p = Nat.find (scale_next_fail_exists hp) := by
  classical
  simp only [maxScale, dite_eq_left hp]


-- @@ L90-94 verbatim
theorem maxScale_next_fail {p : ℝ} (hp : 0 < p) :
    1 / 2 < p * scaleSum (maxScale p + 1) := by
  classical
  rw [maxScale_eq_find hp]
  exact Nat.find_spec (scale_next_fail_exists hp)


-- @@ L96-105 verbatim
theorem maxScale_admissible {p : ℝ} (hp : 0 < p) :
    p * scaleSum (maxScale p) ≤ 1 / 2 := by
  classical
  cases hs : maxScale p with
  | zero => simp [scaleSum_zero]
  | succ s =>
      have hslt : s < Nat.find (scale_next_fail_exists hp) := by
        rw [← maxScale_eq_find hp, hs]
        exact Nat.lt_succ_self s
      exact le_of_not_gt (Nat.find_min (scale_next_fail_exists hp) hslt)


-- @@ L107-114 verbatim
/-- Every admissible integer is at most the constructed cutoff. -/
theorem maxScale_largest {p : ℝ} (hp : 0 < p) {t : ℕ}
    (ht : p * scaleSum t ≤ 1 / 2) : t ≤ maxScale p := by
  by_contra h
  have hst : maxScale p + 1 ≤ t := by omega
  have hle : p * scaleSum (maxScale p + 1) ≤ p * scaleSum t :=
    mul_le_mul_of_nonneg_left (scaleSum_monotone hst) hp.le
  exact (not_le_of_gt (maxScale_next_fail hp)) (hle.trans ht)


-- @@ L116-119 verbatim
/-- The exact pair of cutoff inequalities used by the rounding argument. -/
theorem exists_scale {p : ℝ} (hp : 0 < p) :
    ∃ s : ℕ, p * scaleSum s ≤ 1 / 2 ∧ 1 / 2 < p * scaleSum (s + 1) :=
  ⟨maxScale p, maxScale_admissible hp, maxScale_next_fail hp⟩


-- @@ L121-135 verbatim
/-- Failure at the next scale controls the residual color contribution. -/
theorem tail_lt_four_mul_p {p : ℝ} {s : ℕ} (hp : 0 < p)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    1 / (512 : ℝ) ^ (s + 1) < 4 * p := by
  have hsum : p * scaleSum (s + 1) ≤ p * (2 * (256 : ℝ) ^ (s + 1)) :=
    mul_le_mul_of_nonneg_left (scaleSum_le_two_pow (s + 1)) hp.le
  have hDpos : 0 < (256 : ℝ) ^ (s + 1) := by positivity
  have hDB : (256 : ℝ) ^ (s + 1) ≤ (512 : ℝ) ^ (s + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  calc
    1 / (512 : ℝ) ^ (s + 1) ≤ 1 / (256 : ℝ) ^ (s + 1) :=
      one_div_le_one_div_of_le hDpos hDB
    _ < 4 * p := by
      apply (div_lt_iff₀ hDpos).mpr
      nlinarith


-- @@ L137-139 verbatim
theorem maxScale_tail_lt {p : ℝ} (hp : 0 < p) :
    1 / (512 : ℝ) ^ (maxScale p + 1) < 4 * p :=
  tail_lt_four_mul_p hp (maxScale_next_fail hp)


-- @@ L141-141 verbatim
end TalagrandThreshold


-- @@ L143-143 verbatim
end OAI
