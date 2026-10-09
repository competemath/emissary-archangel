import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
universe uY uK uT


-- @@ L9-15 verbatim
/-!
# Grouping finite nonnegative weights

An optional slot assignment records which columns were retained. Grouping by
the assigned slot and by a tag preserves every weighted expression that only
depends on those two values. No nonemptiness assumptions are needed.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace MetricEntropyDuality


-- @@ L21-21 verbatim
open scoped BigOperators


-- @@ L23-23 verbatim
variable {Y : Type uY} {K : Type uK} {T : Type uT} [Fintype Y]


-- @@ L25-29 verbatim
/-- Total weight of columns with the specified slot and tag. -/
def groupedWeight (assignment : Y → Option K) (tag : Y → T) (μ : Y → ℝ)
    (k : K) (t : T) : ℝ := by
  classical
  exact ∑ y, if assignment y = some k ∧ tag y = t then μ y else 0


-- @@ L31-40 verbatim
theorem groupedWeight_nonneg (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (k : K) (t : T) :
    0 ≤ groupedWeight assignment tag μ k t := by
  classical
  unfold groupedWeight
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact hμ y
  · exact le_rfl


-- @@ L42-51 verbatim
theorem groupedWeight_le_totalMass (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (k : K) (t : T) :
    groupedWeight assignment tag μ k t ≤ ∑ y, μ y := by
  classical
  unfold groupedWeight
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact hμ y


-- @@ L53-57 verbatim
theorem groupedWeight_le_one (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (k : K) (t : T) :
    groupedWeight assignment tag μ k t ≤ 1 :=
  (groupedWeight_le_totalMass assignment tag μ hμ k t).trans hmass


-- @@ L59-64 verbatim
theorem groupedWeight_eq_zero_of_unused (assignment : Y → Option K)
    (tag : Y → T) (μ : Y → ℝ) (k : K)
    (hunused : ∀ y, assignment y ≠ some k) (t : T) :
    groupedWeight assignment tag μ k t = 0 := by
  classical
  simp [groupedWeight, hunused]


-- @@ L66-66 verbatim
section FiniteGroups


-- @@ L68-68 verbatim
variable [Fintype K] [Fintype T]


-- @@ L70-84 verbatim
/-- Grouping is exact for arbitrary real functions of the slot and tag. -/
theorem sum_groupedWeight_mul (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (B : K → T → ℝ) :
    (∑ k, ∑ t, groupedWeight assignment tag μ k t * B k t) =
      ∑ y, μ y * (match assignment y with
        | none => 0
        | some k => B k (tag y)) := by
  classical
  simp_rw [groupedWeight, Finset.sum_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro y _
  cases assignment y with
  | none => simp
  | some slot => simp [ite_and, ite_mul]


-- @@ L86-99 verbatim
/-- The total grouped weight is exactly the mass of assigned columns. -/
theorem sum_groupedWeight_eq (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) :
    (∑ k, ∑ t, groupedWeight assignment tag μ k t) =
      ∑ y, (match assignment y with
        | none => 0
        | some _ => μ y) := by
  classical
  have h := sum_groupedWeight_mul assignment tag μ (fun _ _ => 1)
  simp only [mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y _
  cases assignment y <;> simp


-- @@ L101-109 verbatim
theorem sum_groupedWeight_le_totalMass (assignment : Y → Option K)
    (tag : Y → T) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) :
    (∑ k, ∑ t, groupedWeight assignment tag μ k t) ≤ ∑ y, μ y := by
  rw [sum_groupedWeight_eq]
  apply Finset.sum_le_sum
  intro y _
  cases assignment y with
  | none => exact hμ y
  | some k => exact le_rfl


-- @@ L111-114 verbatim
theorem sum_groupedWeight_le_one (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1) :
    (∑ k, ∑ t, groupedWeight assignment tag μ k t) ≤ 1 :=
  (sum_groupedWeight_le_totalMass assignment tag μ hμ).trans hmass


-- @@ L116-116 verbatim
end FiniteGroups


-- @@ L118-118 verbatim
end MetricEntropyDuality


-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
end OAI
