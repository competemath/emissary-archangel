import OAI.Combinatorics.DiscreteConvexity.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


-- @@ L9-9 verbatim
namespace OAI


-- @@ L11-16 verbatim
/-!
# Symbolic constants for the original-density argument

Only the small factor `32 = 2^5` is evaluated. The number of rows and the
final tuple length remain symbolic powers throughout the construction.
-/


-- @@ L18-18 verbatim
namespace TalagrandDiscreteConvexity


-- @@ L20-21 verbatim
theorem density_rows_gt_one : 1 < (2 : ℕ) ^ 70 :=
  one_lt_pow' (by decide : (1 : ℕ) < 2) (by decide : (70 : ℕ) ≠ 0)


-- @@ L23-24 verbatim
theorem density_rows_pos : 0 < (2 : ℕ) ^ 70 :=
  lt_trans Nat.zero_lt_one density_rows_gt_one


-- @@ L26-27 verbatim
theorem density_tuple_count : 32 * (2 : ℕ) ^ 70 = 2 ^ 75 := by
  rw [show (32 : ℕ) = 2 ^ 5 by decide, ← pow_add]


-- @@ L29-32 verbatim
theorem density_tuple_count_real : (2 : ℝ) ^ 75 = 32 * (2 : ℝ) ^ 70 := by
  calc
    (2 : ℝ) ^ 75 = 2 ^ 5 * 2 ^ 70 := by rw [← pow_add]
    _ = 32 * 2 ^ 70 := by rw [show (2 : ℝ) ^ 5 = 32 by norm_num]


-- @@ L34-41 verbatim
/-- A density loss of at most `1 / (32 L)` spends at most `1 / 32` across rows. -/
theorem density_failure_budget {L a : ℝ} (hL : 0 < L)
    (ha : 1 - 1 / (32 * L) ≤ a) : L * (1 - a) ≤ 1 / 32 := by
  have hbound : 1 - a ≤ 1 / (32 * L) := by linarith
  calc
    L * (1 - a) ≤ L * (1 / (32 * L)) :=
      mul_le_mul_of_nonneg_left hbound hL.le
    _ = 1 / 32 := by field_simp [ne_of_gt hL]


-- @@ L43-43 verbatim
end TalagrandDiscreteConvexity


-- @@ L45-45 verbatim
end OAI
