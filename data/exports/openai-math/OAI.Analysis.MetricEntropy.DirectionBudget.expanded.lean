import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-13 verbatim
/-!
# The numerical budget for robust directions

The scalar expression in the finite union bound is strictly below one
for a sufficiently large prime chosen after the other finite parameters.
-/


-- @@ L15-15 verbatim
namespace MetricEntropyDuality


-- @@ L17-30 verbatim
/-- The union-bound expression after substituting `w = 2 * D`. -/
theorem direction_bad_event_bound_eq (D h : ℕ) (u p : ℝ) (hp : p ≠ 0) :
    p ^ D * u ^ (h * (2 * D)) * ((h : ℝ) / p) ^ (2 * D) =
      (((h : ℝ) ^ 2 * u ^ (2 * h)) / p) ^ D := by
  have hexp : h * (2 * D) = (2 * h) * D := by ring
  have hbase : p * u ^ (2 * h) * ((h : ℝ) / p) ^ 2 =
      ((h : ℝ) ^ 2 * u ^ (2 * h)) / p := by
    field_simp [hp]
  calc
    p ^ D * u ^ (h * (2 * D)) * ((h : ℝ) / p) ^ (2 * D) =
        (p * u ^ (2 * h) * ((h : ℝ) / p) ^ 2) ^ D := by
      rw [hexp, pow_mul u (2 * h) D, pow_mul ((h : ℝ) / p) 2 D,
        mul_pow, mul_pow]
    _ = (((h : ℝ) ^ 2 * u ^ (2 * h)) / p) ^ D := by rw [hbase]


-- @@ L32-43 verbatim
/-- The last-prime threshold makes the actual counting bound strictly less
than one. No positivity of `h` or `u` is needed for this scalar implication. -/
theorem direction_bad_event_bound_lt_one {D h u p : ℕ} (hD : 0 < D)
    (hp : h ^ 2 * u ^ (2 * h) < p) :
    (p : ℝ) ^ D * (u : ℝ) ^ (h * (2 * D)) *
        ((h : ℝ) / p) ^ (2 * D) < 1 := by
  have hp₀ : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (h ^ 2 * u ^ (2 * h))) hp)
  rw [direction_bad_event_bound_eq D h (u : ℝ) (p : ℝ) (ne_of_gt hp₀)]
  apply pow_lt_one₀ (by positivity) _ (Nat.ne_of_gt hD)
  apply (div_lt_one hp₀).mpr
  exact_mod_cast hp


-- @@ L45-45 verbatim
end MetricEntropyDuality


-- @@ L47-47 verbatim
end OAI
