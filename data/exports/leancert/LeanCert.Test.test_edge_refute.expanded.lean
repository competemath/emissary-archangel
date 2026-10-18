import LeanCert.Tactic.Refute
import LeanCert.Tactic.IntervalAuto


-- @@ L4-4 verbatim
open LeanCert.Core


-- @@ L6-7 verbatim
/-- IntervalRat domain to exercise interval_refute on non-Set.Icc intervals. -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L9-11 verbatim
theorem edge_refute_intervalrat : ∀ x ∈ I01, x * x ≤ (1 : ℚ) := by
  interval_refute
  certify_bound


-- @@ L13-15 verbatim
theorem edge_refute_strict_intervalrat : ∀ x ∈ I01, x * x < (2 : ℚ) := by
  interval_refute
  certify_bound
