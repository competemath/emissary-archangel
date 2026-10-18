import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.IntervalAuto


-- @@ L4-5 verbatim
theorem edge_decide_exp : Real.exp (1:ℝ) ≤ (3 : ℚ) := by
  interval_decide 15


-- @@ L7-8 verbatim
theorem edge_decide_sqrt : Real.sqrt (2:ℝ) ≤ (2 : ℚ) := by
  interval_decide


-- @@ L10-11 verbatim
theorem edge_decide_pi : Real.pi < (4 : ℚ) := by
  interval_decide


-- @@ L13-14 verbatim
theorem edge_decide_sin : Real.sin (1:ℝ) < (1 : ℚ) := by
  interval_decide


-- @@ L16-17 verbatim
theorem edge_fast_bound : ∀ x ∈ Set.Icc (0:ℝ) 1, x * x ≤ (1 : ℚ) := by
  certify_bound (trust := auto)


-- @@ L19-20 verbatim
theorem edge_fast_bound_precise : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.sin x ≤ (1 : ℚ) := by
  certify_bound 20 (trust := auto)


-- @@ L22-23 verbatim
theorem edge_fast_bound_quick : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ (3 : ℚ) := by
  certify_bound 5 (trust := auto)
