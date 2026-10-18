import LeanCert.Tactic.IntervalAuto

-- Test: x + y ≤ 2 on [0,1] × [0,1]

-- @@ L4-5 verbatim
theorem test_2d_sum_le : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x + y ≤ (2 : ℚ) := by
  multivariate_bound


-- @@ L7-8 verbatim
example : ∀ x ∈ Set.Icc (1/2:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) (3/4), x + y ≤ (2 : ℚ) := by
  multivariate_bound


-- @@ L10-11 verbatim
example : ∀ x ∈ Set.Icc (1/2:ℝ) 1, ∀ y ∈ Set.Icc (-3/4:ℝ) (-1/4), (-1/4 : ℚ) ≤ x + y := by
  multivariate_bound
