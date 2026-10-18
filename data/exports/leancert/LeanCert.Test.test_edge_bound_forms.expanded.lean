import LeanCert.Tactic.IntervalAuto


-- @@ L3-4 verbatim
theorem edge_bound_setof : ∀ x ∈ {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1}, x * x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L6-7 verbatim
theorem edge_bound_and : ∀ x : ℝ, (0:ℝ) ≤ x ∧ x ≤ 1 → x * x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L9-10 verbatim
theorem edge_bound_arrow : ∀ x : ℝ, (0:ℝ) ≤ x → x ≤ 1 → x * x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L12-13 verbatim
theorem edge_bound_decimal : ∀ x ∈ Set.Icc (-0.5:ℝ) (1/3), x * x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L15-16 verbatim
theorem edge_bound_scientific : ∀ x ∈ Set.Icc (0:ℝ) (2.5:ℝ), x ≤ (3 : ℚ) := by
  certify_bound
