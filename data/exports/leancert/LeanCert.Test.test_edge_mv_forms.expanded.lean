import LeanCert.Tactic.Discovery


-- @@ L3-8 verbatim
theorem edge_minimize_mv_and :
    ∃ m : ℚ,
      ∀ x : ℝ, (0:ℝ) ≤ x ∧ x ≤ 1 →
      ∀ y : ℝ, (0:ℝ) ≤ y ∧ y ≤ 1 →
      x * x + y * y ≥ m := by
  interval_minimize_mv


-- @@ L10-15 verbatim
theorem edge_minimize_mv_arrow :
    ∃ m : ℚ,
      ∀ x : ℝ, (0:ℝ) ≤ x → x ≤ 1 →
      ∀ y : ℝ, (0:ℝ) ≤ y → y ≤ 1 →
      x * x + y * y ≥ m := by
  interval_minimize_mv


-- @@ L17-22 verbatim
theorem edge_maximize_mv_setof :
    ∃ M : ℚ,
      ∀ x ∈ {x : ℝ | (0:ℝ) ≤ x ∧ x ≤ 1},
      ∀ y ∈ {y : ℝ | (0:ℝ) ≤ y ∧ y ≤ 1},
      x + y ≤ M := by
  interval_maximize_mv
