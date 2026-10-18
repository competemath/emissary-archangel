import LeanCert.Tactic.IntervalAuto


-- @@ L3-3 verbatim
open LeanCert.Core


-- @@ L5-5 verbatim
abbrev Icc01 : Set ℝ := Set.Icc (0:ℝ) 1


-- @@ L7-8 verbatim
theorem edge_bound_def_seticc : ∀ x ∈ Icc01, x * x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L10-11 verbatim
theorem edge_bound_neg_interval : ∀ x ∈ Set.Icc (-2:ℝ) 2, x * x ≤ (4 : ℚ) := by
  certify_bound


-- @@ L13-14 verbatim
theorem edge_bound_abs_interval : ∀ x ∈ Set.Icc (-1:ℝ) 1, abs x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L16-17 verbatim
theorem edge_bound_sqrt_upper : ∀ x ∈ Set.Icc (0:ℝ) 4, Real.sqrt x ≤ (2 : ℚ) := by
  certify_bound


-- @@ L19-20 verbatim
theorem edge_bound_rpow_half : ∀ x ∈ Set.Icc (0:ℝ) 4, x ^ ((1:ℝ) / 2) ≤ (2 : ℚ) := by
  certify_bound


-- @@ L22-23 verbatim
theorem edge_bound_rpow_inv_two : ∀ x ∈ Set.Icc (0:ℝ) 4, x ^ ((2:ℝ)⁻¹) ≤ (2 : ℚ) := by
  certify_bound


-- @@ L25-27 verbatim
theorem edge_bound_rpow_three_halves :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ^ ((3:ℝ) / 2) ≤ (1 : ℚ) := by
  certify_bound


-- @@ L29-31 verbatim
theorem edge_bound_rpow_one_point_five :
    ∀ x ∈ Set.Icc (0:ℝ) 1, x ^ (1.5:ℝ) ≤ (1 : ℚ) := by
  certify_bound


-- @@ L33-34 verbatim
theorem edge_bound_sinh_upper : ∀ x ∈ Set.Icc (0:ℝ) 2, Real.sinh x ≤ (4 : ℚ) := by
  certify_bound 15


-- @@ L36-37 verbatim
theorem edge_bound_cosh_lower : ∀ x ∈ Set.Icc (-1:ℝ) 1, (1 : ℚ) ≤ Real.cosh x := by
  certify_bound


-- @@ L39-40 verbatim
theorem edge_bound_tanh_upper : ∀ x ∈ Set.Icc (-2:ℝ) 2, Real.tanh x ≤ (1 : ℚ) := by
  certify_bound


-- @@ L42-43 verbatim
theorem edge_bound_tanh_lower : ∀ x ∈ Set.Icc (-2:ℝ) 2, (-1 : ℚ) ≤ Real.tanh x := by
  certify_bound


-- @@ L45-46 verbatim
theorem edge_bound_pi_shift : ∀ x ∈ Icc01, x + Real.pi ≤ (5 : ℚ) := by
  certify_bound


-- @@ L48-49 verbatim
theorem edge_bound_strict : ∀ x ∈ Icc01, x * x < (2 : ℚ) := by
  certify_bound
