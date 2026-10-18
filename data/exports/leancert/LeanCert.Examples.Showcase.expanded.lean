/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic
import LeanCert.QProduct


-- @@ L9-19 verbatim
/-!
# LeanCert Showcase

Six ordinary mathematical statements covering the main public proof shapes.
Every theorem deliberately uses the semantic `leancert` front door where that
front door applies. The q-product example demonstrates a domain certificate
whose Boolean premise is checked natively and lifted by a Golden Theorem.

The mirrored guide records the selected strategy, trust boundary, and measured
runtime for each theorem.
-/


-- @@ L21-21 verbatim
namespace LeanCert.Examples.Showcase


-- @@ L23-23 verbatim
open LeanCert.QProduct


-- @@ L25-27 verbatim
/-- A closed transcendental inequality. -/
theorem log_two_lt_seven_tenths : Real.log 2 < 7 / 10 := by
  leancert


-- @@ L29-30 verbatim
private example : Real.log 2 < 7 / 10 := by
  interval_auto 10


-- @@ L32-35 verbatim
/-- One certificate proves the nonlinear bound for every point of `[0, 1]`. -/
theorem exp_mul_cos_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  leancert


-- @@ L37-39 verbatim
private example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  certify_bound 10


-- @@ L41-45 verbatim
/-- Semantic routing recognizes a two-dimensional box. -/
theorem two_variable_box_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      x + y ≤ (2 : ℚ) := by
  leancert


-- @@ L47-50 verbatim
private example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      x + y ≤ (2 : ℚ) := by
  multivariate_bound


-- @@ L52-55 verbatim
/-- Interval sign and Newton certificates establish the unique square root. -/
theorem sqrt_two_unique :
    ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  leancert


-- @@ L57-59 verbatim
private example :
    ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  interval_unique_root


-- @@ L61-64 verbatim
/-- Rational-polynomial integration is checked exactly. -/
theorem square_integral :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert


-- @@ L66-68 verbatim
private example :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  integral_exact


-- @@ L70-78 verbatim
/-- A checked finite q-product bounds the prime-indexed limiting constant. -/
theorem prime_lambda_enclosure :
    ((19 / 36 : ℚ) : ℝ) ≤ primeLambda ∧
      primeLambda ≤ ((7 / 12 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc
    shiftedTrunc_sub_tail_le_primeLambda
    1 (19 / 36) (7 / 12)
    (by native_decide)


-- @@ L80-80 verbatim
end LeanCert.Examples.Showcase
