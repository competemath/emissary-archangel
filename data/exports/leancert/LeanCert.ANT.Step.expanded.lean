/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import LeanCert.Cert.Interval


-- @@ L11-17 verbatim
/-!
# Finite step-sum certificates

This module provides the small reusable layer needed by arithmetic step
functions: a semantic real-valued sequence together with computable rational
lower and upper envelopes.
-/


-- @@ L19-19 verbatim
namespace LeanCert.ANT


-- @@ L21-21 verbatim
open scoped BigOperators


-- @@ L23-34 verbatim
/-- A real-valued sequence with rational pointwise lower and upper envelopes. -/
structure StepFn where
  /-- Semantic value. -/
  value : Nat → ℝ
  /-- Computable rational lower envelope. -/
  lowerRat : Nat → ℚ
  /-- Computable rational upper envelope. -/
  upperRat : Nat → ℚ
  /-- Lower-envelope correctness. -/
  lower_correct : ∀ n, (lowerRat n : ℝ) ≤ value n
  /-- Upper-envelope correctness. -/
  upper_correct : ∀ n, value n ≤ (upperRat n : ℝ)


-- @@ L36-38 verbatim
/-- Exact rational lower sum over a finite integer interval. -/
def stepLowerRat (S : StepFn) (m N : Nat) : ℚ :=
  ∑ n ∈ Finset.Icc m N, S.lowerRat n


-- @@ L40-42 verbatim
/-- Exact rational upper sum over a finite integer interval. -/
def stepUpperRat (S : StepFn) (m N : Nat) : ℚ :=
  ∑ n ∈ Finset.Icc m N, S.upperRat n


-- @@ L44-46 verbatim
/-- Semantic finite step sum. -/
noncomputable def stepSum (S : StepFn) (m N : Nat) : ℝ :=
  ∑ n ∈ Finset.Icc m N, S.value n


-- @@ L48-53 verbatim
/-- A finite step sum is bounded below by the sum of the lower envelopes. -/
theorem stepLowerRat_le_stepSum (S : StepFn) (m N : Nat) :
    (stepLowerRat S m N : ℝ) ≤ stepSum S m N := by
  unfold stepLowerRat stepSum
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => S.lower_correct n


-- @@ L55-60 verbatim
/-- A finite step sum is bounded above by the sum of the upper envelopes. -/
theorem stepSum_le_stepUpperRat (S : StepFn) (m N : Nat) :
    stepSum S m N ≤ (stepUpperRat S m N : ℝ) := by
  unfold stepUpperRat stepSum
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun n _ => S.upper_correct n


-- @@ L62-64 verbatim
/-- Boolean interval checker for a finite step sum. -/
def checkStepSumInterval (S : StepFn) (m N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (stepLowerRat S m N) (stepUpperRat S m N) lo hi


-- @@ L66-68 verbatim
/-- Boolean lower-bound checker for a finite step sum. -/
def checkStepSumLower (S : StepFn) (m N : Nat) (lo : ℚ) : Bool :=
  LeanCert.Cert.checkRatLower (stepLowerRat S m N) lo


-- @@ L70-72 verbatim
/-- Boolean upper-bound checker for a finite step sum. -/
def checkStepSumUpper (S : StepFn) (m N : Nat) (hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatUpper (stepUpperRat S m N) hi


-- @@ L74-79 verbatim
/-- Golden theorem for finite step-sum interval certificates. -/
theorem verify_stepSum_interval (S : StepFn) (m N : Nat) (lo hi : ℚ)
    (hcheck : checkStepSumInterval S m N lo hi = true) :
    (lo : ℝ) ≤ stepSum S m N ∧ stepSum S m N ≤ (hi : ℝ) := by
  exact LeanCert.Cert.verify_rat_interval (stepLowerRat_le_stepSum S m N)
    (stepSum_le_stepUpperRat S m N) hcheck


-- @@ L81-85 verbatim
/-- Golden theorem for finite step-sum lower certificates. -/
theorem verify_stepSum_lower (S : StepFn) (m N : Nat) (lo : ℚ)
    (hcheck : checkStepSumLower S m N lo = true) :
    (lo : ℝ) ≤ stepSum S m N := by
  exact LeanCert.Cert.verify_rat_lower (stepLowerRat_le_stepSum S m N) hcheck


-- @@ L87-91 verbatim
/-- Golden theorem for finite step-sum upper certificates. -/
theorem verify_stepSum_upper (S : StepFn) (m N : Nat) (hi : ℚ)
    (hcheck : checkStepSumUpper S m N hi = true) :
    stepSum S m N ≤ (hi : ℝ) := by
  exact LeanCert.Cert.verify_rat_upper (stepSum_le_stepUpperRat S m N) hcheck


-- @@ L93-93 verbatim
end LeanCert.ANT
