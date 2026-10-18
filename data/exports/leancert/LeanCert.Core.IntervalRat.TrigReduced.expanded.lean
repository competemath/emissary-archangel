/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.TrigReduction


-- @@ L9-35 verbatim
/-!
# Computable Range Reduction for Trigonometric Functions

This file implements range reduction for sin and cos to improve Taylor series
convergence for intervals far from 0.

## Problem

Standard Taylor series for sin/cos centered at 0 have remainder bounds of
`|x|^{n+1} / (n+1)!`. For intervals far from 0 (e.g., [10, 11]), this remainder
is huge even for moderate n.

## Solution: Range Reduction

Use the periodicity of sin/cos:
- `sin(x) = sin(x - 2πk)` for any integer k
- `cos(x) = cos(x - 2πk)` for any integer k

By choosing k to bring x - 2πk into [-π, π], the Taylor series converges much
faster since |x - 2πk| ≤ π ≈ 3.14.

## Main definitions

* `twoPiRatLo`, `twoPiRatHi` - Rational bounds for 2π
* `reduceToMainPeriod` - Shift interval to be near 0
* `sinComputableReduced`, `cosComputableReduced` - Computable evaluation with range reduction
-/


-- @@ L37-37 verbatim
namespace LeanCert.Core.IntervalRat


-- @@ L39-39 verbatim
/-! ### Shared range-reduction API -/


-- @@ L41-41 verbatim
def piRatLo : ℚ := LeanCert.Core.TrigReduction.piRatLo

-- @@ L42-42 verbatim
def piRatHi : ℚ := LeanCert.Core.TrigReduction.piRatHi

-- @@ L43-43 verbatim
def twoPiRatLo : ℚ := LeanCert.Core.TrigReduction.twoPiRatLo

-- @@ L44-44 verbatim
def twoPiRatHi : ℚ := LeanCert.Core.TrigReduction.twoPiRatHi

-- @@ L45-45 verbatim
def computeShiftK : IntervalRat → ℤ := LeanCert.Core.TrigReduction.computeShiftK

-- @@ L46-46 verbatim
def shiftInterval : IntervalRat → ℤ → IntervalRat := LeanCert.Core.TrigReduction.shiftInterval

-- @@ L47-48 verbatim
def reduceToMainPeriod : IntervalRat → IntervalRat × ℤ :=
  LeanCert.Core.TrigReduction.reduceToMainPeriod


-- @@ L50-51 verbatim
theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi :=
  LeanCert.Core.TrigReduction.piRatLo_lt_pi


-- @@ L53-54 verbatim
theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.pi_lt_piRatHi


-- @@ L56-57 verbatim
theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_lt_two_pi


-- @@ L59-60 verbatim
theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) :=
  LeanCert.Core.TrigReduction.two_pi_lt_twoPiRatHi


-- @@ L62-63 verbatim
theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi :=
  LeanCert.Core.TrigReduction.twoPiRatLo_le_twoPiRatHi


-- @@ L65-68 verbatim
theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  change x - 2 * Real.pi * k ∈ LeanCert.Core.TrigReduction.shiftInterval I k
  exact LeanCert.Core.TrigReduction.mem_shiftInterval_of_mem hx


-- @@ L70-70 verbatim
/-! ### Computable reduced evaluation -/


-- @@ L72-78 verbatim
/-- Computable sin evaluation with range reduction. -/
def sinComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    sinComputable Ired n


-- @@ L80-86 verbatim
/-- Computable cos evaluation with range reduction. -/
def cosComputableReduced (I : IntervalRat) (n : ℕ := 10) : IntervalRat :=
  let (Ired, _k) := reduceToMainPeriod I
  if Ired.lo < -4 ∨ Ired.hi > 4 then
    ⟨-1, 1, by norm_num⟩
  else
    cosComputable Ired n


-- @@ L88-108 verbatim
/-- sin x ∈ sinComputableReduced I for all x ∈ I -/
theorem mem_sinComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.sin x ∈ sinComputableReduced I n := by
  unfold sinComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hsin_eq : Real.sin x = Real.sin (x - 2 * Real.pi * k) := by
    have h := Real.sin_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · push Not at hwide
    rw [hsin_eq]
    exact mem_sinComputable hxred n


-- @@ L110-129 verbatim
/-- cos x ∈ cosComputableReduced I for all x ∈ I -/
theorem mem_cosComputableReduced {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (n : ℕ := 10) :
    Real.cos x ∈ cosComputableReduced I n := by
  unfold cosComputableReduced reduceToMainPeriod
  simp only []
  set Ired := shiftInterval I (computeShiftK I) with hIred
  set k := computeShiftK I with hk
  have hxred : x - 2 * Real.pi * k ∈ Ired := by
    rw [hIred, hk]
    exact mem_shiftInterval_of_mem hx
  have hcos_eq : Real.cos x = Real.cos (x - 2 * Real.pi * k) := by
    have h := Real.cos_add_int_mul_two_pi x (-k)
    simp only [Int.cast_neg, neg_mul] at h
    rw [← h]
    ring_nf
  split_ifs with hwide
  · simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · rw [hcos_eq]
    exact mem_cosComputable hxred n


-- @@ L131-131 verbatim
end LeanCert.Core.IntervalRat
