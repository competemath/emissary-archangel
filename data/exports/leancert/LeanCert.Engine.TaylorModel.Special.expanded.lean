/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Core


-- @@ L8-20 verbatim
/-!
# Taylor Models - Special Functions

This file contains Taylor polynomial definitions and remainder bounds for
special functions (erf, and future sqrt), along with function-level Taylor
models.

## Main definitions

* `erfTaylorPoly` - Taylor polynomial for erf
* `erfRemainderBound` - Remainder bound for erf
* `tmErf` - Function-level Taylor model for erf
-/


-- @@ L22-22 verbatim
namespace LeanCert.Engine


-- @@ L24-24 verbatim
open LeanCert.Core

-- @@ L25-25 verbatim
open Polynomial


-- @@ L27-27 verbatim
namespace TaylorModel


-- @@ L29-36 verbatim
/-! ### erf Taylor polynomial

erf(x) = (2/√π) ∫₀ˣ e^{-t²} dt
       = (2/√π) Σ_{n=0}^∞ (-1)^n x^{2n+1} / (n! (2n+1))
       = (2/√π) (x - x³/3 + x⁵/10 - x⁷/42 + ...)

We use rational approximations for 2/√π ≈ 1.128379...
-/


-- @@ L38-39 verbatim
/-- Rational approximation of 2/√π (lower bound) -/
def erfCoeff_lo : ℚ := 1128 / 1000  -- ~1.128


-- @@ L41-42 verbatim
/-- Rational approximation of 2/√π (upper bound) -/
def erfCoeff_hi : ℚ := 1129 / 1000  -- ~1.129


-- @@ L44-53 verbatim
/-- Taylor polynomial coefficients for erf at center 0 (using middle approximation):
    erf(x) ≈ (2/√π) Σ (-1)^k x^{2k+1} / (k! (2k+1)) -/
noncomputable def erfTaylorCoeffs (n : ℕ) : ℕ → ℚ := fun i =>
  if i ≤ n then
    if i % 2 = 1 then  -- odd terms only
      let k := (i - 1) / 2
      let coeff := (erfCoeff_lo + erfCoeff_hi) / 2  -- middle approximation
      coeff * ((-1 : ℚ) ^ k) / ((Nat.factorial k : ℚ) * (2 * k + 1))
    else 0
  else 0


-- @@ L55-57 verbatim
/-- Taylor polynomial for erf of degree n -/
noncomputable def erfTaylorPoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.C (erfTaylorCoeffs n i) * Polynomial.X ^ i


-- @@ L59-67 verbatim
/-- Remainder bound for erf: |erf(x)| ≤ 1 for all x, so we use Taylor remainder
    plus coefficient approximation error. -/
noncomputable def erfRemainderBound (domain : IntervalRat) (n : ℕ) : ℚ :=
  let r := max (|domain.lo|) (|domain.hi|)
  -- Taylor remainder plus approximation error for 2/√π
  let taylor_rem := r ^ (n + 1) / (Nat.factorial (n + 1) : ℚ)
  -- Coefficient error: |true - approx| ≤ (erfCoeff_hi - erfCoeff_lo)/2 * sum of poly terms
  let coeff_err := (erfCoeff_hi - erfCoeff_lo) / 2 * r  -- simplified upper bound
  taylor_rem + coeff_err


-- @@ L69-81 verbatim
/-- Remainder bound for erf is nonnegative -/
theorem erfRemainderBound_nonneg (domain : IntervalRat) (n : ℕ) :
    0 ≤ erfRemainderBound domain n := by
  unfold erfRemainderBound
  simp only [erfCoeff_hi, erfCoeff_lo]
  apply add_nonneg
  · apply div_nonneg
    · apply pow_nonneg
      exact le_max_of_le_left (abs_nonneg _)
    · exact Nat.cast_nonneg _
  · apply mul_nonneg
    · norm_num
    · exact le_max_of_le_left (abs_nonneg _)


-- @@ L83-90 verbatim
/-- Taylor model for erf z on domain J, centered at 0, degree n.
    erf(z) = (2/√π) ∫₀ᶻ e^{-t²} dt. -/
noncomputable def tmErf (J : IntervalRat) (n : ℕ) : TaylorModel :=
  { poly := erfTaylorPoly n
    remainder := ⟨-erfRemainderBound J n, erfRemainderBound J n,
      by linarith [erfRemainderBound_nonneg J n]⟩
    center := 0
    domain := J }


-- @@ L92-98 verbatim
/-! ### Future: sqrt Taylor model

sqrt(x) requires special treatment since it's not analytic at 0.
It needs to be expanded around a positive center c > 0.

For now, we leave a placeholder comment.
-/


-- @@ L100-100 verbatim
end TaylorModel


-- @@ L102-102 verbatim
end LeanCert.Engine
