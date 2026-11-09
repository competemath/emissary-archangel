/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.HMinus.LValueReduction.GaussPairing


-- @@ L10-16 verbatim
/-!
# The raw odd Gauss-product formula

This file merges the two `mod 4` branches of the inversion-pair argument into
the final raw Gauss-product identity and packages it as the cyclotomic
`hgauss` hypothesis used downstream.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open NumberField

-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
namespace BernoulliRegular


-- @@ L27-27 verbatim
section GaussProduct


-- @@ L29-30 verbatim
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]


-- @@ L32-67 verbatim
theorem rawGaussProduct_rhs_of_mod_four_eq_one
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 1) :
    (-(p : ℂ)) ^ ((p - 1) / 4) =
      (Complex.I ^ ((p - 1) / 2)) *
        (((Real.sqrt ((p : ℝ) ^ ((p - 1) / 2)) : ℝ) : ℂ)) := by
  let m : ℕ := (p - 1) / 4
  let n : ℕ := (p - 1) / 2
  have hnm : n = 2 * m := by
    dsimp [m, n]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨k, hk⟩
    rw [hk]
    omega
  have hI :
      Complex.I ^ n = (-1 : ℂ) ^ m := by
    calc
      Complex.I ^ n = Complex.I ^ (2 * m) := by rw [hnm]
      _ = (Complex.I ^ 2) ^ m := by rw [pow_mul]
      _ = (-1 : ℂ) ^ m := by rw [Complex.I_sq]
  have hsqrt :
      (((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ)) = (p : ℂ) ^ m := by
    have hsqrt_real : Real.sqrt ((p : ℝ) ^ n) = (p : ℝ) ^ m := by
      calc
        Real.sqrt ((p : ℝ) ^ n) = Real.sqrt ((p : ℝ) ^ (2 * m)) := by rw [hnm]
        _ = Real.sqrt ((p : ℝ) ^ (m * 2)) := by
              congr 1
              ring
        _ = Real.sqrt (((p : ℝ) ^ m) ^ 2) := by rw [pow_mul]
        _ = (p : ℝ) ^ m := by
              rw [Real.sqrt_sq_eq_abs]
              simp
    simpa [Complex.ofReal_pow] using congrArg (fun x : ℝ ↦ (x : ℂ)) hsqrt_real
  calc
    (-(p : ℂ)) ^ m = ((-1 : ℂ) ^ m) * (p : ℂ) ^ m := by
      rw [show (-(p : ℂ)) = (-1 : ℂ) * (p : ℂ) by ring, mul_pow]
    _ = (Complex.I ^ n) * (((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ)) := by
          rw [hI, hsqrt]


-- @@ L69-120 verbatim
theorem rawGaussProduct_rhs_of_mod_four_eq_three
    (hp_odd' : p ≠ 2) (hp₄ : p % 4 = 3) :
    (Complex.I * (Real.sqrt p : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) =
      (Complex.I ^ ((p - 1) / 2)) *
        (((Real.sqrt ((p : ℝ) ^ ((p - 1) / 2)) : ℝ) : ℂ)) := by
  let m : ℕ := (p - 3) / 4
  let n : ℕ := (p - 1) / 2
  have hnm : n = 2 * m + 1 := by
    dsimp [m, n]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨k, hk⟩
    rw [hk]
    omega
  have hI :
      Complex.I ^ n = ((-1 : ℂ) ^ m) * Complex.I := by
    calc
      Complex.I ^ n = Complex.I ^ (1 + 2 * m) := by
        rw [hnm]
        congr 1
        ring
      _ = Complex.I ^ 1 * Complex.I ^ (2 * m) := by rw [pow_add]
      _ = Complex.I * ((Complex.I ^ 2) ^ m) := by simp [pow_mul]
      _ = ((-1 : ℂ) ^ m) * Complex.I := by rw [Complex.I_sq]; ring
  have hsqrt :
      (((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ)) =
        (Real.sqrt p : ℂ) * (p : ℂ) ^ m := by
    have hsqrt_real :
        Real.sqrt ((p : ℝ) ^ n) = Real.sqrt p * (p : ℝ) ^ m := by
      calc
        Real.sqrt ((p : ℝ) ^ n) = Real.sqrt ((p : ℝ) ^ (1 + 2 * m)) := by
              rw [hnm]
              congr 1
              ring
        _ = Real.sqrt (p * (p : ℝ) ^ (2 * m)) := by rw [pow_add, pow_one]
        _ = Real.sqrt ((p : ℝ) ^ (2 * m) * p) := by rw [mul_comm]
        _ = Real.sqrt ((p : ℝ) ^ (2 * m)) * Real.sqrt p := by
              rw [Real.sqrt_mul (by positivity)]
        _ = Real.sqrt ((p : ℝ) ^ (m * 2)) * Real.sqrt p := by
              congr 1
              congr 1
              ring
        _ = Real.sqrt (((p : ℝ) ^ m) ^ 2) * Real.sqrt p := by rw [pow_mul]
        _ = (p : ℝ) ^ m * Real.sqrt p := by rw [Real.sqrt_sq_eq_abs]; simp
        _ = Real.sqrt p * (p : ℝ) ^ m := by ring
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hsqrt_real
  calc
    (Complex.I * (Real.sqrt p : ℂ)) * (-(p : ℂ)) ^ m =
        (Complex.I * (Real.sqrt p : ℂ)) * (((-1 : ℂ) ^ m) * (p : ℂ) ^ m) := by
          rw [show (-(p : ℂ)) = (-1 : ℂ) * (p : ℂ) by ring, mul_pow]
    _ = (((-1 : ℂ) ^ m) * Complex.I) * ((Real.sqrt p : ℂ) * (p : ℂ) ^ m) := by ring
    _ = (Complex.I ^ n) * (((Real.sqrt ((p : ℝ) ^ n) : ℝ) : ℂ)) := by
          rw [hI, hsqrt]


-- @@ L122-140 verbatim
/-- **T023d6**: Merge the two `mod 4` branches into the clean raw odd
Gauss-product formula used downstream. -/
theorem rawGaussProduct
    (hp_odd' : p ≠ 2) :
    Finset.prod (oddCharacters (p := p))
        (fun χ ↦ gaussSum χ (ZMod.stdAddChar (N := p))) =
      (Complex.I ^ ((p - 1) / 2)) *
        (((Real.sqrt ((p : ℝ) ^ ((p - 1) / 2)) : ℝ) : ℂ)) := by
  by_cases hp₄ : p % 4 = 1
  · rw [rawGaussProduct_of_mod_four_eq_one (p := p) hp_odd' hp₄]
    exact rawGaussProduct_rhs_of_mod_four_eq_one (p := p) hp_odd' hp₄
  · have hpodd : p % 2 = 1 := by
      rcases hp.out.odd_of_ne_two hp_odd' with ⟨k, hk⟩
      rw [hk]
      omega
    have hp₄' : p % 4 = 3 := by
      omega
    rw [rawGaussProduct_of_mod_four_eq_three (p := p) hp_odd' hp₄']
    exact rawGaussProduct_rhs_of_mod_four_eq_three (p := p) hp_odd' hp₄'


-- @@ L142-149 verbatim
/-- **T023d7**: Package the raw odd Gauss-product formula as the exact
cyclotomic `hgauss` hypothesis consumed by the final `hMinus` assembly
theorem. -/
theorem cyclotomicHGaussGoal_holds
    (hp_odd' : p ≠ 2) :
    cyclotomicHGaussGoal (p := p) K :=
  (cyclotomicHGaussGoal_iff_rawGaussProduct (p := p) (K := K) hp_odd').2
    (rawGaussProduct (p := p) hp_odd')


-- @@ L151-151 verbatim
end GaussProduct


-- @@ L153-153 verbatim
end BernoulliRegular
