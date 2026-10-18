/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.EulerProduct


-- @@ L8-13 verbatim
/-!
# Prime Euler-product presets

This file keeps arithmetic presets separate from the generic finite
Euler-product certificate machinery.
-/


-- @@ L15-15 verbatim
namespace LeanCert.ANT


-- @@ L17-17 verbatim
open scoped BigOperators


-- @@ L19-21 verbatim
/-- Rational factor `1 - 1/n`. -/
def oneMinusInvRat (n : Nat) : ℚ :=
  1 - 1 / (n : ℚ)


-- @@ L23-25 verbatim
/-- Rational factor `1 + 1/n`. -/
def onePlusInvRat (n : Nat) : ℚ :=
  1 + 1 / (n : ℚ)


-- @@ L27-29 verbatim
/-- Finite prime product `∏_{p ≤ N} (1 - 1/p)`. -/
noncomputable def primeEulerOneMinusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) - 1 / (p : ℝ)


-- @@ L31-33 verbatim
/-- Exact rational value of `∏_{p ≤ N} (1 - 1/p)`. -/
def primeEulerOneMinusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) oneMinusInvRat


-- @@ L35-37 verbatim
/-- Finite prime product `∏_{p ≤ N} (1 + 1/p)`. -/
noncomputable def primeEulerOnePlusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) + 1 / (p : ℝ)


-- @@ L39-41 verbatim
/-- Exact rational value of `∏_{p ≤ N} (1 + 1/p)`. -/
def primeEulerOnePlusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) onePlusInvRat


-- @@ L43-47 verbatim
private theorem prime_of_mem_primesLE {N p : Nat} (hp : p ∈ primesLE N) :
    Nat.Prime p := by
  have hp' := hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
  exact hp'.2


-- @@ L49-58 verbatim
private theorem oneMinusInvRat_nonneg_of_prime {p : Nat} (hp : Nat.Prime p) :
    0 ≤ oneMinusInvRat p := by
  unfold oneMinusInvRat
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp_one : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  have hinv' : (1 : ℚ) / p ≤ (p : ℚ) / p :=
    div_le_div_of_nonneg_right hp_one (le_of_lt hp_pos)
  have hinv : (1 / (p : ℚ)) ≤ 1 := by
    simpa [div_self (ne_of_gt hp_pos)] using hinv'
  linarith


-- @@ L60-64 verbatim
private theorem oneMinusInvRat_cast_eq {p : Nat} (hp : Nat.Prime p) :
    (oneMinusInvRat p : ℝ) = (1 : ℝ) - 1 / (p : ℝ) := by
  unfold oneMinusInvRat
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  norm_num [Rat.cast_div, hp_ne]


-- @@ L66-70 verbatim
private theorem onePlusInvRat_cast_eq {p : Nat} (hp : Nat.Prime p) :
    (onePlusInvRat p : ℝ) = (1 : ℝ) + 1 / (p : ℝ) := by
  unfold onePlusInvRat
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  norm_num [Rat.cast_div, hp_ne]


-- @@ L72-75 verbatim
/-- Boolean interval checker for `∏_{p ≤ N} (1 - 1/p)`. -/
def checkPrimeEulerOneMinusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (primeEulerOneMinusInvRat N)
    (primeEulerOneMinusInvRat N) lo hi


-- @@ L77-80 verbatim
/-- Boolean interval checker for `∏_{p ≤ N} (1 + 1/p)`. -/
def checkPrimeEulerOnePlusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (primeEulerOnePlusInvRat N)
    (primeEulerOnePlusInvRat N) lo hi


-- @@ L82-97 verbatim
/-- Golden theorem for finite prime products `∏_{p ≤ N} (1 - 1/p)`. -/
theorem verify_primeEulerOneMinusInv_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkPrimeEulerOneMinusInvInterval N lo hi = true) :
    (lo : ℝ) ≤ primeEulerOneMinusInv N ∧
      primeEulerOneMinusInv N ≤ (hi : ℝ) := by
  unfold checkPrimeEulerOneMinusInvInterval primeEulerOneMinusInvRat at hcheck
  have hprod := verify_eulerProduct_interval (primesLE N)
    (fun p => (1 : ℝ) - 1 / (p : ℝ)) oneMinusInvRat oneMinusInvRat
    (fun p hp => oneMinusInvRat_nonneg_of_prime (prime_of_mem_primesLE hp))
    (fun p hp => by rw [oneMinusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    (fun p hp => by rw [oneMinusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    lo hi
  have hgeneric :
      checkEulerProductInterval (primesLE N) oneMinusInvRat oneMinusInvRat lo hi = true := by
    simpa [checkEulerProductInterval, productUpperRat, productLowerRat] using hcheck
  simpa [primeEulerOneMinusInv] using hprod hgeneric


-- @@ L99-114 verbatim
/-- Golden theorem for finite prime products `∏_{p ≤ N} (1 + 1/p)`. -/
theorem verify_primeEulerOnePlusInv_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkPrimeEulerOnePlusInvInterval N lo hi = true) :
    (lo : ℝ) ≤ primeEulerOnePlusInv N ∧
      primeEulerOnePlusInv N ≤ (hi : ℝ) := by
  unfold checkPrimeEulerOnePlusInvInterval primeEulerOnePlusInvRat at hcheck
  have hprod := verify_eulerProduct_interval (primesLE N)
    (fun p => (1 : ℝ) + 1 / (p : ℝ)) onePlusInvRat onePlusInvRat
    (fun p hp => by unfold onePlusInvRat; positivity)
    (fun p hp => by rw [onePlusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    (fun p hp => by rw [onePlusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    lo hi
  have hgeneric :
      checkEulerProductInterval (primesLE N) onePlusInvRat onePlusInvRat lo hi = true := by
    simpa [checkEulerProductInterval, productUpperRat, productLowerRat] using hcheck
  simpa [primeEulerOnePlusInv] using hprod hgeneric


-- @@ L116-116 verbatim
end LeanCert.ANT
