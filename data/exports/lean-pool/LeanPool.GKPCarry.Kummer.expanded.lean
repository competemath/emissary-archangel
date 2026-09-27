/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic


-- @@ L15-20 verbatim
/-!
# Kummer formulas for central binomial coefficients

Kummer's digit-sum formula is specialized to `Nat.centralBinom`.  The resulting
bridge turns digit and carry estimates into divisibility statements.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace GKPCarry


-- @@ L26-26 verbatim
open Nat


-- @@ L28-41 verbatim
/-- Kummer's digit-sum formula specialized to central binomial coefficients. -/
theorem sub_one_mul_padicValNat_centralBinom
    (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) =
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hn : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  have hkummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits
      (p := p) (k := n) (n := 2 * n) hn
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hkummer
  rw [hkummer]
  ring_nf


-- @@ L43-56 verbatim
/-- A lower bound on Kummer's digit excess gives divisibility by a prime
power. -/
theorem pow_dvd_centralBinom_of_digit_excess
    {p n e : ℕ} [hp : Fact p.Prime]
    (h : (p - 1) * e ≤
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum) :
    p ^ e ∣ Nat.centralBinom n := by
  rw [← sub_one_mul_padicValNat_centralBinom p n] at h
  have hp1 : 0 < p - 1 := by
    have := hp.out.one_lt
    omega
  have hval : e ≤ padicValNat p (Nat.centralBinom n) :=
    Nat.le_of_mul_le_mul_left h hp1
  exact dvd_trans (pow_dvd_pow p hval) pow_padicValNat_dvd


-- @@ L58-63 verbatim
/-- The ternary specialization of the central-binomial digit formula. -/
theorem two_mul_padicValNat_three_centralBinom (n : ℕ) :
    2 * padicValNat 3 (Nat.centralBinom n) =
      2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  simpa using sub_one_mul_padicValNat_centralBinom 3 n


-- @@ L65-65 verbatim
end GKPCarry
