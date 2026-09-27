/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Mathlib.Data.Nat.Choose.Central


-- @@ L10-15 verbatim
/-!
# The Graham--Knuth--Patashnik central-binomial conjecture

This file records the conjecture from Exercise 5.112 of *Concrete Mathematics*
and its restriction to powers of two.  The conjecture itself remains open.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace GKPCarry


-- @@ L21-25 verbatim
/-- The Graham--Knuth--Patashnik conjecture: if `n > 4` and
`n ∉ {64, 256}`, then `Nat.centralBinom n` is divisible by `4` or by `9`. -/
def gkpConjecture : Prop :=
  ∀ n : ℕ, 4 < n → n ≠ 64 → n ≠ 256 →
    (4 ∣ Nat.centralBinom n ∨ 9 ∣ Nat.centralBinom n)


-- @@ L27-30 verbatim
/-- The power-of-two restriction of the GKP conjecture. -/
def gkpPowerOfTwoConjecture : Prop :=
  ∀ k : ℕ, 2 < k → k ≠ 6 → k ≠ 8 →
    9 ∣ Nat.centralBinom (2 ^ k)


-- @@ L32-32 verbatim
end GKPCarry
