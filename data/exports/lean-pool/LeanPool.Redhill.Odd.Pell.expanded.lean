/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.RingTheory.Radical.NatInt


-- @@ L13-15 verbatim
/-!
# Pell equation for the odd case
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace OddCase


-- @@ L22-28 verbatim
/-- An infinite sequence of pairs of natural numbers `(s, t)` satisfying
`y * s ^ 2 + 1 = (y + 1) * t ^ 2`. This will be applied with `y = Y n F ^ 2`. -/
def pell (y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
    let (s, t) := pell y k
    ((2 * y + 1) * s + (2 * y + 2) * t, 2 * y * s + (2 * y + 1) * t)


-- @@ L30-30 verbatim
variable {y k : ℕ}


-- @@ L32-33 verbatim
lemma pell_spec : y * (pell y k).1 ^ 2 + 1 = (y + 1) * (pell y k).2 ^ 2 := by
  induction k <;> grind [pell]


-- @@ L35-35 verbatim
lemma pell_snd_pos : 0 < (pell y k).2 := by induction k <;> grind [pell]


-- @@ L37-37 verbatim
lemma pell_snd_le_pell_fst : (pell y k).2 ≤ (pell y k).1 := by induction k <;> grind [pell]


-- @@ L39-39 verbatim
lemma pell_fst_pos : 0 < (pell y k).1 := pell_snd_pos.trans_le pell_snd_le_pell_fst


-- @@ L41-43 verbatim
lemma strictMono_pell_fst : StrictMono fun k ↦ (pell y k).1 := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  induction n <;> grind [pell]


-- @@ L45-50 verbatim
open UniqueFactorizationMonoid in
lemma radical_mul_pell_sq_add_one_dvd :
    radical (((pell (y ^ 2) k).1 * y) ^ 2 + 1) ∣ (y ^ 2 + 1) * (pell (y ^ 2) k).2 := by
  rw [mul_comm, mul_pow, pell_spec]
  exact radical_mul_dvd.trans
    (mul_dvd_mul radical_dvd_self (radical_pow_dvd.trans radical_dvd_self))


-- @@ L52-52 verbatim
end OddCase
