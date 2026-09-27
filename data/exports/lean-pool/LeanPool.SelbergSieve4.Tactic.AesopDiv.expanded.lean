/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.Divisors
import LeanPool.SelbergSieve4.Tactic.AesopInit
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt


-- @@ L13-15 verbatim
/-!
# LeanPool.SelbergSieve4.Tactic.AesopDiv
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Sieve

-- @@ L20-20 verbatim
open Finset


-- @@ L22-23 verbatim
/-- Wrapper predicate for divisibility used by the `Divisibility` Aesop rule set. -/
protected def MyDvd (a b : ℕ) : Prop := a ∣ b

-- @@ L24-24 verbatim
open Sieve (MyDvd)


-- @@ L26-28 verbatim
@[simp]
theorem myDvd_iff (a b : ℕ) : MyDvd a b ↔ a ∣ b := by
  exact Iff.rfl


-- @@ L30-35 verbatim
/-- Run `aesop` using the local divisibility rule set with simplification disabled. -/
macro (name := aesopDiv) "aesopDiv" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Divisibility):ident]))


-- @@ L37-42 verbatim
/-- Run `aesop?` using the local divisibility rule set with simplification disabled. -/
macro (name := aesopDiv?) "aesopDiv?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Divisibility):ident]))



-- @@ L45-46 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_of_myDvd (a b : ℕ) : MyDvd a b → a ∣ b := (myDvd_iff a b).mp


-- @@ L48-49 verbatim
@[aesop destruct safe (rule_sets := [Divisibility])]
theorem myDvd_of_dvd (a b : ℕ) : a ∣ b → MyDvd a b := (myDvd_iff a b).mpr


-- @@ L51-54 verbatim
@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_trans {a b c : ℕ} : MyDvd a b → MyDvd b c → MyDvd a c := by
  intro hab hbc
  exact (myDvd_iff a c).mpr (Nat.dvd_trans ((myDvd_iff a b).mp hab) ((myDvd_iff b c).mp hbc))


-- @@ L56-58 verbatim
@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_of_mem_divisors {a b : ℕ} : a ∈ b.divisors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_divisors


-- @@ L60-62 verbatim
@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_of_mem_primeFactors {a b : ℕ} : a ∈ b.primeFactors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_primeFactors


-- @@ L64-64 verbatim
attribute [aesop safe forward (rule_sets := [Divisibility])] not_squarefree_zero


-- @@ L66-68 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem eq_zero_of_zero_myDvd (a : ℕ) : MyDvd 0 a → a = 0 := by
  simp_all


-- @@ L70-70 verbatim
attribute [aesop safe (rule_sets := [Divisibility])] Nat.pos_of_ne_zero


-- @@ L72-73 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : False := by simp at h


-- @@ L75-76 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem mem_zero_divisors (a : ℕ) (h : a ∈ Nat.divisors 0) : False := by simp at h


-- @@ L78-79 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem zero_lt_zero (h : 0 < 0) : False := by linarith


-- @@ L81-82 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem test {n m : ℕ} : n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr


-- @@ L84-86 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c a :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b)


-- @@ L88-90 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c b :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b)


-- @@ L92-94 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : MyDvd a c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b) h


-- @@ L96-98 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : MyDvd b c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b) h


-- @@ L100-102 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_myDvd_left (a b : ℕ) : MyDvd (a.gcd b) a :=
  myDvd_of_dvd _ _ (gcd_dvd_left a b)


-- @@ L104-106 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_myDvd_right (a b : ℕ) : MyDvd (a.gcd b) b :=
  myDvd_of_dvd _ _ (gcd_dvd_right a b)


-- @@ L108-110 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem gcd_eq_zero_left (a b : ℕ) (h : a.gcd b = 0) : a = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.1

-- @@ L111-113 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem gcd_eq_zero_right (a b : ℕ) (h : a.gcd b = 0) : b = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.2


-- @@ L115-117 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd a c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b) h


-- @@ L119-121 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd b c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b) h


-- @@ L123-125 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : MyDvd c a) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b)


-- @@ L127-129 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : MyDvd c b) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b)


-- @@ L131-133 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem myDvd_lcm_left (a b : ℕ) : MyDvd a (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_left a b)


-- @@ L135-137 verbatim
@[aesop safe (rule_sets := [Divisibility])]
theorem myDvd_lcm_right (a b : ℕ) : MyDvd b (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_right a b)


-- @@ L139-141 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem lcm_eq_zero_left (a b : ℕ) (h : a.lcm b = 0) : a = 0 ∨ b = 0 := by
  rw [←lcm_eq_nat_lcm, _root_.lcm_eq_zero_iff] at h; exact h


-- @@ L143-143 verbatim
attribute [aesop forward safe (rule_sets := [Divisibility])] Squarefree.squarefree_of_dvd


-- @@ L145-149 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem squarefree_of_myDvd (a b : ℕ) (hb : Squarefree b) (h : MyDvd a b) :
    Squarefree a := by
  rw[myDvd_iff] at h
  exact Squarefree.squarefree_of_dvd h hb

-- @@ L150-150 verbatim
end Sieve
