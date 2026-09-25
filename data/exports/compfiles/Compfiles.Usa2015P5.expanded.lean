/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Jujian Zhang
-/

module

public import Mathlib
public import Mathlib.Tactic

public import ProblemExtraction


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
problem_file { tags := [.NumberTheory] }


-- @@ L18-23 verbatim
/-!
# USA Mathematical Olympiad 2015, Problem 5

Let a, b, c, d, e be distinct positive integers such that a⁴+b⁴ = c⁴+d⁴ = e⁵.
Show that ac+bd is a composite number.
-/


-- @@ L25-25 verbatim
namespace Usa2015P5


-- @@ L27-34 verbatim
variable { a b c d e : ℕ }
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (habe : a ^ 4 + b ^ 4 = e ^ 5)
    (hcde : c ^ 4 + d ^ 4 = e ^ 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e)


-- @@ L36-38 verbatim
snip begin

-- Follows the solution at https://web.evanchen.cc/exams/USAMO-2015-notes.pdf


-- @@ L40-40 verbatim
set_option quotPrecheck false

-- @@ L41-41 verbatim
local notation3 "p" => a * c + b * d


-- @@ L43-49 verbatim
include habe hcde in
lemma p_divis : ((a - d) * (a + d) * (a ^ 2 + d ^ 2) * e ^ 5 : ZMod p) = 0 := by
  replace habe := congr(($habe : ZMod p))
  replace hcde := congr(($hcde : ZMod p))
  simp_all
  have : (a * c + b * d : ZMod p) = 0 := by simp [← Nat.cast_mul, ← Nat.cast_add]
  grind only


-- @@ L51-58 verbatim
include ha hb hc hd habe in
lemma e_lt_p : e < p := by
  have h : e ^ 5 < p ^ 5 := calc
    _ = a ^ 4 + b ^ 4 := habe.symm
    _ ≤ a ^ 5 + b ^ 5 := by gcongr 1 <;> exact Nat.pow_le_pow_right ‹_› (by norm_num)
    _ < (a + b) ^ 5 := by group; simp_all
    _ ≤ _ := by gcongr <;> nlinarith
  exact lt_of_pow_lt_pow_left' 5 h


-- @@ L60-62 verbatim
include ha hb hc hd he habe in
lemma not_p_dvd_e :  ¬ p ∣ e :=
  Nat.not_dvd_of_pos_of_lt he (e_lt_p ha hb hc hd habe)


-- @@ L64-68 verbatim
include ha hb hc hd he habe in
lemma not_p_dvd_e_pow_5 (hp: Nat.Prime p) : ¬ p ∣ e ^ 5 := by
  have h := not_p_dvd_e ha hb hc hd he habe
  contrapose! h
  exact Nat.Prime.dvd_of_dvd_pow hp h


-- @@ L70-91 verbatim
include ha hb hc hd he habe hcde had in
lemma p_le_aa_plus_dd (hp : Nat.Prime p) : p ≤ a ^ 2 + d ^ 2 := by
  wlog h_d_le_a : d ≤ a
  · grind only
  have h_d_lt_a : d < a := Nat.lt_of_le_of_ne h_d_le_a (id (Ne.symm had))
  have h := p_divis habe hcde
  simp only [← Nat.cast_sub h_d_le_a, ← Nat.cast_npow, ← Nat.cast_add, ← Nat.cast_mul] at h
  rw [ZMod.natCast_eq_zero_iff] at h
  rw [Nat.Prime.dvd_mul hp] at h
  -- At this point, p ∣ (a-d)(a+d)(a²+d²)e⁵
  -- Cut off the e at the far right
  replace h := h.resolve_right (by apply not_p_dvd_e_pow_5 <;> assumption)
  simp only [Nat.Prime.dvd_mul hp] at h
  clear hb hc he habe hcde h_d_le_a
  -- At this point, p ∣ (a-d)(a+d)(a²+d²)
  -- Break into a ton of cases based on which factor is divided; most are easy
  rcases h with ((h|h)|h) <;> apply Nat.le_of_dvd at h <;> try nlinarith
  · refine h.trans ?_
    calc
      _ ≤ a + d := by lia
      _ ≤ _ := by gcongr <;> apply Nat.le_pow <;> norm_num
  · simp_all

-- @@ L92-92 verbatim
snip end


-- @@ L94-110 verbatim
include ha hb hc hd he habe hcde had hbc hac in
problem usa2015_p5 : ¬ Nat.Prime (a * c + b * d) ∧ (1 < a * c + b * d) := by
  constructor
  · wlog h_a_le_c : a ≤ c
    · rw [show a * c + b * d = c * a + d * b by ring]
      apply this hc hd ha hb he <;> try {symm; assumption} <;> linarith
    have h_a_lt_c : a < c := Nat.lt_of_le_of_ne h_a_le_c hac
    clear h_a_le_c hac
    by_contra
    have : a * c + b * d ≤ a ^ 2 + d ^ 2 := by apply p_le_aa_plus_dd <;> assumption
    clear had hbc
    have h_d_lt_b : d < b := by
      rw [← hcde] at habe
      have : a ^ 4 < c ^ 4 := by gcongr
      exact lt_of_pow_lt_pow_left' 4 (by grind only)
    nlinarith
  · nlinarith


-- @@ L112-112 verbatim
end Usa2015P5
