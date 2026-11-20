/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib
public import KostkaNumbers.Dominate


-- @@ L11-13 verbatim
/-!
Prove some results about when small lists dominate one another.  Used for some of the computations.
-/


-- @@ L15-15 verbatim
public section


-- @@ L17-24 expanded
lemma singleton_dominates_singleton {a b : ℕ} : (Dominates [b] [a]) ↔ a ≤ b :=
  by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp [h]


-- @@ L26-36 expanded
lemma singleton_dominates_pair {a b c : ℕ} : (Dominates [c] [a, b]) ↔ a + b ≤ c :=
  by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h] <;> lia


-- @@ L38-48 expanded
lemma singleton_dominates_triple {a b c d : ℕ} : (Dominates [d] [a, b, c]) ↔ a + b + c ≤ d :=
  by
  constructor
  · intro h
    apply sum_le_sum_of_dominates at h
    simpa [← add_assoc] using h
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h] <;> lia


-- @@ L52-62 expanded
lemma pair_dominates_singleton {a b c : ℕ} : (Dominates [b, c] [a]) ↔ a ≤ b :=
  by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]


-- @@ L64-77 expanded
lemma pair_dominates_pair {a b c d : ℕ} : (Dominates [c, d] [a, b]) ↔ a ≤ c ∧ a + b ≤ c + d :=
  by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h₁, h₂]


-- @@ L79-93 expanded
lemma pair_dominates_triple {a b c d e : ℕ} :
    (Dominates [d, e] [a, b, c]) ↔ a ≤ d ∧ a + b + c ≤ d + e :=
  by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [add_assoc] using h
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂] <;> lia


-- @@ L97-107 expanded
lemma triple_dominates_singleton {a b c d : ℕ} : (Dominates [b, c, d] [a]) ↔ a ≤ b :=
  by
  constructor
  · intro h
    refine get_zero_ge_of_dominates h ?_ ?_
    all_goals simp
  · intro h
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, h]


-- @@ L109-123 expanded
lemma triple_dominates_pair {a b c d e : ℕ} :
    (Dominates [c, d, e] [a, b]) ↔ a ≤ c ∧ a + b ≤ c + d :=
  by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂]


-- @@ L125-141 expanded
lemma triple_dominates_triple {a b c d e f : ℕ} :
    (Dominates [d, e, f] [a, b, c]) ↔ a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f :=
  by
  constructor
  · intro h
    constructor; swap; constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · apply sum_le_sum_of_dominates at h
      simpa [← add_assoc] using h
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, h₁, h₂, h₃]


-- @@ L144-161 expanded
lemma quad_dominates_triple {a b c d e f g : ℕ} :
    (Dominates [d, e, f, g] [a, b, c]) ↔ a ≤ d ∧ a + b ≤ d + e ∧ a + b + c ≤ d + e + f :=
  by
  constructor
  · intro h
    constructor
    · refine get_zero_ge_of_dominates h ?_ ?_
      all_goals simp
    constructor
    · refine sum_two_le_of_dominates h ?_ ?_
      all_goals simp
    · refine sum_three_le_of_dominates h ?_ ?_
      all_goals simp
  · intro ⟨h₁, h₂, h₃⟩
    refine dominates_of_forall_lt_length ?_
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    intro r hr
    interval_cases r
    all_goals simp [Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_four, h₁, h₂, h₃]

