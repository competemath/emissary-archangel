/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib
public import KostkaNumbers.Defs
public import KostkaNumbers.Dominate
import KostkaNumbers.Basic
import KostkaNumbers.Kostka.KostkaPos
import KostkaNumbers.Kostka.HorizontalAndHook
import KostkaNumbers.Util.Util
import KostkaNumbers.Util.Diagrams


-- @@ L17-19 verbatim
/-!
Prove some easy cases of the inequality.
-/


-- @@ L21-21 verbatim
public section


-- @@ L23-23 verbatim
open Kostka SemistandardYoungTableau YoungDiagram


-- @@ L25-25 verbatim
variable {γ : YoungDiagram} {μ : Multiset ℕ}


-- @@ L27-33 expanded
lemma kostka_ineq_not_dominate {n : ℕ} (hd : ¬Dominates γ.rowLens (μ.sort (· ≥ ·)))
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) :=
  by
  rw [← kostka_pos_iff_dominates h h0, Nat.pos_iff_ne_zero] at hd
  push Not at hd
  rw [hd, mul_zero]
  exact Nat.zero_le ((μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1))


-- @@ L35-42 verbatim
lemma kostka_ineq_hook {n : ℕ} (hn : n ≥ 2) (hγ : γ = hookDiagram n)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  have hnc : γ.card = n := by rw [hγ, hookDiagram_card]
  rw [hγ]
  nth_rw 2 [← hnc]
  rw [h, kostka_hook μ h0, mul_comm, kostka_hook_replicate n hn]
  rwa [← h, hnc]


-- @@ L44-58 expanded
lemma rowLens_dominates_card_iff {n : ℕ} (h : γ.card = n) :
    (Dominates γ.rowLens [n]) ↔ γ = horizontalDiagram n :=
  by
  by_cases hn : n = 0
  · simp [hn, h, eq_bot_iff_card_eq_zero]
  constructor
  · intro hd
    rw [eq_iff_rowLens_eq, horizontalDiagram_rowLens hn, ← dominates_singleton_iff ?_ hn]
    · exact hd
    · intro i
      refine γ.pos_of_mem_rowLens _ ?_
      exact List.getElem_mem (Fin.val_lt_of_le i (le_refl γ.rowLens.length))
    · rw [← h, card_eq_sum_rowLens]
  · intro hd
    rw [hd, horizontalDiagram_rowLens hn]
    exact dominates_self


-- @@ L60-73 expanded
lemma kostka_ineq_singleton {n : ℕ} (hγ : γ ≠ horizontalDiagram n) (hμ : μ = { n })
    (h : γ.card = μ.sum) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) :=
  by
  have h0 : n ≠ 0 := by
    contrapose! hγ
    rw [hγ, horizontalDiagram_zero, eq_bot_iff_card_eq_zero, h, hμ, hγ, Multiset.sum_singleton]
  by_cases hd : Dominates γ.rowLens (μ.sort (· ≥ ·))
  · suffices γ = horizontalDiagram n by contradiction
    simp only [ge_iff_le, hμ, Multiset.sort_singleton, Multiset.sum_singleton, h,
      rowLens_dominates_card_iff] at hd h
    exact hd
  · refine kostka_ineq_not_dominate hd h ?_
    rw [hμ, Multiset.mem_singleton]
    exact h0.symm


-- @@ L75-77 verbatim
lemma kostka_ineq_replicate {n : ℕ} (hμ : μ = Multiset.replicate n 1) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) := by
  rw [hμ, Multiset.card_replicate]


-- @@ L79-90 expanded
lemma kostka_ineq_vertical {n : ℕ} (hγ : Multiset.ofList γ.rowLens = Multiset.replicate n 1)
    (h : γ.card = μ.sum) (h0 : 0 ∉ μ) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) :=
  by
  by_cases hd : Dominates γ.rowLens (μ.sort (· ≥ ·))
  · simp_rw [Multiset.eq_replicate, Multiset.coe_card, Multiset.mem_coe, ←
      List.eq_replicate_iff] at hγ
    rw [hγ, replicate_one_dominates_iff, Multiset.sort_eq_replicate_iff] at hd
    · exact kostka_ineq_replicate hd
    · rw [Multiset.sort_sum, ← h, card_eq_sum_rowLens, hγ, List.sum_replicate, smul_eq_mul, mul_one]
    · contrapose! h0
      simpa using h0
  · exact kostka_ineq_not_dominate hd h h0

