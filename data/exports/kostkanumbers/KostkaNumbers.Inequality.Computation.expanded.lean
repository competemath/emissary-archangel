/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib
public import KostkaNumbers.Defs
import KostkaNumbers.Computation.HookLengthComputation
import KostkaNumbers.Computation.Computation
import KostkaNumbers.Computation.Partition
import KostkaNumbers.Inequality.Special
import KostkaNumbers.Inequality.TwoRows
import KostkaNumbers.Kostka.Diagonal
import KostkaNumbers.SmallDominate
import KostkaNumbers.Util.Diagrams
import KostkaNumbers.Diagrams.Diagrams


-- @@ L20-22 verbatim
/-!
Prove the inequality for the particular cases when μ is (2,2,1) or (2,2,2).
-/


-- @@ L24-24 verbatim
public section


-- @@ L26-26 verbatim
open YoungDiagram SemistandardYoungTableau Kostka


-- @@ L28-28 verbatim
variable {γ : YoungDiagram} {μ : Multiset ℕ} {n : ℕ}


-- @@ L30-75 expanded
theorem kostka_ineq_221 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum) (h0 : 0 ∉ μ)
    (hn : n = 5) (hμ : μ = { 2, 2, 1 }) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) :=
  by
  subst hn
  have h5 :=
    partition5 (Multiset.ofList γ.rowLens)
      (by simp [Multiset.sum_coe, ← card_eq_sum_rowLens, h, hμ])
      (by
        simp only [Multiset.mem_coe, gt_iff_lt]
        exact γ.pos_of_mem_rowLens)
  by_cases! hd : ¬Dominates γ.rowLens (μ.sort (· ≥ ·))
  · exact kostka_ineq_not_dominate hd h h0
  rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5
  · rw [ne_eq, eq_iff_rowLens_eq, horizontalDiagram_rowLens] at hhd
    · rw [Multiset.coe_eq_singleton] at h5
      contradiction
    · lia
  · refine kostka_ineq_hook (by lia) ?_ h h0
    rw [eq_iff_rowLens_eq', h5, hookDiagram_rowLens]
    · rfl
    · norm_num
  · have h5' : γ = ofRowLens [3, 2] (sorted_pair (by norm_num)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · grind
    rw [hμ, h5', kostka_32]
    exact le_trans (Nat.mul_le_mul_left _ kostka_g32u221_le) (by norm_num)
  · have h5' : γ = ofRowLens [3, 1, 1] (sorted_triple (by norm_num) (by rfl)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · grind
    grw [hμ, h5', kostka_311, kostka_g311u221]
    norm_num
  · have h5' : γ = ofRowLens [2, 2, 1] (sorted_triple (by rfl) (by norm_num)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self, h5]
      · rfl
      · grind
    rw [hμ, ← h5, kostka_self, h5, h5', kostka_221]
    norm_num
  · have h5' : γ.rowLens = [2, 1, 1, 1] :=
      by
      refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise (by simp) ?_
      rw [← Multiset.coe_eq_coe, h5]
      rfl
    rw [hμ, sort_triple_ge (by rfl) (by norm_num), h5', quad_dominates_triple] at hd
    simp at hd
  · exact kostka_ineq_vertical h5 h h0


-- @@ L78-155 expanded
theorem kostka_ineq_222 (hhd : γ ≠ horizontalDiagram n) (h : γ.card = μ.sum) (h0 : 0 ∉ μ)
    (hn : n = 6) (hμ : μ = { 2, 2, 2 }) :
    (n - 1) * kostkaNumber γ μ ≤ (μ.card - 1) * kostkaNumber γ (Multiset.replicate n 1) :=
  by
  subst hn
  have h6 :=
    partition6 (Multiset.ofList γ.rowLens)
      (by
        rw [Multiset.sum_coe, ← card_eq_sum_rowLens, h, hμ]
        norm_num)
      (by
        simp only [Multiset.mem_coe, gt_iff_lt]
        exact γ.pos_of_mem_rowLens)
  by_cases! hd : ¬Dominates γ.rowLens (μ.sort (· ≥ ·))
  · exact kostka_ineq_not_dominate hd h h0
  rcases h6 with h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6
  · rw [Multiset.coe_eq_singleton] at h6
    rw [ne_eq, eq_iff_rowLens_eq, horizontalDiagram_rowLens] at hhd
    · contradiction
    · positivity
  · have h6' : γ = hookDiagram 6 :=
      by
      rw [eq_iff_rowLens_eq', hookDiagram_rowLens, h6]
      · rfl
      · norm_num
    refine kostka_ineq_hook ?_ h6' h h0
    norm_num
  · have hγ : γ.rowLens = [6 - 2, 2] := by
      norm_num1
      refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise (by simp) ?_
      rw [← Multiset.coe_eq_coe, h6]
      rfl
    refine kostka_ineq_two_rows hγ ?_ (by norm_num) ?_ h ?_ h0 ?_
    · norm_num1
    · rw [card_eq_sum_rowLens, hγ]
      norm_num
    · simp [hμ]
    · simp only [min_triple (by rfl) (by rfl), hμ]
      rfl
  · have h6' : γ = ofRowLens [4, 1, 1] (sorted_triple (by norm_num) (by rfl)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    grw [hμ, h6', kostka_411, kostka_g411u222]
    norm_num
  · have h6' : γ = ofRowLens [3, 3] (sorted_pair (by rfl)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    grw [hμ, h6', kostka_33, kostka_g33u222]
    norm_num
  · have h6' : γ = ofRowLens [3, 2, 1] (sorted_triple (by norm_num) (by norm_num)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hμ, h6', kostka_321]
    refine le_trans (Nat.mul_le_mul_left _ kostka_g321u222_le) ?_
    norm_num
  · have h6' : γ.rowLens = [3, 1, 1, 1] :=
      by
      refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise (by simp) ?_
      rw [← Multiset.coe_eq_coe, h6]
      rfl
    rw [hμ, h6', sort_triple_ge (by rfl) (by rfl), quad_dominates_triple] at hd
    simp at hd
  · have h6' : γ = ofRowLens [2, 2, 2] (sorted_triple (by rfl) (by rfl)) :=
      by
      rw [eq_iff_rowLens_eq', rowLens_ofRowLens_eq_self (by simp), h6]
      rfl
    rw [hμ, ← h6, kostka_self, h6, h6', kostka_222]
    norm_num
  · have h6' : γ.rowLens = [2, 2, 1, 1] :=
      by
      refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise (by simp) ?_
      rw [← Multiset.coe_eq_coe, h6]
      rfl
    rw [hμ, h6', sort_triple_ge (by rfl) (by rfl), quad_dominates_triple] at hd
    simp at hd
  · have h6' : γ.rowLens = [2, 1, 1, 1, 1] :=
      by
      refine List.Perm.eq_of_pairwise' γ.rowLens_sorted.pairwise (by simp) ?_
      rw [← Multiset.coe_eq_coe, h6]
      rfl
    rw [hμ, h6', sort_triple_ge (by rfl) (by rfl)] at hd
    apply sum_three_le_of_dominates at hd
    simp at hd
  · exact kostka_ineq_vertical h6 h h0

