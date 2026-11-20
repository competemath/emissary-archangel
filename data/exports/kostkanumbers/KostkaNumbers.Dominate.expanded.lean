/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/
module

public import Mathlib
import KostkaNumbers.Util.Util


-- @@ L11-15 verbatim
/-!
Define the dominance relation for lists and prove some results about it.  This file does not develop
a thorough API for dominance, it just proves the things I needed for the proof.  In particular, this
file could probably be improved a lot.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-20 verbatim
def Dominates (L L' : List ℕ) := ∀ r : ℕ, ∑ i : Fin L.length with i.1 ≤ r,
  L.get i ≥ ∑ i : Fin L'.length with i.1 ≤ r, L'.get i


-- @@ L22-22 verbatim
notation L " ⊵ " L' => Dominates L L'

-- @@ L23-23 verbatim
notation L " ⊴ " L' => Dominates L' L


-- @@ L25-33 expanded
lemma get_zero_ge_of_dominates {L L' : List ℕ} (h : Dominates L L') (hL : 0 < L.length)
    (hL' : 0 < L'.length) : L[0] ≥ L'[0] :=
  by
  specialize h 0
  have hL0 : Finset.filter (fun i : Fin L.length => i.1 ≤ 0) Finset.univ = {⟨0, hL⟩} := by ext x;
    simp [Fin.eq_mk_iff_val_eq]
  have hL'0 : Finset.filter (fun i : Fin L'.length => i.1 ≤ 0) Finset.univ = {⟨0, hL'⟩} := by ext x;
    simp [Fin.eq_mk_iff_val_eq]
  rwa [hL0, hL'0, Finset.sum_singleton, Finset.sum_singleton, List.get_eq_getElem,
    List.get_eq_getElem] at h


-- @@ L35-65 expanded
lemma lengths_le_of_dominates {L L' : List ℕ} (hd : Dominates L L') (h : L.sum = L'.sum)
    (hp : ∀ i, L.get i > 0) : L.length ≤ L'.length :=
  by
  by_cases h0 : L'.length = 0
  · rw [h0]
    suffices Multiset.ofList L = 0 by simpa using this
    rw [← Multiset.sum_eq_zero_iff_eq_zero, Multiset.sum_coe, h]
    · simp only [List.length_eq_zero_iff] at h0
      rw [h0, List.sum_nil]
    · grind [Multiset.mem_coe, List.get_of_mem]
  contrapose! h
  specialize hd (L'.length - 1)
  refine ne_of_gt ?_
  simp only [List.get_eq_getElem, ge_iff_le] at hd
  have hLs : L'.sum = ∑ x : Fin L'.length with x.1 ≤ L'.length - 1, L'[x.1] :=
    by
    rw [← Fin.sum_univ_getElem]
    congr
    ext x
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, true_iff]
    exact Nat.le_sub_one_of_lt x.2
  rw [hLs]
  refine lt_of_le_of_lt hd ?_
  rw [← Fin.sum_univ_getElem]
  let i := (⟨L.length - 1, Nat.sub_one_lt_of_lt h⟩ : Fin L.length)
  refine Finset.sum_lt_sum_of_subset ?_ (Finset.mem_univ i) ?_ ?_ ?_
  · simp
  · simp [i]
    lia
  · rw [← List.get_eq_getElem]
    exact hp i
  · simp


-- @@ L67-74 expanded
lemma sum_two_le_of_dominates {L L' : List ℕ} (hd : Dominates L' L) (hL : 1 < L.length)
    (hL' : 1 < L'.length) : L[0] + L[1] ≤ L'[0] + L'[1] :=
  by
  specialize hd 1
  have hL1 : Finset.filter (fun i : Fin L.length => i.1 ≤ 1) Finset.univ = {⟨0, by lia⟩, ⟨1, hL⟩} :=
    by grind
  have hL'1 :
    Finset.filter (fun i : Fin L'.length => i.1 ≤ 1) Finset.univ = {⟨0, by lia⟩, ⟨1, hL'⟩} := by
    grind
  grind


-- @@ L76-84 expanded
lemma sum_three_le_of_dominates {L L' : List ℕ} (hd : Dominates L' L) (hL : 2 < L.length)
    (hL' : 2 < L'.length) : L[0] + L[1] + L[2] ≤ L'[0] + L'[1] + L'[2] :=
  by
  specialize hd 2
  have hL1 :
    Finset.filter (fun i : Fin L.length => i.1 ≤ 2) Finset.univ =
      {⟨0, by lia⟩, ⟨1, by lia⟩, ⟨2, hL⟩} :=
    by grind
  have hL1' :
    Finset.filter (fun i : Fin L'.length => i.1 ≤ 2) Finset.univ =
      {⟨0, by lia⟩, ⟨1, by lia⟩, ⟨2, hL'⟩} :=
    by grind
  grind


-- @@ L86-86 expanded
@[simp]
lemma dominates_self {L : List ℕ} : Dominates L L := by intro r; rfl


-- @@ L88-88 expanded
@[simp]
lemma dominates_nil {L : List ℕ} : Dominates L [] := by intro r; simp


-- @@ L90-90 expanded
@[simp]
lemma dominates_zero {L : List ℕ} : Dominates L [0] := by intro r; simp


-- @@ L92-99 expanded
lemma nil_dominates_of_sum_eq_zero {L : List ℕ} (h : L.sum = 0) : Dominates [] L :=
  by
  simp only [List.sum_eq_zero_iff, List.mem_iff_get, List.get_eq_getElem] at h
  intro r
  simp only [List.length_nil, Finset.univ_eq_empty, Finset.filter_empty, List.get_eq_getElem,
    Finset.sum_empty, ge_iff_le, nonpos_iff_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i hi
  exact h L[i.1] (by use i)


-- @@ L101-104 verbatim
lemma sum_with_eq_sum_with_length {L : List ℕ} {r : ℕ} (hr : r ≥ L.length - 1) :
    ∑ i : Fin L.length with i.1 ≤ r, L.get i =
    ∑ i : Fin L.length with i.1 ≤ L.length - 1, L.get i :=
  (Finset.sum_subset (by grind) (by grind)).symm


-- @@ L106-109 verbatim
lemma sum_with_eq_sum_with {L : List ℕ} {r s : ℕ} (hr : r ≥ L.length - 1) (hs : s ≥ L.length - 1) :
    ∑ i : Fin L.length with i.1 ≤ r, L.get i =
    ∑ i : Fin L.length with i.1 ≤ s, L.get i := by
  rw [sum_with_eq_sum_with_length hr, sum_with_eq_sum_with_length hs]


-- @@ L111-113 verbatim
lemma sum_with_eq_sum_univ {L : List ℕ} (r : ℕ) (h : r ≥ L.length - 1) :
    ∑ i, L.get i = ∑ i with i.1 ≤ r, L.get i :=
  (Finset.sum_subset (by simp) (by grind)).symm


-- @@ L115-138 expanded
lemma dominates_of_forall_lt_length {L L' : List ℕ}
    (h :
      ∀ r < L.length,
        ∑ i : Fin L.length with i.1 ≤ r, L.get i ≤ ∑ i : Fin L'.length with i.1 ≤ r, L'.get i) :
    Dominates L' L := by
  by_cases! hL0 : L.length = 0
  · grind [dominates_nil]
  by_cases! hL0' : L'.length = 0
  · specialize h (L.length - 1) (by lia)
    simp_rw [← sum_with_eq_sum_univ _ (by rfl), List.get_eq_getElem, Fin.sum_univ_getElem] at h
    rw [Finset.sum_eq_zero, Nat.le_zero] at h
    · rw [List.length_eq_zero_iff] at hL0'
      rw [hL0']
      exact nil_dominates_of_sum_eq_zero h
    · lia
  intro r
  have hle : min L.length L'.length ≠ 0 := by grind
  by_cases hr : r < L.length
  · exact h r hr
  · push Not at hr
    have hr : r ≥ L.length - 1 := by lia
    rw [sum_with_eq_sum_with hr (by rfl)]
    specialize h (L.length - 1) (by grind)
    refine le_trans h <| Finset.sum_le_sum_of_subset ?_
    grind


-- @@ L140-151 expanded
lemma dominates_of_forall_lt_min {L L' : List ℕ}
    (h :
      ∀ r < min L.length L'.length,
        ∑ i : Fin L.length with i.1 ≤ r, L.get i ≤ ∑ i : Fin L'.length with i.1 ≤ r, L'.get i)
    (hs : L.sum = L'.sum) : Dominates L' L :=
  by
  refine dominates_of_forall_lt_length ?_
  intro r hr'
  by_cases hr : r < min L.length L'.length
  · exact h r hr
  · push Not at hr
    conv => rhs; rw [← sum_with_eq_sum_univ _ (by grind)]
    simp_rw [List.get_eq_getElem, Fin.sum_univ_getElem, ← hs, ← Fin.sum_univ_getElem]
    refine Finset.sum_le_sum_of_subset ?_
    simp


-- @@ L153-157 expanded
lemma sum_le_sum_of_dominates {L L' : List ℕ} (hd : Dominates L' L) : L.sum ≤ L'.sum :=
  by
  simp_rw [← Fin.sum_univ_getElem, ← List.get_eq_getElem]
  rw [sum_with_eq_sum_univ (max L.length L'.length - 1) (by grind),
    sum_with_eq_sum_univ (max L.length L'.length - 1) (by grind)]
  exact hd (max L.length L'.length - 1)


-- @@ L159-174 expanded
lemma dominates_singleton_iff {L : List ℕ} {n : ℕ} (h : L.sum = n) (hn : n ≠ 0)
    (hp : ∀ i : Fin (L.length), L[i.1] > 0) : (Dominates L [n]) ↔ L = [n] :=
  by
  constructor
  · intro hd
    have hL : L.length ≤ 1 := by
      apply lengths_le_of_dominates at hd
      simpa [h, hp] using hd
    have hL0 : L.length > 0 :=
      by
      refine List.length_pos_of_sum_ne_zero _ ?_
      rwa [h]
    have hL1 : L.length = 1 := by lia
    rw [List.length_eq_one_iff] at hL1
    obtain ⟨m, hm⟩ := hL1
    rw [hm, List.sum_singleton] at h
    rw [hm, h]
  · exact (· ▸ dominates_self)


-- @@ L176-188 verbatim
private lemma List.forall_mem_eq_one_of_length_eq_sum {L : List ℕ} (h : L.length = L.sum)
    (hp : ∀ x ∈ L, x > 0) : ∀ x ∈ L, x = 1 := by
  contrapose! h
  obtain ⟨x, hxL, hx⟩ := h
  have hxL' := hxL
  rw [List.mem_iff_getElem] at hxL
  obtain ⟨n, ⟨hn, hnx⟩⟩ := hxL
  refine ne_of_lt ?_
  rw [← Fin.sum_univ_getElem, ← Finset.sum_erase_add _ _ (Finset.mem_univ ⟨n, hn⟩)]
  suffices L.length - 1 ≤ ∑ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin (L.length)), L[i.1] by grind
  refine le_trans ?_ (Finset.card_nsmul_le_sum _ _ 1 ?_)
  · simp
  · grind [List.getElem_mem]


-- @@ L190-209 expanded
lemma replicate_one_dominates_iff {L : List ℕ} {n : ℕ} (h : L.sum = n) (hp : ∀ x ∈ L, x > 0) :
    (Dominates (List.replicate n 1) L) ↔ L = List.replicate n 1 :=
  by
  constructor
  · intro hd
    rw [List.eq_replicate_iff]
    suffices L.length = n by
      constructor
      · exact this
      · refine List.forall_mem_eq_one_of_length_eq_sum ?_ hp
        rw [this, h]
    apply lengths_le_of_dominates at hd
    specialize hd ?_ ?_
    · rw [h, List.sum_replicate, smul_eq_mul, mul_one]
    · simp
    · rw [List.length_replicate] at hd
      refine antisymm ?_ hd
      rw [← h]
      exact List.length_le_sum_of_one_le _ hp
  · exact (· ▸ dominates_self)


-- @@ L211-224 expanded
lemma dominates_replicate_one {L : List ℕ} {n : ℕ} (h : L.sum = n) (hp : ∀ x ∈ L, x > 0) :
    Dominates L (List.replicate n 1) :=
  by
  refine dominates_of_forall_lt_min ?_ ?_
  · intro r hr
    simp only [List.get_eq_getElem, List.getElem_replicate, Finset.sum_const, smul_eq_mul, mul_one]
    refine le_trans ?_ (Finset.card_nsmul_le_sum _ _ 1 ?_)
    · have hiic :
        ({i : Fin (List.replicate n 1).length | i ≤ r} : Finset _) = Finset.Iic ⟨r, by grind⟩ := by
        grind
      have hiic' : ({i : Fin L.length | i ≤ r} : Finset _) = Finset.Iic ⟨r, by grind⟩ := by grind
      simp [hiic, hiic', Fin.card_Iic]
    · intro i _
      exact hp L[i.1] (List.getElem_mem (Fin.val_lt_of_le i (le_refl L.length)))
  · simp [h]

