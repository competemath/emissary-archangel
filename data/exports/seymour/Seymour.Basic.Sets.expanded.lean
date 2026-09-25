import Seymour.Basic.Conversions


-- @@ L3-7 verbatim
/-!
# Sets

This file provides lemmas about sets that are not present in Mathlib.
-/


-- @@ L9-9 verbatim
variable {α : Type*}


-- @@ L11-12 verbatim
lemma Disjoint.ni_right_of_in_left {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ X) : a ∉ Y :=
  (by simpa [hXY.inter_eq] using Set.mem_inter ha ·)


-- @@ L14-15 verbatim
lemma Disjoint.ni_left_of_in_right {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ Y) : a ∉ X :=
  hXY.symm.ni_right_of_in_left ha


-- @@ L17-18 verbatim
lemma in_left_of_in_union_of_ni_right {X Y : Set α} {a : α} (haXY : a ∈ X ∪ Y) (haY : a ∉ Y) : a ∈ X := by
  tauto_set


-- @@ L20-21 verbatim
lemma in_right_of_in_union_of_ni_left {X Y : Set α} {a : α} (haXY : a ∈ X ∪ Y) (haX : a ∉ X) : a ∈ Y := by
  tauto_set


-- @@ L23-24 verbatim
lemma singleton_inter_in_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ X :=
  Set.mem_of_mem_inter_left (ha.symm.subset rfl)


-- @@ L26-27 verbatim
lemma singleton_inter_in_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ Y :=
  Set.mem_of_mem_inter_right (ha.symm.subset rfl)


-- @@ L29-32 expanded
lemma right_eq_right_of_union_eq_union {A₁ A₂ B₁ B₂ : Set α} (hA : A₁ = A₂) (hB₁ : Disjoint A₁ B₁)
    (hB₂ : Disjoint A₂ B₂) (hAB : A₁ ∪ B₁ = A₂ ∪ B₂) : B₁ = B₂ := by tauto_set


-- @@ L34-36 expanded
lemma union_disjoint_union_iff (A₁ A₂ B₁ B₂ : Set α) :
    Disjoint (A₁ ∪ A₂) (B₁ ∪ B₂) ↔
      (Disjoint A₁ B₁ ∧ Disjoint A₂ B₁) ∧ (Disjoint A₁ B₂ ∧ Disjoint A₂ B₂) :=
  by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]


-- @@ L38-41 expanded
lemma union_disjoint_union_aux {A B C D : Set α} (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hCB : Disjoint C B) (hAD : Disjoint A D) : Disjoint (A ∪ C) (B ∪ D) :=
  by
  rw [union_disjoint_union_iff]
  exact ⟨⟨hAB, hCB⟩, ⟨hAD, hCD⟩⟩


-- @@ L43-45 expanded
lemma union_disjoint_union {A B C D : Set α} (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAD : Disjoint A D) (hBC : Disjoint B C) : Disjoint (A ∪ C) (B ∪ D) :=
  union_disjoint_union_aux hAB hCD hBC.symm hAD


-- @@ L47-48 verbatim
lemma Subtype.subst_elem {X Y : Set α} (x : X) (hXY : X = Y) : (hXY ▸ x).val = x.val := by
  aesop


-- @@ L50-51 verbatim
lemma eq_toFinset_of_toSet_eq {s : Finset α} {S : Set α} [Fintype S] (hsS : s.toSet = S) : s = S.toFinset := by
  aesop


-- @@ L53-57 expanded
def HasSubset.Subset.equiv {A B : Set α} [∀ i, Decidable (i ∈ A)] (hAB : A ⊆ B) :
    A.Elem ⊕ (B \ A).Elem ≃ B.Elem :=
  ⟨(·.casesOn hAB.elem Set.diff_subset.elem), fun i : B =>
    if hiA : i.val ∈ A then Sum.inl ⟨i.val, hiA⟩ else Sum.inr ⟨i.val, by simp [hiA]⟩, fun _ => by
    aesop, fun _ => by aesop⟩


-- @@ L59-59 verbatim
variable {β : Type*}


-- @@ L61-63 verbatim
lemma ofSupportFinite_support_eq [Zero β] {f : α → β} {S : Set α} (hS : Finite S) (hfS : f.support = S) :
    (Finsupp.ofSupportFinite f (hfS ▸ hS)).support = S := by
  aesop


-- @@ L65-80 expanded
lemma finset_of_cardinality_between [Fintype α] [Fintype β] {n : ℕ} (hα : Fintype.card α < n)
    (hn : n ≤ Fintype.card α + Fintype.card β) :
    ∃ b : Finset β, Fintype.card (α ⊕ b) = n ∧ Nonempty b :=
  by
  have hβ : n - Fintype.card α ≤ Fintype.card β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - Fintype.card α :=
    (Finset.exists_subset_card_eq hβ).imp (by simp)
  use s
  constructor
  · rw [Fintype.card_sum, Fintype.card_coe, hs]
    omega
  · by_contra hs'
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at hs'
      exact Finset.eq_empty_of_forall_not_mem hs'
    omega

