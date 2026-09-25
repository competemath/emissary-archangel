/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.UpperLower.Basic


-- @@ L12-28 verbatim
/-!
# Set family certificates

This file defines the certificator of two families of sets. If we consider set families `𝒜` and `ℬ`
as probabilistic events, the size of the certificator `𝒜 □ ℬ` corresponds to the probability that
`𝒜` and `ℬ` occur "disjointly".

## Main declarations

* `finset.certificator`: Certificator of two elements of a Boolean algebra
* `finset.card_certificator_le`: The Van den Berg-Kesten-Reimer inequality: The probability that `𝒜`
  and `ℬ` occur "disjointly" is less than the product of their probabilities.

## References

* D. Reimer, *Proof of the Van den Berg–Kesten Conjecture*
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
open scoped FinsetFamily


-- @@ L34-34 verbatim
variable {α : Type*}


-- @@ L36-36 verbatim
namespace Finset

-- @@ L37-37 verbatim
section BooleanAlgebra

-- @@ L38-38 verbatim
variable [BooleanAlgebra α] (s t u : Finset α) {a : α}


-- @@ L40-42 verbatim
noncomputable def certificator : Finset α :=
  open scoped Classical in
  {a ∈ s ∩ t | ∃ x y, IsCompl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧ ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t}


-- @@ L44-44 verbatim
scoped[FinsetFamily] infixl:70 " □ " => Finset.certificator


-- @@ L46-46 verbatim
variable {s t u}


-- @@ L48-54 expanded
@[simp]
lemma mem_certificator :
    a ∈ Finset.certificator s t ↔
      ∃ x y, IsCompl x y ∧ (∀ ⦃b⦄, a ⊓ x = b ⊓ x → b ∈ s) ∧ ∀ ⦃b⦄, a ⊓ y = b ⊓ y → b ∈ t :=
  by
  classical
  rw [certificator, mem_filter, and_iff_right_of_imp]
  rintro ⟨u, v, _, hu, hv⟩
  exact mem_inter.2 ⟨hu rfl, hv rfl⟩


-- @@ L56-57 expanded
lemma certificator_subset_inter [DecidableEq α] : Finset.certificator s t ⊆ s ∩ t := by
  unfold certificator; convert filter_subset ..


-- @@ L59-65 expanded
open scoped Classical in
lemma certificator_subset_disjSups : Finset.certificator s t ⊆ s ○ t :=
  by
  simp_rw [subset_iff, mem_certificator, mem_disjSups]
  rintro x ⟨u, v, huv, hu, hv⟩
  refine
    ⟨x ⊓ u, hu (inf_right_idem _ _).symm, x ⊓ v, hv (inf_right_idem _ _).symm,
      huv.disjoint.mono inf_le_right inf_le_right, ?_⟩
  rw [← inf_sup_left, huv.codisjoint.eq_top, inf_top_eq]


-- @@ L67-67 verbatim
variable (s t u)


-- @@ L69-70 expanded
lemma certificator_comm : Finset.certificator s t = Finset.certificator t s := by ext s;
  rw [mem_certificator, exists_comm]; simp [isCompl_comm, and_comm]


-- @@ L72-78 expanded
lemma IsUpperSet.certificator_eq_inter [DecidableEq α] (hs : IsUpperSet (s : Set α))
    (ht : IsLowerSet (t : Set α)) : Finset.certificator s t = s ∩ t :=
  by
  refine certificator_subset_inter.antisymm fun a ha ↦ mem_certificator.2 ⟨a, aᶜ, isCompl_compl, ?_⟩
  rw [mem_inter] at ha
  simp only [@eq_comm _ ⊥, ← sdiff_eq, inf_idem, right_eq_inf, _root_.sdiff_self, sdiff_eq_bot_iff]
  exact ⟨fun b hab ↦ hs hab ha.1, fun b hab ↦ ht hab ha.2⟩


-- @@ L80-86 expanded
lemma IsLowerSet.certificator_eq_inter [DecidableEq α] (hs : IsLowerSet (s : Set α))
    (ht : IsUpperSet (t : Set α)) : Finset.certificator s t = s ∩ t :=
  by
  refine
    certificator_subset_inter.antisymm fun a ha ↦ mem_certificator.2 ⟨aᶜ, a, isCompl_compl.symm, ?_⟩
  rw [mem_inter] at ha
  simp only [@eq_comm _ ⊥, ← sdiff_eq, inf_idem, right_eq_inf, _root_.sdiff_self, sdiff_eq_bot_iff]
  exact ⟨fun b hab ↦ hs hab ha.1, fun b hab ↦ ht hab ha.2⟩


-- @@ L88-95 expanded
open scoped Classical in
lemma IsUpperSet.certificator_eq_disjSups (hs : IsUpperSet (s : Set α))
    (ht : IsUpperSet (t : Set α)) : Finset.certificator s t = s ○ t :=
  by
  refine certificator_subset_disjSups.antisymm fun a ha ↦ mem_certificator.2 ?_
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_disjSups.1 ha
  refine ⟨x, xᶜ, isCompl_compl, ?_⟩
  simp only [inf_of_le_right, le_sup_left, right_eq_inf, ← sdiff_eq, hxy.sup_sdiff_cancel_left]
  exact ⟨fun b hab ↦ hs hab hx, fun b hab ↦ ht (hab.trans_le sdiff_le) hy⟩


-- @@ L97-97 verbatim
end BooleanAlgebra


-- @@ L99-99 verbatim
open scoped FinsetFamily


-- @@ L101-101 verbatim
variable [DecidableEq α] [Fintype α] {𝒜 ℬ 𝒞 : Finset (Finset α)}


-- @@ L103-105 expanded
/-- The **Van den Berg-Kesten-Reimer Inequality**: The probability that `𝒜` and `ℬ` occur
"disjointly" is less than the product of their probabilities. -/
lemma card_certificator_le : 2 ^ Fintype.card α * #(Finset.certificator 𝒜 ℬ) ≤ #𝒜 * #ℬ :=
  sorry


-- @@ L107-107 verbatim
end Finset
