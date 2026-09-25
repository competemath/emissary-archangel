/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Finset.Sups
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic


-- @@ L14-33 verbatim
/-!
# Positive difference

This file defines the positive difference of set families and sets in an ordered additive group.

## Main declarations

* `Finset.posDiffs`: Positive difference of set families.
* `Finset.posSub`: Positive difference of sets in an ordered additive group.

## Notations

We declare the following notation in the `finset_family` locale:
* `s \₊ t` for `finset.posDiffs s t`
* `s -₊ t` for `finset.posSub s t`

## References

* [Bollobás, Leader, Radcliffe, *Reverse Kleitman Inequalities][bollobasleaderradcliffe1989]
-/


-- @@ L35-35 verbatim
public section


-- @@ L37-37 verbatim
open scoped Pointwise


-- @@ L39-39 verbatim
variable {α : Type*}


-- @@ L41-41 verbatim
namespace Finset


-- @@ L43-43 verbatim
/-! ### Positive set difference -/


-- @@ L45-45 verbatim
section posDiffs

-- @@ L46-46 verbatim
section GeneralizedBooleanAlgebra

-- @@ L47-48 verbatim
variable [GeneralizedBooleanAlgebra α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α]
  {s t : Finset α} {a : α}


-- @@ L50-53 verbatim
/-- The positive set difference of finsets `s` and `t` is the set of `a \ b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posDiffs (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a \ b


-- @@ L55-55 verbatim
scoped[FinsetFamily] 
-- @@ L55-55 verbatim
infixl:70 " \\₊ " => Finset.posDiffs


-- @@ L57-57 verbatim
open scoped FinsetFamily


-- @@ L59-60 verbatim
@[simp] lemma mem_posDiffs : a ∈ s \₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b \ c = a := by
  simp_rw [posDiffs, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]


-- @@ L62-62 verbatim
@[simp] lemma posDiffs_empty (s : Finset α) : s \₊ ∅ = ∅ := by simp [posDiffs]

-- @@ L63-67 verbatim
@[simp] lemma empty_posDiffs (s : Finset α) : ∅ \₊ s = ∅ := by simp [posDiffs]

lemma posDiffs_subset_diffs : s \₊ t ⊆ s \\ t := by
  simp only [subset_iff, mem_posDiffs, mem_diffs]
  exact fun a ⟨b, hb, c, hc, _, ha⟩ ↦ ⟨b, hb, c, hc, ha⟩


-- @@ L69-69 verbatim
end GeneralizedBooleanAlgebra


-- @@ L71-71 verbatim
open scoped FinsetFamily


-- @@ L73-73 verbatim
section Finset


-- @@ L75-85 verbatim
variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

lemma card_posDiffs_self_le (h𝒜 : (𝒜 : Set (Finset α)).OrdConnected) :
    #(𝒜 \₊ 𝒜) ≤ #𝒜 := by
  revert h𝒜
  refine Finset.memberFamily_induction_on 𝒜 ?_ ?_ ?_
  · simp
  · intro
    rfl
  · rintro a 𝒜 h𝒜₀ h𝒜₁ h𝒜
    sorry


-- @@ L87-95 verbatim
/-- A **reverse Kleitman inequality**. -/
lemma le_card_upper_inter_lower (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) : #(𝒜 \₊ ℬ) ≤ #(𝒜 ∩ ℬ) := by
  refine (card_le_card ?_).trans (card_posDiffs_self_le ?_)
  · simp_rw [subset_iff, mem_posDiffs, mem_inter]
    rintro _ ⟨s, hs, t, ht, hts, rfl⟩
    exact ⟨s, ⟨hs, hℬ hts ht⟩, t, ⟨h𝒜 hts hs, ht⟩, hts, rfl⟩
  · rw [coe_inter]
    exact h𝒜.ordConnected.inter hℬ.ordConnected


-- @@ L97-97 verbatim
end Finset

-- @@ L98-98 verbatim
end posDiffs


-- @@ L100-100 verbatim
/-! ### Positive subtraction -/


-- @@ L102-102 verbatim
section posSub

-- @@ L103-104 verbatim
variable [Sub α] [Preorder α] [DecidableRel (α := α) (· ≤ ·)] [DecidableEq α] {s t : Finset α}
  {a : α}


-- @@ L106-109 verbatim
/-- The positive subtraction of finsets `s` and `t` is the set of `a - b` for `a ∈ s`, `b ∈ t`,
`b ≤ a`. -/
def posSub (s t : Finset α) : Finset α :=
  ((s ×ˢ t).filter fun (a, b) ↦ b ≤ a).image fun (a, b) ↦ a - b


-- @@ L111-111 verbatim
scoped[FinsetFamily] 
-- @@ L111-111 verbatim
infixl:70 " -₊ " => Finset.posSub


-- @@ L113-121 verbatim
open scoped FinsetFamily

lemma mem_posSub : a ∈ s -₊ t ↔ ∃ b ∈ s, ∃ c ∈ t, c ≤ b ∧ b - c = a := by
  simp_rw [posSub, mem_image, mem_filter, mem_product, Prod.exists, and_assoc, exists_and_left]

lemma posSub_subset_sub : s -₊ t ⊆ s - t := fun x ↦ by
  rw [mem_posSub, mem_sub]; exact fun ⟨b, hb, c, hc, _, h⟩ ↦ ⟨b, hb, c, hc, h⟩

lemma card_posSub_self_le (hs : (s : Set α).OrdConnected) : #(s -₊ s) ≤ #s := sorry


-- @@ L123-123 verbatim
end posSub

-- @@ L124-124 verbatim
end Finset
