/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.TautoSet


-- @@ L14-18 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Applications.General

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
lemma diff_subset_union {I} {A B C : Set I} : A \ C ⊆ (A \ B) ∪ (B \ C) := by tauto_set

-- @@ L24-28 verbatim
lemma projection_formula {α β} (f : α → β) (X : Set α) (Y : Set β) :
  Disjoint X (f⁻¹' Y) ↔ Disjoint (f '' X) Y := by --exists?
  constructor <;> intro h
  · rw [Set.disjoint_iff] at *; rintro _ ⟨⟨x, hx, rfl⟩, hy⟩; exact h ⟨hx, hy⟩
  · exact Set.disjoint_of_subset_left (Set.subset_preimage_image f X) (h.preimage f)


-- @@ L30-30 verbatim
namespace Filter

-- @@ L31-31 verbatim
variable {α β γ : Type*} {s t : Set α} {l : Filter α}

-- @@ L32-34 verbatim
lemma mem_congr (h : s =ᶠ[l] t) : s ∈ l ↔ t ∈ l := by
  apply congr_sets
  rwa [eventuallyEqSet_iff, eventually_iff] at h

-- @@ L35-40 verbatim
lemma eventuallyEq_set' {α} {s t : Set α} {l : Filter α} :
  l.EventuallyEqSet s t ↔ (s \ t)ᶜ ∈ l ∧ (t \ s)ᶜ ∈ l := by
  constructor <;> intro h
  · simp [Filter.mem_congr (h.diff (Filter.EventuallyEqSet.refl _ t)).compl,
      Filter.mem_congr ((Filter.EventuallyEqSet.refl _ t).diff h).compl]
  · rw [Filter.eventuallyEqSet_iff]; filter_upwards [h.1, h.2]; tauto_set

-- @@ L41-41 verbatim
end Filter
