/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.ToAdditive
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L14-14 verbatim
/-! # Collection -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Cons (β : outParam Type*) (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  cons : β → α → α

-- @@ L23-23 verbatim
export Cons (cons)


-- @@ L25-25 verbatim
instance (α : Type*) : Cons α (Set α) := ⟨insert⟩


-- @@ L27-27 verbatim
instance (α : Type*) : Cons α (List α) := ⟨List.cons⟩


-- @@ L29-29 verbatim
instance (α : Type*) : Cons α (Multiset α) := ⟨Multiset.cons⟩


-- @@ L31-31 verbatim
instance (α : Type*) [DecidableEq α] : Cons α (Finset α) := ⟨insert⟩


-- @@ L33-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Collection (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α,
  EmptyCollection α, Cons β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ cons z a ↔ x = z ∨ x ∈ a


-- @@ L40-40 verbatim
attribute [simp] Collection.not_mem_empty Collection.mem_cons_iff


-- @@ L42-46 verbatim
instance Set.collection : Collection α (Set α) where
  Subset a b := a ⊆ b
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]


-- @@ L48-51 verbatim
instance List.collection : Collection α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]


-- @@ L53-56 verbatim
instance Multiset.collection : Collection α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]


-- @@ L58-62 verbatim
instance Finset.collection [DecidableEq α] : Collection α (Finset α) where
  Subset a b := a ⊆ b
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]


-- @@ L64-64 verbatim
namespace Collection


-- @@ L66-66 verbatim
variable {β α : Type*} [Collection β α]


-- @@ L68-69 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def set : α → Set β := fun a ↦ {x | x ∈ a}


-- @@ L71-71 verbatim
@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]


-- @@ L73-73 verbatim
lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]


-- @@ L75-75 verbatim
@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)


-- @@ L77-79 verbatim
@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha)
    (subset_iff_set_subset_set.mp hb))


-- @@ L81-82 verbatim
lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)


-- @@ L84-84 verbatim
@[simp 1100] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]


-- @@ L86-86 verbatim
@[simp 1100] lemma mem_cons (a : α) (x : β) : x ∈ cons x a := by simp [mem_cons_iff]


-- @@ L88-89 verbatim
@[simp] lemma subset_cons (a : α) (x : β) :
    a ⊆ cons x a := by simp [subset_iff, mem_cons_iff]; tauto


-- @@ L91-91 verbatim
@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]


-- @@ L93-93 verbatim
@[simp] lemma set_cons (z : β) (a : α) : set (cons z a) = insert z (set a) := by ext; simp [set]


-- @@ L95-96 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Finite (a : α) : Prop := (set a).Finite


-- @@ L98-98 verbatim
@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]


-- @@ L100-101 verbatim
lemma _root_.Collection.Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)


-- @@ L103-106 verbatim
@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (cons z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), fun h ↦ by
    rw [Finite, set_cons]
    exact Set.Finite.insert z h⟩


-- @@ L108-111 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def addList (a : α) : List β → α
  | [] => a
  | x :: xs => cons x (addList a xs)


-- @@ L113-116 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.List.toCollection : List β → α
  | [] => ∅
  | x :: xs => cons x xs.toCollection


-- @@ L118-119 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.Finset.toCollection : Finset β → α := fun s ↦ s.toList.toCollection


-- @@ L121-122 verbatim
@[simp] lemma mem_list_toCollection {x : β} {l : List β} : x ∈ (l.toCollection : α) ↔ x ∈ l := by
  induction l <;> simp [List.toCollection, *]


-- @@ L124-125 verbatim
@[simp] lemma mem_finset_toCollection {x : β} {s : Finset β} : x ∈ (s.toCollection :
    α) ↔ x ∈ s := by simp [Finset.toCollection]


-- @@ L127-128 verbatim
@[simp] lemma list_toCollection_finite (l : List β) : Finite (l.toCollection :
    α) := by simp [Finite, set]


-- @@ L130-131 verbatim
@[simp] lemma finset_toCollection_finite (s : Finset β) : Finite (s.toCollection :
    α) := by simp [Finite, set]


-- @@ L133-133 verbatim
end Collection


-- @@ L135-135 verbatim
namespace Set


-- @@ L137-137 verbatim
variable {α : Type*}


-- @@ L139-139 verbatim
lemma cons_eq (a : α) (s : Set α) : cons a s = insert a s := rfl


-- @@ L141-141 verbatim
@[simp] lemma collection_set (s : Set α) : Collection.set s = s := rfl


-- @@ L143-144 verbatim
@[simp] lemma collection_finite_iff (s : Set α) :
    Collection.Finite s ↔ s.Finite := by simp [Collection.Finite]


-- @@ L146-146 verbatim
end Set
