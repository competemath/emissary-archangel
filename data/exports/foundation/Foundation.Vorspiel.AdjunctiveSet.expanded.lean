module

public import Mathlib.Data.Set.Finite.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-8 verbatim
class Adjoin (β : outParam Type*) (α : Type*) where
  adjoin : β → α → α

-- @@ L9-9 verbatim
export Adjoin (adjoin)


-- @@ L11-11 verbatim
instance (α : Type*) : Adjoin α (Set α) := ⟨insert⟩


-- @@ L13-13 verbatim
instance (α : Type*) : Adjoin α (List α) := ⟨List.cons⟩


-- @@ L15-15 verbatim
instance (α : Type*) : Adjoin α (Multiset α) := ⟨Multiset.cons⟩


-- @@ L17-17 verbatim
instance (α : Type*) [DecidableEq α] : Adjoin α (Finset α) := ⟨insert⟩


-- @@ L19-22 verbatim
class AdjunctiveSet (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Adjoin β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ adjoin z a ↔ x = z ∨ x ∈ a


-- @@ L24-24 verbatim
attribute [simp] AdjunctiveSet.not_mem_empty AdjunctiveSet.mem_cons_iff


-- @@ L26-30 verbatim
instance Set.adjunctiveSet : AdjunctiveSet α (Set α) where
  Subset := (· ⊆ ·)
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]


-- @@ L32-35 verbatim
instance List.adjunctiveSet : AdjunctiveSet α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]


-- @@ L37-40 verbatim
instance Multiset.adjunctiveSet : AdjunctiveSet α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]


-- @@ L42-46 verbatim
instance Finset.adjunctiveSet [DecidableEq α] : AdjunctiveSet α (Finset α) where
  Subset := (· ⊆ ·)
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]


-- @@ L48-48 verbatim
namespace AdjunctiveSet


-- @@ L50-50 verbatim
variable {β α : Type*} [AdjunctiveSet β α]


-- @@ L52-52 verbatim
def set : α → Set β := fun a ↦ {x | x ∈ a}


-- @@ L54-56 verbatim
@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]


-- @@ L58-58 verbatim
@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)


-- @@ L60-64 verbatim
@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb))

lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)


-- @@ L66-66 verbatim
@[simp] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]


-- @@ L68-68 verbatim
@[simp] lemma mem_cons (a : α) (x : β) : x ∈ adjoin x a := by simp [mem_cons_iff]


-- @@ L70-70 verbatim
@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ adjoin x a := by simp [subset_iff, mem_cons_iff]; tauto


-- @@ L72-72 verbatim
@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]


-- @@ L74-74 verbatim
@[simp] lemma set_cons (z : β) (a : α) : set (adjoin z a) = insert z (set a) := by ext; simp [set]


-- @@ L76-76 verbatim
def Finite (a : α) : Prop := (set a).Finite


-- @@ L78-81 verbatim
@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

lemma Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)


-- @@ L83-84 verbatim
@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (adjoin z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), by simp [Finite]⟩


-- @@ L86-88 verbatim
def addList (a : α) : List β → α
  | [] => a
  | x :: xs => adjoin x (addList a xs)


-- @@ L90-92 verbatim
def _root_.List.toAdjunctiveSet : List β → α
  | [] => ∅
  | x :: xs => adjoin x xs.toAdjunctiveSet


-- @@ L94-94 verbatim
noncomputable def _root_.Finset.toAdjunctiveSet : Finset β → α := fun s ↦ s.toList.toAdjunctiveSet


-- @@ L96-97 verbatim
@[simp] lemma mem_list_toAdjunctiveSet {x : β} {l : List β} : x ∈ (l.toAdjunctiveSet : α) ↔ x ∈ l := by
  induction l <;> simp [List.toAdjunctiveSet, *]


-- @@ L99-99 verbatim
@[simp] lemma mem_finset_toAdjunctiveSet {x : β} {s : Finset β} : x ∈ (s.toAdjunctiveSet : α) ↔ x ∈ s := by simp [Finset.toAdjunctiveSet]


-- @@ L101-101 verbatim
@[simp] lemma list_toAdjunctiveSet_finite (l : List β) : Finite (l.toAdjunctiveSet : α) := by simp [Finite, set]


-- @@ L103-103 verbatim
@[simp] lemma finset_toAdjunctiveSet_finite (s : Finset β) : Finite (s.toAdjunctiveSet : α) := by simp [Finite, set]


-- @@ L105-105 verbatim
end AdjunctiveSet


-- @@ L107-107 verbatim
namespace Set


-- @@ L109-111 verbatim
variable {α : Type*}

lemma cons_eq (a : α) (s : Set α) : adjoin a s = insert a s := rfl


-- @@ L113-113 verbatim
@[simp] lemma adjunctiveSet_set (s : Set α) : AdjunctiveSet.set s = s := rfl


-- @@ L115-115 verbatim
@[simp] lemma adjunctiveSet_finite_iff (s : Set α) : AdjunctiveSet.Finite s ↔ s.Finite := by simp [AdjunctiveSet.Finite]


-- @@ L117-117 verbatim
end Set


-- @@ L119-119 verbatim
end
