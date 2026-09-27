/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.SetTheory.Cardinal.Order
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF


-- @@ L18-22 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L24-24 verbatim
@[expose] public section



-- @@ L27-29 verbatim
attribute [simp_lengths]
  List.length_append List.length_cons List.length_nil
  List.length_take List.length_drop List.length_map List.length_tail


-- @@ L31-33 verbatim
variable {α β I : Type*} {γ : Type* → Type*} {a : α}

--used in gale stewart and undetermined

-- @@ L34-35 verbatim
@[simp] lemma Nat.add_div' (k m n : ℕ) (h : n < k) : (k * m + n) / k = m := by
  apply Nat.div_eq_of_lt_le <;> linarith --omega instead of linarith fails for either subgoal

-- @@ L36-37 verbatim
@[simp] lemma Nat.add_sub_sub_of_le {m n p : ℕ} (mn : m ≤ n) (np : n ≤ p) :
  (n - m) + (p - n) = p - m := by zify [mn, np, mn.trans np]; ring

-- @@ L38-38 verbatim
@[simp] lemma div_add_self (n : ℕ) : (n + n) % 2 = 0 := by omega


-- @@ L40-44 verbatim
lemma Set.hEq_of_image_eq {α} {A A' : Set α} (h : A = A') {B : Set A} {B' : Set A'}
  (h' : Subtype.val '' B = Subtype.val '' B') : HEq B B' := by
  subst h; rw [← Set.preimage_image_eq B Subtype.val_injective,
    ← Set.preimage_image_eq B' Subtype.val_injective, h']
--cf. exists_exists_eq_and

-- @@ L45-46 verbatim
lemma exists_exists_and_eq {f : α → β} {p : β → Prop} :
    (∃ b, p b ∧ (∃ a, b = f a)) ↔ ∃ a, p (f a) := by aesop

-- @@ L47-48 verbatim
lemma exists_exists_and_eq' {f : α → β} {p : β → Prop} {r : α → Prop} :
    (∃ b, p b ∧ (∃ a, r a ∧ b = f a)) ↔ ∃ a, r a ∧ p (f a) := by aesop

-- @@ L49-53 verbatim
lemma Disjoint.subset_iff_empty {s t : Set α} (h : Disjoint s t) : s ⊆ t ↔ s ⊆ ∅ := by
  rw [Set.disjoint_iff_inter_eq_empty] at h
  constructor <;> intro h' x hx
  · exact h.subset ⟨hx, h' hx⟩
  · cases h' hx

-- @@ L54-63 verbatim
lemma pairwiseDisjoint_iff {α : I → Type*} (f : ∀ i, α i → β) :
  Set.univ.PairwiseDisjoint (fun i ↦ Set.range (f i)) ↔ ∀ ⦃i x j y⦄, f i x = f j y → i = j := by
  constructor
  · intros h i x j y he; by_contra hne
    apply @h i trivial j trivial hne {f i x}
    · rintro _ rfl; use x
    · rintro _ rfl; use y; exact he.symm
    · rfl
  · intros h i _ j _ ij _ hi hj _ hx; obtain ⟨_, rfl⟩ := hi hx; obtain ⟨_, he⟩ := hj hx
    exact ij <| h he.symm


-- @@ L65-67 verbatim
lemma sigma_eq {β : α → Sort*} {a a' : α} (h : a = a') {b : β a} :
  PSigma.mk a b = PSigma.mk a' (cast (by rw [h]) b : β a') := by
  subst h; rfl


-- @@ L69-71 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def uncurryProp {α : Type*} {β : α → Prop} {γ : ∀ a, β a → Sort*} --exists already?
  (f : ∀ (x) (y : β x), γ x y) (x : {a | β a}) : γ x.val x.prop := f x.val x.prop


-- @@ L73-73 verbatim
open Cardinal

-- @@ L74-75 verbatim
lemma equals_nonempty_some {A : Set α} {ne : A.Nonempty} (h : a = ne.some) : a ∈ A := --avoid
  cast (h.symm ▸ rfl) ne.some_mem

-- @@ L76-91 verbatim
universe u in
lemma Cardinal.choose_injection {α β : Type u} (f : α → Set β) (h : ∀ a, #α ≤ #(f a)) :
    ∃ g : α → β, g.Injective ∧ ∀ a, g a ∈ f a := by
  let ⟨wo, hwo, hwol⟩ := Cardinal.exists_ord_eq α
  let recg (a : α) (recg : (b : α) → wo b a → β) : β :=
    (Set.nonempty_iff_ne_empty.mpr fun hf ↦
      not_le_of_gt (lt_of_lt_of_le (lt_of_le_of_lt
      (Cardinal.mk_le_of_surjective Set.rangeFactorization_surjective :
        #(Set.range (uncurryProp recg)) ≤ _)
      (Cardinal.card_typein_lt (r := wo) a hwol)) (h a))
      (Cardinal.mk_le_mk_of_subset (Set.sdiff_eq_empty.mp hf))).some
  refine ⟨hwo.wf.fix recg, ?_, ?_⟩
  · intro a a' he
    rcases trichotomous_of wo a a' with h | h | h <;> [symm at he; exact h; skip] <;>
     (rw [hwo.wf.fix_eq] at he; cases (equals_nonempty_some he.symm).2 ⟨⟨_, h⟩, rfl⟩)
  · intro a; rw [hwo.wf.fix_eq]; exact Set.sdiff_subset (Set.Nonempty.some_mem _)
