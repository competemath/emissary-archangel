/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Aesop.BuiltinRules
public import Mathlib.Order.Heyting.Basic
public import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.SetLike


-- @@ L17-17 verbatim
/-! # Order -/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
section «lp_section_1»


-- @@ L24-24 verbatim
variable {α : Sort u} (r : α → α → Prop)


-- @@ L26-26 verbatim
local infix:50 " ≺ " => r


-- @@ L28-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def IsInfiniteDescendingChain (c : ℕ → α) : Prop := ∀ i, c (i + 1) ≺ c i


-- @@ L31-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def descendingChain (z : α) : ℕ → α
  | 0       => z
  | (i + 1) => @Classical.epsilon α ⟨z⟩ (fun y => y ≺ descendingChain z i ∧ ¬Acc r y)


-- @@ L36-44 verbatim
lemma not_acc_iff {x : α} : ¬Acc r x ↔ ∃ y, y ≺ x ∧ ¬Acc r y :=
  ⟨by
    intro hx
    by_contra h
    exact hx <| Acc.intro x (fun y hy => by
      simp_all),
  by
    rintro ⟨y, hy, hy'⟩ hx
    exact hy' (Acc.inv hx hy)⟩


-- @@ L46-46 verbatim
@[simp] lemma descending_chain_zero (z : α) : descendingChain r z 0 = z := rfl


-- @@ L48-60 verbatim
lemma isInfiniteDescendingChain_of_non_acc (z : α) (hz : ¬Acc r z) :
    IsInfiniteDescendingChain r (descendingChain r z) := by
  have : ∀ i, (i ≠ 0 → descendingChain r z i ≺ descendingChain r z i.pred) ∧
          ¬Acc r (descendingChain r z i) := by
    intro i
    induction i with
    | zero =>
        exact ⟨by intro h; exact False.elim (h rfl), hz⟩
    | succ i ih =>
      have : ∃ y, y ≺ (descendingChain r z i) ∧ ¬Acc r y := (not_acc_iff r).mp ih.2
      have hs := Classical.epsilon_spec this
      exact ⟨fun _ => hs.1, hs.2⟩
  intro i; simpa using (this (i + 1)).1


-- @@ L62-62 verbatim
end «lp_section_1»


-- @@ L64-64 verbatim
section «lp_section_2»


-- @@ L66-66 verbatim
variable {α : Type*} [HeytingAlgebra α]


-- @@ L68-76 verbatim
lemma himp_himp_inf_himp_inf_le (a b c : α) : (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := calc
  (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a = (a ⇨ b ⇨ c) ⊓ b ⊓ a := by simp only [inf_assoc, himp_inf_self]
  _                         = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by simp only [inf_assoc, inf_comm a b]
  _                         ≤ (b ⇨ c) ⊓ b         := by
    simp only [himp_inf_self a (b ⇨ c), le_inf_iff]
    constructor
    · simp only [inf_assoc, inf_le_left]
    · exact inf_le_right
  _                         ≤ c                   := by simp


-- @@ L78-86 verbatim
lemma himp_inf_himp_inf_sup_le (a b c : α) : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c := by
  have ha : a ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have hb : b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, inf_comm (a ⇨ c) (b ⇨ c), ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have : a ⊔ b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := sup_le_iff.mpr ⟨ha, hb⟩
  simpa only [GeneralizedHeytingAlgebra.le_himp_iff, inf_comm (a ⊔ b)] using this


-- @@ L88-88 verbatim
end «lp_section_2»
