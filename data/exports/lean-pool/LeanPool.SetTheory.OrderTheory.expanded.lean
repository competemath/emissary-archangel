/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic


-- @@ L10-15 verbatim
/-!
# Order-theoretic preliminaries

This module collects order-theoretic lemmas about infima and suprema in conditionally
complete lattices, in particular closure under bounded infima and suprema.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Function OrderDual Set


-- @@ L21-21 verbatim
variable {α β : Type*} [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]


-- @@ L23-24 verbatim
/-- The `sInfClosed` declaration. -/
def sInfClosed (S : Set α) := ∀ s ⊆ S, s.Nonempty → BddBelow s → sInf s ∈ S

-- @@ L25-26 verbatim
/-- The `sSupClosed` declaration. -/
def sSupClosed (S : Set α) := ∀ s ⊆ S, s.Nonempty → BddAbove s → sSup s ∈ S


-- @@ L28-28 verbatim
lemma sInfClosed_top : sInfClosed (⊤ : Set α) := by simp [sInfClosed]

-- @@ L29-29 verbatim
lemma sInfClosed_Ici (x : α) : sInfClosed (Ici x) := fun _ hsub hne _ => le_csInf hne hsub

-- @@ L30-30 verbatim
lemma sInfClosed_bot : sInfClosed (⊥ : Set α) := by simp [sInfClosed]

-- @@ L31-31 verbatim
lemma sSupClosed_top : sSupClosed (⊤ : Set α) := by simp [sSupClosed]

-- @@ L32-32 verbatim
lemma sSupClosed_Iic (x : α) : sSupClosed (Iic x) := fun _ hsub hne _ => csSup_le hne hsub

-- @@ L33-33 verbatim
lemma sSupClosed_bot : sSupClosed (⊥ : Set α) := by simp [sSupClosed]


-- @@ L35-39 verbatim
/-- The `ContinuousOrderMap` type. -/
class ContinuousOrderMap (f : α → β) where
  monotone : Monotone f
  preimage_Ici_closed : ∀ x, sInfClosed (f ⁻¹' (Ici x))
  preimage_Iic_closed : ∀ x, sSupClosed (f ⁻¹' (Iic x))


-- @@ L41-44 verbatim
/-- The `ContinuousOrderMapBounded` type. -/
class ContinuousOrderMapBounded (f : α → β) extends ContinuousOrderMap f where
  bounded_preimage_Ici : ∀ y, BddBelow (f ⁻¹' (Ici y))
  bounded_preimage_Iic : ∀ y, BddAbove (f ⁻¹' (Iic y))


-- @@ L46-46 verbatim
namespace ContinuousOrderMap


-- @@ L48-48 verbatim
variable (f : α → β) [ContinuousOrderMap f]

-- @@ L49-49 verbatim
open ContinuousOrderMap


-- @@ L51-54 verbatim
instance : ContinuousOrderMap (toDual ∘ f ∘ ofDual) where
  monotone := monotone.dual
  preimage_Ici_closed := preimage_Iic_closed (f := f)
  preimage_Iic_closed := preimage_Ici_closed (f := f)


-- @@ L56-56 verbatim
variable {ι} [Nonempty ι] {s : Set α} {g : ι → α}


-- @@ L58-66 verbatim
lemma map_sInf' (hne : s.Nonempty) (hbdd : BddBelow s) : f (sInf s) = sInf (f '' s) := by
  refine (IsGLB.csInf_eq ?_ (by simpa)).symm
  simpa only [
    IsGLB, IsGreatest, lowerBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_ofPred_eq, upperBounds
  ] using ⟨
    fun _ hs => monotone (csInf_le hbdd hs),
    fun y hy => preimage_Ici_closed _ _ hy hne hbdd
  ⟩


-- @@ L68-69 verbatim
lemma map_sInf (hne : s.Nonempty) (hbdd : BddBelow s) : f (sInf s) = ⨅ x : s, f x := by
  rw [← sInf_image', ← map_sInf' f hne hbdd]


-- @@ L71-72 verbatim
lemma map_sSup' (hne : s.Nonempty) (hbdd : BddAbove s) : f (sSup s) = sSup (f '' s) :=
  map_sInf' (toDual ∘ f ∘ ofDual) hne hbdd


-- @@ L74-75 verbatim
lemma map_sSup (hne : s.Nonempty) (hbdd : BddAbove s) : f (sSup s) = ⨆ x : s, f x :=
  map_sInf (toDual ∘ f ∘ ofDual) hne hbdd


-- @@ L77-79 verbatim
lemma map_iInf (hbdd : BddBelow (range g)) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  erw [← sInf_range, ← sInf_range,
    map_sInf' f (Set.range_nonempty_iff_nonempty.mpr (by infer_instance)) hbdd, range_comp]


-- @@ L81-82 verbatim
lemma map_iSup (hbdd : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i) :=
  map_iInf (toDual ∘ f ∘ ofDual) hbdd


-- @@ L84-84 verbatim
end ContinuousOrderMap


-- @@ L86-86 verbatim
namespace ContinuousOrderMapBounded


-- @@ L88-88 verbatim
variable (f : α → β) {s : Set α}

-- @@ L89-89 verbatim
open ContinuousOrderMapBounded ContinuousOrderMap


-- @@ L91-91 verbatim
variable [ContinuousOrderMapBounded f]


-- @@ L93-98 verbatim
instance : ContinuousOrderMapBounded (toDual ∘ f ∘ ofDual) where
  monotone := monotone
  bounded_preimage_Iic := bounded_preimage_Ici (f := f)
  bounded_preimage_Ici := bounded_preimage_Iic (f := f)
  preimage_Ici_closed := preimage_Iic_closed (f := f)
  preimage_Iic_closed := preimage_Ici_closed (f := f)


-- @@ L100-109 verbatim
lemma bddBelow_iff : BddBelow (f '' s) ↔ BddBelow s := by
  refine ⟨fun | ⟨y, hy⟩ => ?_, fun | ⟨x, hx⟩ => ?_⟩
  · contrapose! hy
    simp only [BddBelow, Set.Nonempty, lowerBounds, mem_ofPred_eq, not_exists, not_forall,
      exists_prop, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hy ⊢
    obtain ⟨b, hb⟩ := bounded_preimage_Ici (f := f) y
    obtain ⟨x, hx⟩ := hy b
    exact ⟨x, hx.1, fun le => hx.2 (hb le)⟩
  · exact ⟨f x, by simpa [lowerBounds] using fun _ hs => monotone (hx hs)⟩


-- @@ L111-111 verbatim
lemma bddAbove_iff : BddAbove (f '' s) ↔ BddAbove s := bddBelow_iff (toDual ∘ f ∘ ofDual)


-- @@ L113-113 verbatim
end ContinuousOrderMapBounded
