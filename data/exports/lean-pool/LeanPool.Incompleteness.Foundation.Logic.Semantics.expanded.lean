/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L12-26 verbatim
/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions.
Also provides 𝓜 characterization of compactness.

## Main Definitions
* `LO.Semantics`: The realization of 𝓜 formula.
* `LO.Compact`: The semantic compactness of Foundation.

## Notation
* `𝓜 ⊧ φ`: a proposition that states `𝓜` satisfies `φ`.
* `𝓜 ⊧* T`: a proposition that states that `𝓜` satisfies each formulae in a set `T`.

-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace LO


-- @@ L32-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Semantics (F : outParam Type*) (M : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Realize : M → F → Prop


-- @@ L37-37 verbatim
variable {M : Type*} {F : Type*} [𝓢 : Semantics F M]


-- @@ L39-39 verbatim
namespace Semantics


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ " => Realize


-- @@ L44-44 verbatim
section «lp_section_1»


-- @@ L46-46 verbatim
variable [LogicalConnective F] (M)


-- @@ L48-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Top where
  realize_top (𝓜 : M) : Realize 𝓜 (⊤ : F)


-- @@ L52-54 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Bot where
  realize_bot (𝓜 : M) : ¬Realize 𝓜 (⊥ : F)


-- @@ L56-58 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class And where
  realize_and {𝓜 : M} {φ ψ : F} : Realize 𝓜 (Wedge.wedge φ ψ) ↔ Realize 𝓜 φ ∧ Realize 𝓜 ψ


-- @@ L60-62 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Or where
  realize_or {𝓜 : M} {φ ψ : F} : Realize 𝓜 (Vee.vee φ ψ) ↔ Realize 𝓜 φ ∨ Realize 𝓜 ψ


-- @@ L64-66 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Imp where
  realize_imp {𝓜 : M} {φ ψ : F} : Realize 𝓜 (Arrow.arrow φ ψ) ↔ (Realize 𝓜 φ → Realize 𝓜 ψ)


-- @@ L68-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Not where
  realize_not {𝓜 : M} {φ : F} : Realize 𝓜 (Tilde.tilde φ) ↔ ¬Realize 𝓜 φ


-- @@ L72-80 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Tarski extends
  Semantics.Top M,
  Semantics.Bot M,
  Semantics.And M,
  Semantics.Or M,
  Semantics.Imp M,
  Semantics.Not M
  where



-- @@ L83-89 verbatim
attribute [simp]
  Top.realize_top
  Bot.realize_bot
  Not.realize_not
  And.realize_and
  Or.realize_or
  Imp.realize_imp


-- @@ L91-91 verbatim
variable {M}


-- @@ L93-93 verbatim
variable [Tarski M]


-- @@ L95-95 verbatim
variable {𝓜 : M}


-- @@ L97-98 expanded
@[simp]
lemma realize_iff {φ ψ : F} :
    Realize 𝓜 (LogicalConnective.iff φ ψ) ↔ ((Realize 𝓜 φ) ↔ (Realize 𝓜 ψ)) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]


-- @@ L100-101 expanded
@[simp]
lemma realize_list_conj {l : List F} : Realize 𝓜 l.conj ↔ ∀ φ ∈ l, Realize 𝓜 φ := by
  induction l <;> simp [*]


-- @@ L103-104 expanded
@[simp]
lemma realize_finset_conj {s : Finset F} : Realize 𝓜 s.conj ↔ ∀ φ ∈ s, Realize 𝓜 φ := by
  simp [Finset.conj]


-- @@ L106-107 expanded
@[simp]
lemma realize_list_disj {l : List F} : Realize 𝓜 l.disj ↔ ∃ φ ∈ l, Realize 𝓜 φ := by
  induction l <;> simp [*]


-- @@ L109-110 expanded
@[simp]
lemma realize_finset_disj {s : Finset F} : Realize 𝓜 s.disj ↔ ∃ φ ∈ s, Realize 𝓜 φ := by
  simp [Finset.disj]


-- @@ L112-112 verbatim
end «lp_section_1»


-- @@ L114-116 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class RealizeSet (𝓜 : M) (T : Set F) : Prop where
  all_realize : ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f


-- @@ L118-119 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧* " => RealizeSet


-- @@ L121-121 verbatim
variable (M)


-- @@ L123-124 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Valid (f : F) : Prop :=
  ∀ 𝓜 : M, Realize 𝓜 f


-- @@ L126-127 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Satisfiable (T : Set F) : Prop :=
  ∃ 𝓜 : M, RealizeSet 𝓜 T


-- @@ L129-130 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def models (T : Set F) : Set M :=
  {𝓜 | RealizeSet 𝓜 T}


-- @@ L132-132 verbatim
variable {M}


-- @@ L134-135 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def theory (𝓜 : M) : Set F :=
  {φ | Realize 𝓜 φ}


-- @@ L137-139 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Meaningful (𝓜 : M) : Prop where
  exists_unrealize : ∃ f, ¬Realize 𝓜 f


-- @@ L141-141 verbatim
instance [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) : Meaningful 𝓜 := ⟨⟨⊥, by simp⟩⟩


-- @@ L143-143 expanded
lemma meaningful_iff {𝓜 : M} : Meaningful 𝓜 ↔ ∃ f, ¬Realize 𝓜 f :=
  ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩


-- @@ L145-145 expanded
lemma not_meaningful_iff (𝓜 : M) : ¬Meaningful 𝓜 ↔ ∀ f, Realize 𝓜 f := by simp [meaningful_iff]


-- @@ L147-148 expanded
lemma realizeSet_iff {𝓜 : M} {T : Set F} : RealizeSet 𝓜 T ↔ ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f :=
  ⟨by rintro ⟨h⟩ f hf; exact h hf, by intro h; exact ⟨h⟩⟩


-- @@ L150-152 expanded
lemma not_satisfiable_finset [LogicalConnective F] [Tarski M] [DecidableEq F] (t : Finset F) :
    ¬Satisfiable M (t : Set F) ↔ Valid M (t.image (Tilde.tilde ·)).disj := by
  simp [Satisfiable, realizeSet_iff, Valid]


-- @@ L154-155 verbatim
lemma satisfiableSet_iff_models_nonempty {T : Set F} : Satisfiable M T ↔ (models M T).Nonempty :=
  ⟨by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩, by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩⟩


-- @@ L157-157 verbatim
namespace RealizeSet


-- @@ L159-159 expanded
lemma realize {T : Set F} (𝓜 : M) [RealizeSet 𝓜 T] (hf : f ∈ T) : Realize 𝓜 f :=
  all_realize hf


-- @@ L161-162 expanded
lemma of_subset {T U : Set F} {𝓜 : M} (h : RealizeSet 𝓜 U) (ss : T ⊆ U) : RealizeSet 𝓜 T :=
  ⟨fun _ hf => h.all_realize (ss hf)⟩


-- @@ L164-165 expanded
lemma of_subset' {T U : Set F} {𝓜 : M} [RealizeSet 𝓜 U] (ss : T ⊆ U) : RealizeSet 𝓜 T :=
  of_subset (𝓜 := 𝓜) inferInstance ss


-- @@ L167-167 expanded
instance empty' (𝓜 : M) : RealizeSet 𝓜 (∅ : Set F) :=
  ⟨by simp⟩


-- @@ L169-169 expanded
@[simp]
lemma empty (𝓜 : M) : RealizeSet 𝓜 (∅ : Set F) :=
  ⟨by simp⟩


-- @@ L171-171 expanded
@[simp]
lemma singleton_iff {f : F} {𝓜 : M} : RealizeSet 𝓜 { f } ↔ Realize 𝓜 f := by simp [realizeSet_iff]


-- @@ L173-174 expanded
@[simp]
lemma insert_iff {T : Set F} {f : F} {𝓜 : M} :
    RealizeSet 𝓜 (insert f T) ↔ Realize 𝓜 f ∧ RealizeSet 𝓜 T := by simp [realizeSet_iff]


-- @@ L176-177 expanded
@[simp]
lemma union_iff {T U : Set F} {𝓜 : M} : RealizeSet 𝓜 (T ∪ U) ↔ RealizeSet 𝓜 T ∧ RealizeSet 𝓜 U := by
  simp only [realizeSet_iff, Set.mem_union, or_imp, forall_and]


-- @@ L179-180 expanded
@[simp]
lemma image_iff {ι} {f : ι → F} {A : Set ι} {𝓜 : M} :
    RealizeSet 𝓜 (f '' A) ↔ ∀ i ∈ A, Realize 𝓜 (f i) := by simp [realizeSet_iff]


-- @@ L182-183 expanded
@[simp]
lemma range_iff {ι} {f : ι → F} {𝓜 : M} : RealizeSet 𝓜 (Set.range f) ↔ ∀ i, Realize 𝓜 (f i) := by
  simp [realizeSet_iff]


-- @@ L185-186 expanded
@[simp]
lemma setOf_iff {P : F → Prop} {𝓜 : M} : RealizeSet 𝓜 (Set.ofPred P) ↔ ∀ f, P f → Realize 𝓜 f := by
  simp [realizeSet_iff]


-- @@ L188-188 verbatim
end RealizeSet


-- @@ L190-191 expanded
lemma valid_neg_iff [LogicalConnective F] [Tarski M] (f : F) :
    Valid M (Tilde.tilde f) ↔ ¬Satisfiable M { f } := by simp [Valid, Satisfiable]


-- @@ L193-194 verbatim
lemma _root_.LO.Semantics.Satisfiable.of_subset {T U : Set F} (h : Satisfiable M U) (ss : T ⊆ U) :
    Satisfiable M T := by rcases h with ⟨𝓜, h⟩; exact ⟨𝓜, RealizeSet.of_subset h ss⟩


-- @@ L196-196 verbatim
variable (M)


-- @@ L198-198 expanded
instance : Semantics F (Set M) :=
  ⟨fun s f ↦ ∀ ⦃𝓜⦄, 𝓜 ∈ s → Realize 𝓜 f⟩


-- @@ L200-200 expanded
@[simp]
lemma empty_models (f : F) : Realize (∅ : Set M) f := by rintro h; simp


-- @@ L202-205 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Consequence (T : Set F) (f : F) : Prop :=
  Realize (models M T) f


-- @@ L206-207 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation T:45 " ⊨[" M "] " φ:46 => Consequence M T φ


-- @@ L209-209 verbatim
variable {M}


-- @@ L211-211 expanded
lemma set_models_iff {s : Set M} : Realize s f ↔ ∀ 𝓜 ∈ s, Realize 𝓜 f :=
  iff_of_eq rfl


-- @@ L213-214 verbatim
instance [LogicalConnective F] [Semantics.Top M] : Semantics.Top (Set M) :=
  ⟨fun s ↦ by simp [set_models_iff]⟩


-- @@ L216-222 verbatim
lemma set_meaningful_iff_nonempty [∀ 𝓜 : M, Meaningful 𝓜] {s : Set M} :
    Meaningful s ↔ s.Nonempty :=
  ⟨by rintro ⟨f, hf⟩; by_contra A; rcases Set.not_nonempty_iff_eq_empty.mp A; simp at hf,
   by rintro ⟨𝓜, h𝓜⟩
      have hMeaningful : Meaningful (F := F) 𝓜 := inferInstance
      rcases hMeaningful.exists_unrealize with ⟨f, hf⟩
      exact ⟨f, fun hs => hf (set_models_iff.mp hs 𝓜 h𝓜)⟩⟩


-- @@ L224-226 verbatim
lemma meaningful_iff_satisfiableSet [∀ 𝓜 : M, Meaningful 𝓜] :
    Satisfiable M T ↔ Meaningful (models M T) := by
  simp [set_meaningful_iff_nonempty, satisfiableSet_iff_models_nonempty]


-- @@ L228-228 expanded
lemma consequence_iff {T : Set F} {f} :
    Consequence M T f ↔ ∀ {𝓜 : M}, RealizeSet 𝓜 T → Realize 𝓜 f :=
  iff_of_eq rfl


-- @@ L230-231 expanded
lemma consequence_iff' {T : Set F} {f : F} :
    Consequence M T f ↔ (∀ (𝓜 : M) [RealizeSet 𝓜 T], Realize 𝓜 f) :=
  ⟨fun h _ _ => consequence_iff.mp h inferInstance, fun H 𝓜 hs => @H 𝓜 hs⟩


-- @@ L233-245 expanded
lemma consequence_iff_not_satisfiable [LogicalConnective F] [Tarski M] {f : F} :
    Consequence M T f ↔ ¬Satisfiable M (insert (Tilde.tilde f) T) :=
  by
  rw [consequence_iff]
  unfold Satisfiable
  constructor
  · intro h hs
    rcases hs with ⟨𝓜, hs⟩
    have hparts : Realize 𝓜 (Tilde.tilde f) ∧ RealizeSet 𝓜 T := by simpa using hs
    have : Realize 𝓜 f := h hparts.2
    exact (Semantics.Not.realize_not.mp hparts.1) this
  · intro h 𝓜 hT
    by_contra hf
    exact h ⟨𝓜, by exact RealizeSet.insert_iff.mpr ⟨by simpa using hf, hT⟩⟩


-- @@ L247-248 expanded
lemma weakening {T U : Set F} {f} (h : Consequence M T f) (ss : T ⊆ U) : Consequence M U f :=
  consequence_iff.mpr fun hs => consequence_iff.mp h (RealizeSet.of_subset hs ss)


-- @@ L250-250 expanded
lemma of_mem {T : Set F} {f} (h : f ∈ T) : Consequence M T f := fun _ hs => hs.all_realize h


-- @@ L252-252 verbatim
end Semantics


-- @@ L254-255 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Cumulative (T : ℕ → Set F) : Prop := ∀ s, T s ⊆ T (s + 1)


-- @@ L257-257 verbatim
namespace Cumulative


-- @@ L259-265 verbatim
lemma subset_of_le {T : ℕ → Set F} (H : Cumulative T)
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : T s₁ ⊆ T s₂ := by
  suffices ∀ s d, T s ⊆ T (s + d) by simpa[Nat.add_sub_of_le h] using this s₁ (s₂ - s₁)
  intro s d
  induction d with
  | zero => simp
  | succ d ih => simpa only [Nat.add_succ, add_zero] using subset_trans ih (H (s + d))


-- @@ L267-281 verbatim
lemma finset_mem {T : ℕ → Set F}
    (H : Cumulative T) {u : Finset F} (hu : ↑u ⊆ ⋃ s, T s) : ∃ s, ↑u ⊆ T s := by
  have := Classical.decEq
  induction u using Finset.induction
  case empty => exact ⟨0, by simp⟩
  case insert f u _ ih =>
    simp only [Finset.coe_insert] at hu
    have : ∃ s, ↑u ⊆ T s := ih (subset_trans (Set.subset_insert _ _) hu)
    rcases this with ⟨s, hs⟩
    have : ∃ s', f ∈ T s' := by simpa using (Set.insert_subset_iff.mp hu).1
    rcases this with ⟨s', hs'⟩
    exact ⟨max s s', by
      simpa only [Finset.coe_insert] using Set.insert_subset
        (subset_of_le H (Nat.le_max_right s s') hs')
        (subset_trans hs (subset_of_le H <| Nat.le_max_left s s'))⟩


-- @@ L283-283 verbatim
end Cumulative


-- @@ L285-285 verbatim
variable (M)


-- @@ L287-290 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Compact : Prop where
  compact {T : Set F} :
    Semantics.Satisfiable M T ↔ (∀ u : Finset F, ↑u ⊆ T → Semantics.Satisfiable M (u : Set F))


-- @@ L292-292 verbatim
variable {M}


-- @@ L294-294 verbatim
namespace Compact


-- @@ L296-296 verbatim
variable [Compact M]


-- @@ L298-298 verbatim
variable {𝓜 : M}


-- @@ L300-314 expanded
lemma conseq_compact [LogicalConnective F] [Semantics.Tarski M] {f : F} :
    Consequence M T f ↔ ∃ u : Finset F, ↑u ⊆ T ∧ Consequence M u f := by
  classical
  simp only [Semantics.consequence_iff_not_satisfiable, compact (T := insert (Tilde.tilde f) T),
    not_forall]
  constructor
  · intro ⟨u, ss, hu⟩
    exact
      ⟨Finset.erase u (Tilde.tilde f), by simp [ss],
        by
        simp only [Finset.coe_erase, Set.insert_sdiff_singleton]
        intro h
        exact hu (Semantics.Satisfiable.of_subset h (by simp))⟩
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (Tilde.tilde f) u, by simpa using Set.insert_subset_insert ss, by simpa using hu⟩


-- @@ L316-324 verbatim
lemma compact_cumulative {T : ℕ → Set F} (hT : Cumulative T) :
    Semantics.Satisfiable M (⋃ s, T s) ↔ ∀ s, Semantics.Satisfiable M (T s) :=
  ⟨by intro H s
      exact H.of_subset (Set.subset_iUnion T s),
   by intro H
      apply compact.mpr
      intro u hu
      rcases hT.finset_mem hu with ⟨s, hs⟩
      exact (H s).of_subset hs ⟩


-- @@ L326-326 verbatim
end Compact


-- @@ L328-328 verbatim
end LO
