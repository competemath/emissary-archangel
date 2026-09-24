module
public import Foundation.Logic.LogicSymbol


-- @@ L4-18 verbatim
/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions.
Also provides 𝓜 characterization of compactness.

## Main Definitions
* `FFL.Semantics`: The realization of 𝓜 formula.
* `FFL.Compact`: The semantic compactness of Foundation.

## Notation
* `𝓜 ⊧ φ`: a proposition that states `𝓜` satisfies `φ`.
* `𝓜 ⊧* T`: a proposition that states that `𝓜` satisfies each formulae in a set `T`.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace FFL


-- @@ L24-26 verbatim
/-- `Semantics M F` denotes semantics of formulae `F for models `M` -/
class Semantics (M : Type*) (F : outParam Type*) where
  Models : M → F → Prop


-- @@ L28-28 verbatim
variable {M : Type*} {F : Type*} [𝓢 : Semantics M F]


-- @@ L30-30 verbatim
namespace Semantics


-- @@ L32-32 verbatim
infix:45 " ⊧ " => Models


-- @@ L34-35 verbatim
/-- The negation of `𝓜 ⊧ φ` -/
abbrev NotModels (𝓜 : M) (φ : F) : Prop := ¬𝓜 ⊧ φ


-- @@ L37-37 verbatim
infix:45 " ⊭ " => NotModels


-- @@ L39-39 verbatim
/-! ### Tarski's truth definitions -/


-- @@ L41-41 verbatim
section


-- @@ L43-43 verbatim
variable [LogicalConnective F] [LogicalNeutral F] (M)


-- @@ L45-47 verbatim
/-- Tarski's truth definition for `⊤`. -/
protected class Top where
  models_verum (𝓜 : M) : 𝓜 ⊧ (⊤ : F)


-- @@ L49-51 verbatim
/-- Tarski's truth definition for `⊥`. -/
protected class Bot where
  models_falsum (𝓜 : M) : ¬𝓜 ⊧ (⊥ : F)


-- @@ L53-55 verbatim
/-- Tarski's truth definition for `⋏`. -/
protected class And where
  models_and {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋏ ψ ↔ 𝓜 ⊧ φ ∧ 𝓜 ⊧ ψ


-- @@ L57-59 verbatim
/-- Tarski's truth definition for `⋎`. -/
protected class Or where
  models_or {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋎ ψ ↔ 𝓜 ⊧ φ ∨ 𝓜 ⊧ ψ


-- @@ L61-63 verbatim
/-- Tarski's truth definition for `🡒`. -/
protected class Imp where
  models_imply {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ 🡒 ψ ↔ (𝓜 ⊧ φ → 𝓜 ⊧ ψ)


-- @@ L65-67 verbatim
/-- Tarski's truth definition for `∼`. -/
protected class Not where
  models_not {𝓜 : M} {φ : F} : 𝓜 ⊧ ∼φ ↔ ¬𝓜 ⊧ φ


-- @@ L69-77 verbatim
/-- Tarski's truth definitions. -/
class Tarski extends
  Semantics.Top M,
  Semantics.Bot M,
  Semantics.And M,
  Semantics.Or M,
  Semantics.Imp M,
  Semantics.Not M
  where


-- @@ L79-81 verbatim
attribute [simp, grind .]
  Top.models_verum
  Bot.models_falsum


-- @@ L83-87 verbatim
attribute [simp, grind =]
  Not.models_not
  And.models_and
  Or.models_or
  Imp.models_imply


-- @@ L89-89 verbatim
variable {M}


-- @@ L91-91 verbatim
variable [Tarski M]


-- @@ L93-93 verbatim
variable {𝓜 : M}


-- @@ L95-97 verbatim
@[simp] lemma models_iff {φ ψ : F} :
    𝓜 ⊧ φ 🡘 ψ ↔ (𝓜 ⊧ φ ↔ 𝓜 ⊧ ψ) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]


-- @@ L99-100 verbatim
@[simp] lemma models_list_conj {l : List F} :
    𝓜 ⊧ l.conj ↔ ∀ φ ∈ l, 𝓜 ⊧ φ := by induction l <;> simp [*]


-- @@ L102-103 verbatim
@[simp] lemma models_list_conj₂ {l : List F} :
    𝓜 ⊧ ⋀l ↔ ∀ φ ∈ l, 𝓜 ⊧ φ := by induction l using List.induction_with_singleton <;> simp [*]


-- @@ L105-105 verbatim
@[simp] lemma models_list_conj' {l : List α} {ι : α → F} : 𝓜 ⊧ l.conj' ι ↔ ∀ i ∈ l, 𝓜 ⊧ ι i := by simp [List.conj']


-- @@ L107-108 verbatim
@[simp] lemma models_finset_conj {s : Finset F} :
    𝓜 ⊧ s.conj ↔ ∀ φ ∈ s, 𝓜 ⊧ φ := by simp [Finset.conj]


-- @@ L110-110 verbatim
@[simp] lemma models_finset_conj' {s : Finset α} {ι : α → F} : 𝓜 ⊧ s.conj' ι ↔ ∀ i ∈ s, 𝓜 ⊧ ι i := by simp [Finset.conj']


-- @@ L112-113 verbatim
@[simp] lemma models_list_disj {l : List F} :
    𝓜 ⊧ l.disj ↔ ∃ φ ∈ l, 𝓜 ⊧ φ := by induction l <;> simp [*]


-- @@ L115-116 verbatim
@[simp] lemma models_list_disj₂ {l : List F} :
    𝓜 ⊧ ⋁l ↔ ∃ φ ∈ l, 𝓜 ⊧ φ := by induction l using List.induction_with_singleton <;> simp [*]


-- @@ L118-118 verbatim
@[simp] lemma models_list_disj' {l : List α} {ι : α → F} : 𝓜 ⊧ l.disj' ι ↔ ∃ i ∈ l, 𝓜 ⊧ ι i := by simp [List.disj']


-- @@ L120-121 verbatim
@[simp] lemma models_finset_disj {s : Finset F} :
    𝓜 ⊧ s.disj ↔ ∃ φ ∈ s, 𝓜 ⊧ φ := by simp [Finset.disj]


-- @@ L123-123 verbatim
@[simp] lemma models_finset_disj' {s : Finset α} {ι : α → F} : 𝓜 ⊧ s.disj' ι ↔ ∃ i ∈ s, 𝓜 ⊧ ι i := by simp [Finset.disj']


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
/-! ### A semantics and satisfiability over a set of formulas -/


-- @@ L129-131 verbatim
/-- `𝓜 ⊧* T` denotes `𝓜 ⊧ φ` for all `φ` in `T`. -/
class ModelsSet (𝓜 : M) (T : Set F) : Prop where
  models_set : ∀ ⦃φ⦄, φ ∈ T → Models 𝓜 φ


-- @@ L133-133 verbatim
infix:45 " ⊧* " => ModelsSet


-- @@ L135-135 verbatim
variable (M)


-- @@ L137-137 verbatim
def Valid (φ : F) : Prop := ∀ 𝓜 : M, 𝓜 ⊧ φ


-- @@ L139-139 verbatim
def Satisfiable (T : Set F) : Prop := ∃ 𝓜 : M, 𝓜 ⊧* T


-- @@ L141-142 verbatim
/-- A set of models satisfies set of formulae `T`. -/
def models (T : Set F) : Set M := {𝓜 | 𝓜 ⊧* T}


-- @@ L144-144 verbatim
variable {M}


-- @@ L146-147 verbatim
/-- A set of formulae satisfied by model `𝓜`. -/
def theory (𝓜 : M) : Set F := {φ | 𝓜 ⊧ φ}


-- @@ L149-150 verbatim
class Meaningful (𝓜 : M) : Prop where
  exists_unmodels : ∃ φ, 𝓜 ⊭ φ


-- @@ L152-160 verbatim
instance [LogicalNeutral F] [Semantics.Bot M] (𝓜 : M) : Meaningful 𝓜 := ⟨⟨⊥, by grind⟩⟩

lemma meaningful_iff {𝓜 : M} : Meaningful 𝓜 ↔ ∃ φ, 𝓜 ⊭ φ :=
  ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma not_meaningful_iff (𝓜 : M) : ¬Meaningful 𝓜 ↔ ∀ φ, 𝓜 ⊧ φ := by simp [meaningful_iff]

lemma modelsSet_iff {𝓜 : M} {T : Set F} : 𝓜 ⊧* T ↔ ∀ ⦃φ⦄, φ ∈ T → Models 𝓜 φ :=
  ⟨by rintro ⟨h⟩ φ hf; exact h hf, by intro h; exact ⟨h⟩⟩


-- @@ L162-162 verbatim
@[simp] lemma modelsTheory_theory (𝓜 : M) : 𝓜 ⊧* theory 𝓜 := ⟨by simp [theory]⟩


-- @@ L164-168 verbatim
@[simp] lemma theory_satisfiable (𝓜 : M) : Satisfiable M (theory 𝓜) := ⟨𝓜, by simp⟩

lemma not_satisfiable_finset [LogicalConnective F] [LogicalNeutral F] [Tarski M] [DecidableEq F] (t : Finset F) :
    ¬Satisfiable M (t : Set F) ↔ Valid M (t.image (∼·)).disj := by
  simp [Satisfiable, modelsSet_iff, Valid];


-- @@ L170-172 verbatim
@[simp] lemma satisfiable_conj₂ [LogicalConnective F] [LogicalNeutral F] [Tarski M] [DecidableEq F] (l : List F) :
    Satisfiable M {⋀l} ↔ Satisfiable M {φ | φ ∈ l} := by
  simp [Satisfiable, modelsSet_iff]


-- @@ L174-180 verbatim
@[simp] lemma satisfiable_fconj [LogicalConnective F] [LogicalNeutral F] [Tarski M] [DecidableEq F] (s : Finset F) :
    Satisfiable M {s.conj} ↔ Satisfiable M {φ | φ ∈ s} := by
  simp [Satisfiable, modelsSet_iff]

lemma satisfiableSet_iff_models_nonempty {T : Set F} :
    Satisfiable M T ↔ (models M T).Nonempty :=
  ⟨by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩, by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩⟩


-- @@ L182-191 verbatim
namespace ModelsSet

lemma models {T : Set F} (𝓜 : M) [𝓜 ⊧* T] (hf : φ ∈ T) : 𝓜 ⊧ φ :=
  models_set hf

lemma of_subset {T U : Set F} {𝓜 : M} (h : 𝓜 ⊧* U) (ss : T ⊆ U) : 𝓜 ⊧* T :=
  ⟨fun _ hf => h.models_set (ss hf)⟩

lemma of_subset' {T U : Set F} {𝓜 : M} [𝓜 ⊧* U] (ss : T ⊆ U) : 𝓜 ⊧* T :=
  of_subset (𝓜 := 𝓜) inferInstance ss


-- @@ L193-193 verbatim
instance empty' (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨by simp⟩


-- @@ L195-195 verbatim
@[simp] lemma empty (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨by simp⟩


-- @@ L197-198 verbatim
@[simp] lemma singleton_iff {φ : F} {𝓜 : M} :
    𝓜 ⊧* {φ} ↔ 𝓜 ⊧ φ := by simp [modelsSet_iff]


-- @@ L200-202 verbatim
@[simp] lemma insert_iff {T : Set F} {φ : F} {𝓜 : M} :
    𝓜 ⊧* insert φ T ↔ 𝓜 ⊧ φ ∧ 𝓜 ⊧* T := by
  simp [modelsSet_iff]


-- @@ L204-212 verbatim
@[simp] lemma union_iff {T U : Set F} {𝓜 : M} :
    𝓜 ⊧* T ∪ U ↔ 𝓜 ⊧* T ∧ 𝓜 ⊧* U := by
  simp only [modelsSet_iff, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun _ hf => h (Or.inl hf), fun _ hf => h (Or.inr hf)⟩
  · rintro ⟨h₁, h₂⟩ φ (h | h)
    · exact h₁ h
    · exact h₂ h


-- @@ L214-215 verbatim
@[simp] lemma image_iff {ι} {φ : ι → F} {A : Set ι} {𝓜 : M} :
    𝓜 ⊧* φ '' A ↔ ∀ i ∈ A, 𝓜 ⊧ φ i := by simp [modelsSet_iff]


-- @@ L217-218 verbatim
@[simp] lemma range_iff {ι} {φ : ι → F} {𝓜 : M} :
    𝓜 ⊧* Set.range φ ↔ ∀ i, 𝓜 ⊧ φ i := by simp [modelsSet_iff]


-- @@ L220-223 verbatim
@[simp] lemma setOf_iff {P : F → Prop} {𝓜 : M} :
    𝓜 ⊧* Set.ofPred P ↔ ∀ φ, P φ → 𝓜 ⊧ φ := by
  rw [modelsSet_iff]
  exact Iff.rfl


-- @@ L225-231 verbatim
end ModelsSet

lemma valid_neg_iff [LogicalConnective F] [LogicalNeutral F] [Tarski M] (φ : F) : Valid M (∼φ) ↔ ¬Satisfiable M {φ} := by
  simp [Valid, Satisfiable]

lemma Satisfiable.of_subset {T U : Set F} (h : Satisfiable M U) (ss : T ⊆ U) : Satisfiable M T := by
  rcases h with ⟨𝓜, h⟩; exact ⟨𝓜, ModelsSet.of_subset h ss⟩


-- @@ L233-233 verbatim
variable (M)


-- @@ L235-235 verbatim
instance : Semantics (Set M) F := ⟨fun s φ ↦ ∀ ⦃𝓜⦄, 𝓜 ∈ s → 𝓜 ⊧ φ⟩


-- @@ L237-237 verbatim
@[simp] lemma empty_models (φ : F) : (∅ : Set M) ⊧ φ := by rintro h; simp


-- @@ L239-239 verbatim
/-! Logical consequence -/


-- @@ L241-244 verbatim
/-- The logical conseqence. -/
def Consequence (T : Set F) (φ : F) : Prop := models M T ⊧ φ

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)

-- @@ L245-245 verbatim
notation T:45 " ⊨[" M "] " φ:46 => Consequence M T φ


-- @@ L247-249 verbatim
variable {M}

lemma set_models_iff {s : Set M} : s ⊧ φ ↔ ∀ 𝓜 ∈ s, 𝓜 ⊧ φ := iff_of_eq rfl


-- @@ L251-281 verbatim
instance [LogicalNeutral F] [Semantics.Top M] : Semantics.Top (Set M) := ⟨fun s ↦ by simp [set_models_iff]⟩

lemma set_meaningful_iff_nonempty [∀ 𝓜 : M, Meaningful 𝓜] {s : Set M} : Meaningful s ↔ s.Nonempty := by
  constructor;
  . rintro ⟨φ, hf⟩;
    by_contra A;
    rcases Set.not_nonempty_iff_eq_empty.mp A; simp [NotModels] at hf;
  . rintro ⟨𝓜, h𝓜⟩;
    rcases Meaningful.exists_unmodels (self := by tauto) with ⟨φ, hf⟩;
    exact ⟨φ, by simpa [NotModels, set_models_iff] using ⟨𝓜, h𝓜, hf⟩⟩

lemma meaningful_iff_satisfiableSet [∀ 𝓜 : M, Meaningful 𝓜] : Satisfiable M T ↔ Meaningful (models M T) := by
  simp [set_meaningful_iff_nonempty, satisfiableSet_iff_models_nonempty]

lemma consequence_iff {T : Set F} {φ} : T ⊨[M] φ ↔ ∀ {𝓜 : M}, 𝓜 ⊧* T → 𝓜 ⊧ φ := iff_of_eq rfl

lemma consequence_iff' {T : Set F} {φ : F} : T ⊨[M] φ ↔ (∀ (𝓜 : M) [𝓜 ⊧* T], 𝓜 ⊧ φ) :=
  ⟨fun h _ _ => consequence_iff.mp h inferInstance, fun H 𝓜 hs => @H 𝓜 hs⟩

lemma consequence_iff_not_satisfiable [LogicalConnective F] [LogicalNeutral F] [Tarski M] {φ : F} :
    T ⊨[M] φ ↔ ¬Satisfiable M (insert (∼φ) T) := by
  suffices (∀ {𝓜 : M}, 𝓜 ⊧* T → 𝓜 ⊧ φ) ↔ ∀ (x : M), x ⊭ φ → ¬x ⊧* T by
    simpa [consequence_iff, Satisfiable]
  constructor
  · intro h 𝓜 hf hT; have : 𝓜 ⊧ φ := h hT; contradiction
  · intro h 𝓜; contrapose; exact h 𝓜

lemma weakening {T U : Set F} {φ} (h : T ⊨[M] φ) (ss : T ⊆ U) : U ⊨[M] φ :=
  consequence_iff.mpr fun hs => consequence_iff.mp h (ModelsSet.of_subset hs ss)

lemma of_mem {T : Set F} {φ} (h : φ ∈ T) : T ⊨[M] φ := fun _ hs => hs.models_set h


-- @@ L283-283 verbatim
end Semantics


-- @@ L285-285 verbatim
/-! Compactness -/


-- @@ L287-288 verbatim
/-- A cumulative sequence of sets. -/
def Cumulative (T : ℕ → Set F) : Prop := ∀ s, T s ⊆ T (s + 1)


-- @@ L290-315 verbatim
namespace Cumulative

lemma subset_of_le {T : ℕ → Set F} (H : Cumulative T)
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : T s₁ ⊆ T s₂ := by
  suffices ∀ s d, T s ⊆ T (s + d) by
    simpa [Nat.add_sub_of_le h] using this s₁ (s₂ - s₁)
  intro s d
  induction' d with d ih
  · simp
  · simpa only [Nat.add_succ, add_zero] using subset_trans ih (H (s + d))

lemma finset_mem {T : ℕ → Set F}
    (H : Cumulative T) {u : Finset F} (hu : ↑u ⊆ ⋃ s, T s) : ∃ s, ↑u ⊆ T s := by
  have := Classical.decEq
  induction u using Finset.induction
  case empty => exact ⟨0, by simp⟩
  case insert φ u _ ih =>
    have hu : insert φ ↑u ⊆ ⋃ s, T s := by simpa using hu
    have : ∃ s, ↑u ⊆ T s := ih (subset_trans (Set.subset_insert _ _) hu)
    rcases this with ⟨s, hs⟩
    have : ∃ s', φ ∈ T s' := by simpa using (Set.insert_subset_iff.mp hu).1
    rcases this with ⟨s', hs'⟩
    exact ⟨max s s', by
      simpa using Set.insert_subset
        (subset_of_le H (Nat.le_max_right s s') hs')
        (subset_trans hs (subset_of_le H $ Nat.le_max_left s s'))⟩


-- @@ L317-317 verbatim
end Cumulative


-- @@ L319-319 verbatim
variable (M)


-- @@ L321-324 verbatim
/-- A `Semantics M F` is compact if, for any set of formulas, the satisfiability of the set is equivalent to the satisfiability of every finite subset of it.  -/
class Compact : Prop where
  compact {T : Set F} :
    Semantics.Satisfiable M T ↔ (∀ u : Finset F, ↑u ⊆ T → Semantics.Satisfiable M (u : Set F))


-- @@ L326-326 verbatim
variable {M}


-- @@ L328-328 verbatim
namespace Compact


-- @@ L330-330 verbatim
variable [Compact M]


-- @@ L332-357 verbatim
variable {𝓜 : M}

lemma conseq_compact [LogicalConnective F] [LogicalNeutral F] [Semantics.Tarski M] [DecidableEq F] {φ : F} :
    T ⊨[M] φ ↔ ∃ u : Finset F, ↑u ⊆ T ∧ u ⊨[M] φ := by
  suffices
    (∃ x : Finset F, ↑x ⊆ insert (∼φ) T ∧ ¬Semantics.Satisfiable M ↑x) ↔
    ∃ u : Finset F, ↑u ⊆ T ∧ ¬Semantics.Satisfiable M (insert (∼φ) ↑u) by
    simpa [Semantics.consequence_iff_not_satisfiable, compact (T := insert (∼φ) T)]
  constructor
  · intro ⟨u, ss, hu⟩
    refine ⟨Finset.erase u (∼φ), by simp [ss],?_⟩
    simp only [Finset.coe_erase, Set.insert_sdiff_singleton]
    intro h; exact hu (Semantics.Satisfiable.of_subset h (by simp))
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (∼φ) u,
      by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

lemma compact_cumulative {T : ℕ → Set F} (hT : Cumulative T) :
    Semantics.Satisfiable M (⋃ s, T s) ↔ ∀ s, Semantics.Satisfiable M (T s) :=
  ⟨by intro H s
      exact H.of_subset (Set.subset_iUnion T s),
   by intro H
      apply compact.mpr
      intro u hu
      rcases hT.finset_mem hu with ⟨s, hs⟩
      exact (H s).of_subset hs ⟩


-- @@ L359-359 verbatim
end Compact


-- @@ L361-361 verbatim
end FFL


-- @@ L363-363 verbatim
end
