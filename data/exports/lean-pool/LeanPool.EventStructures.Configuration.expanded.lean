/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/
module

public import LeanPool.EventStructures.Basic
public import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Attr


-- @@ L12-19 verbatim
/-!
# Configurations

A configuration of an event structure is a conflict-free, downward-closed set of
events. This module defines configurations (and their finite variant), the
enabling relation between a configuration and an event, and proves that enabling
an event extends a configuration.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EventStructures


-- @@ L25-25 verbatim
variable (es : EventStructure)


-- @@ L27-30 verbatim
/-- A set of events is a configuration if it is conflict-free and downward closed. -/
@[simp] def isConf (X : Set es.Event) : Prop :=
  (∀ {e₁ e₂}, e₁ ∈ X → e₂ ∈ X → ¬ es.conflict e₁ e₂) ∧
  (∀ {e e'}, e ∈ X → e' ≤ e → e' ∈ X)


-- @@ L32-33 verbatim
/-- Type of all configurations of an event structure. -/
def Conf : Type := {X : Set es.Event // isConf es X}


-- @@ L35-36 verbatim
/-- Type of all finite configurations of an event structure. -/
def FinConf : Type := {X : Finset es.Event // isConf es (X : Set es.Event)}


-- @@ L38-38 verbatim
namespace Configuration


-- @@ L40-47 verbatim
/-- A configuration c enables an event e if e is fresh (not already in c),
    e is consistent with all events in c, and the past of e is contained in c.
    Freshness rules out self-loop edges in the configuration graph. -/
def enables (c : Set es.Event) (e : es.Event) : Prop :=
  isConf es c ∧
  e ∉ c ∧
  (∀ e' ∈ c, es.consistent e e') ∧
  es.past e ⊆ c


-- @@ L49-50 verbatim
/-- Notation for the enabling relation. -/
local infix:50 " ⊢ " => enables es


-- @@ L52-54 verbatim
/-- An enabled event is not already in the configuration. -/
lemma enables_not_mem {c : Set es.Event} {e : es.Event} (h : c ⊢ e) : e ∉ c :=
  h.2.1


-- @@ L56-82 verbatim
/-- If a configuration c enables an event e, then c ∪ {e} is also a configuration. -/
lemma enables_extension {c : Set es.Event} {e : es.Event} (h : c ⊢ e) :
    isConf es (c ∪ {e}) := by
  obtain ⟨⟨hConflictFree, hDownClosed⟩, -, hConsistent, hPast⟩ := h
  constructor
  · -- Conflict-free
    intro e₁ e₂ h₁ h₂
    obtain h₁ | h₁ := h₁
    · obtain h₂ | h₂ := h₂
      · exact hConflictFree h₁ h₂
      · rw [Set.mem_singleton_iff] at h₂
        exact h₂ ▸ fun hConf => hConsistent e₁ h₁ (es.conflict_symm hConf)
    · rw [Set.mem_singleton_iff] at h₁
      obtain h₂ | h₂ := h₂
      · exact h₁ ▸ fun hConf => hConsistent e₂ h₂ hConf
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₁, h₂]
        exact es.conflict_irrefl e
  · -- Downward closed
    intro e' e'' h' h''
    obtain h' | h' := h'
    · exact Set.mem_union_left _ (hDownClosed h' h'')
    · rw [Set.mem_singleton_iff] at h'
      subst h'
      rcases lt_or_eq_of_le h'' with hlt | rfl
      · exact Set.mem_union_left _ (hPast hlt)
      · exact Set.mem_union_right _ rfl


-- @@ L84-84 verbatim
end Configuration


-- @@ L86-86 verbatim
end EventStructures
