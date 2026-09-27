/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Aesop.BuiltinRules
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike


-- @@ L14-14 verbatim
/-! # Graph -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace Function


-- @@ L21-21 verbatim
variable {σ α β : Sort*}


-- @@ L23-24 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)


-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x


-- @@ L29-30 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂


-- @@ L32-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃


-- @@ L35-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph₄ (f : α → β → γ → δ → σ) :
    σ → α → β → γ → δ → Prop :=
  fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄


-- @@ L40-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Graph₅ (f : α → β → γ → δ → ε → σ) :
    σ → α → β → γ → δ → ε → Prop :=
  fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅


-- @@ L45-45 verbatim
lemma _root_.Function.Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm


-- @@ L47-48 verbatim
lemma _root_.Function.Graph.iff_left (f : α → σ) {y x} :
    f x = y ↔ Graph f y x := by simp [Graph, eq_comm]


-- @@ L50-50 verbatim
lemma _root_.Function.Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]


-- @@ L52-54 verbatim
lemma _root_.Function.Graph₂.eq {f : α → β → σ} {y x₁ x₂} (h : Graph₂ f y x₁ x₂) :
    f x₁ x₂ = y :=
  h.symm


-- @@ L56-57 verbatim
lemma _root_.Function.Graph₂.iff_left (f : α → β → σ) {y x₁ x₂} :
    f x₁ x₂ = y ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂, eq_comm]


-- @@ L59-60 verbatim
lemma _root_.Function.Graph₂.iff_right (f : α → β → σ) {y x₁ x₂} :
    y = f x₁ x₂ ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂]


-- @@ L62-64 verbatim
lemma _root_.Function.Graph₃.eq {f : α → β → γ → σ} {y x₁ x₂ x₃} (h : Graph₃ f y x₁ x₂ x₃) :
    f x₁ x₂ x₃ = y :=
  h.symm


-- @@ L66-67 verbatim
lemma _root_.Function.Graph₃.iff_left (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    f x₁ x₂ x₃ = y ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃, eq_comm]


-- @@ L69-70 verbatim
lemma _root_.Function.Graph₃.iff_right (f : α → β → γ → σ) {y x₁ x₂ x₃} :
    y = f x₁ x₂ x₃ ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃]


-- @@ L72-72 verbatim
end Function
