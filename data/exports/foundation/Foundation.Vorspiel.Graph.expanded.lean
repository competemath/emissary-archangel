module

public import Mathlib.Logic.Function.Defs


-- @@ L5-6 verbatim
@[expose]
public section


-- @@ L8-8 verbatim
namespace Function


-- @@ L10-10 verbatim
variable {k} {σ α β γ δ ε : Sort*}


-- @@ L12-12 verbatim
def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)


-- @@ L14-14 verbatim
def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x


-- @@ L16-16 verbatim
def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂


-- @@ L18-18 verbatim
def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃


-- @@ L20-20 verbatim
def Graph₄ (f : α → β → γ → δ → σ) : σ → α → β → γ → δ → Prop := fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄


-- @@ L22-22 verbatim
def Graph₅ (f : α → β → γ → δ → ε → σ) : σ → α → β → γ → δ → ε → Prop := fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅


-- @@ L24-24 verbatim
lemma Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm


-- @@ L26-26 verbatim
lemma Graph.iff_left (f : α → σ) {y x} : f x = y ↔ Graph f y x := by simp [Graph, eq_comm]


-- @@ L28-28 verbatim
lemma Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]


-- @@ L30-30 verbatim
lemma Graph₂.eq {f : α → β → σ} {y x₁ x₂} (h : Graph₂ f y x₁ x₂) : f x₁ x₂ = y := h.symm


-- @@ L32-32 verbatim
lemma Graph₂.iff_left (f : α → β → σ) {y x₁ x₂} : f x₁ x₂ = y ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂, eq_comm]


-- @@ L34-34 verbatim
lemma Graph₂.iff_right (f : α → β → σ) {y x₁ x₂} : y = f x₁ x₂ ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂]


-- @@ L36-36 verbatim
lemma Graph₃.eq {f : α → β → γ → σ} {y x₁ x₂ x₃} (h : Graph₃ f y x₁ x₂ x₃) : f x₁ x₂ x₃ = y := h.symm


-- @@ L38-38 verbatim
lemma Graph₃.iff_left (f : α → β → γ → σ) {y x₁ x₂ x₃} : f x₁ x₂ x₃ = y ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃, eq_comm]


-- @@ L40-40 verbatim
lemma Graph₃.iff_right (f : α → β → γ → σ) {y x₁ x₂ x₃} : y = f x₁ x₂ x₃ ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃]


-- @@ L42-42 verbatim
end Function


-- @@ L44-44 verbatim
end
