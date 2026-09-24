module

public import Foundation.Propositional.Hilbert.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-9 verbatim
/-!
  # Dialectica-like realizableation of intuitionistic propositional logic
-/


-- @@ L11-11 verbatim
namespace FFL.Propositional.Dialectica


-- @@ L13-13 verbatim
open Formula


-- @@ L15-17 verbatim
inductive Player
  | eloise : Player
  | abelard : Player


-- @@ L19-19 verbatim
notation "ℰ" => Player.eloise

-- @@ L20-20 verbatim
notation "𝒜" => Player.abelard


-- @@ L22-32 verbatim
abbrev Argument : Player → Formula α → Type
  | ℰ,       ⊥ => Unit
  | 𝒜,       ⊥ => Unit
  | ℰ, .atom _ => Unit
  | 𝒜, .atom _ => Unit
  | ℰ,   φ ⋏ ψ => Argument ℰ φ × Argument ℰ ψ
  | 𝒜,   φ ⋏ ψ => Argument 𝒜 φ ⊕ Argument 𝒜 ψ
  | ℰ,   φ ⋎ ψ => Argument ℰ φ ⊕ Argument ℰ ψ
  | 𝒜,   φ ⋎ ψ => Argument 𝒜 φ × Argument 𝒜 ψ
  | ℰ,   φ 🡒 ψ => (Argument ℰ φ → Argument ℰ ψ) × (Argument ℰ φ → Argument 𝒜 ψ → Argument 𝒜 φ)
  | 𝒜,   φ 🡒 ψ => Argument ℰ φ × Argument 𝒜 ψ


-- @@ L34-34 verbatim
abbrev Witness (φ : Formula α) := Argument ℰ φ


-- @@ L36-36 verbatim
abbrev Counter (φ : Formula α) := Argument 𝒜 φ


-- @@ L38-45 verbatim
abbrev Realizable (V : α → Prop) : (φ : Formula α) → Witness φ → Counter φ → Prop
  |       ⊥,      (),       () => False
  | .atom a,      (),       () => V a
  |   φ ⋏ _, ⟨θ₁, _⟩,  .inl π₁ => Realizable V φ θ₁ π₁
  |   _ ⋏ ψ, ⟨_, θ₂⟩,  .inr π₂ => Realizable V ψ θ₂ π₂
  |   φ ⋎ _, .inl θ₁, ⟨π₁,  _⟩ => Realizable V φ θ₁ π₁
  |   _ ⋎ ψ, .inr θ₂, ⟨ _, π₂⟩ => Realizable V ψ θ₂ π₂
  |   φ 🡒 ψ,  ⟨f, g⟩, ⟨ θ,  π⟩ => Realizable V φ θ (g θ π) → Realizable V ψ (f θ) π


-- @@ L47-47 verbatim
scoped notation:80 "⟦" w " | " c "⟧⊩[" V "] " φ:46 => Realizable V φ w c


-- @@ L49-49 verbatim
def Valid (φ : Formula α) : Prop := ∃ w, ∀ V c, ⟦w | c⟧⊩[V] φ


-- @@ L51-51 verbatim
def NotValid (φ : Formula α) : Prop := ∀ w, ∃ V c, ¬⟦w | c⟧⊩[V] φ


-- @@ L53-53 verbatim
scoped notation "⊩ " φ => Valid φ


-- @@ L55-58 verbatim
scoped notation "⊮ " φ => NotValid φ

lemma not_valid_iff_notValid {φ : Formula α} : (¬⊩ φ) ↔ (⊮ φ) := by
  simp [Valid, NotValid]


-- @@ L60-60 verbatim
namespace Realizable


-- @@ L62-62 verbatim
@[simp] lemma falsum {w c V} : ¬⟦w | c⟧⊩[V] (⊥ : Formula α) := id


-- @@ L64-64 verbatim
@[simp] lemma atom {w c V} {a : α} : (⟦w | c⟧⊩[V] .atom a) ↔ V a := Eq.to_iff rfl


-- @@ L66-67 verbatim
@[simp] lemma and_left {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inl π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.1 | π⟧⊩[V] φ := Eq.to_iff rfl


-- @@ L69-70 verbatim
@[simp] lemma and_right {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inr π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.2 | π⟧⊩[V] ψ := Eq.to_iff rfl


-- @@ L72-73 verbatim
@[simp] lemma or_left {φ ψ : Formula α} {V θ π} :
    ⟦.inl θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.1⟧⊩[V] φ := Eq.to_iff rfl


-- @@ L75-76 verbatim
@[simp] lemma or_right {φ ψ : Formula α} {V θ π} :
    ⟦.inr θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.2⟧⊩[V] ψ := Eq.to_iff rfl


-- @@ L78-79 verbatim
@[simp] lemma imply {φ ψ : Formula α} {V f π} :
    ⟦f | π⟧⊩[V] φ 🡒 ψ ↔ (⟦π.1 | f.2 π.1 π.2⟧⊩[V] φ → ⟦f.1 π.1 | π.2⟧⊩[V] ψ) := Eq.to_iff rfl


-- @@ L81-81 verbatim
@[simp] lemma verum {w c V} : ⟦w | c⟧⊩[V] (⊤ : Formula α) := by simp [Realizable]


-- @@ L83-83 verbatim
@[simp] lemma not {φ : Formula α} {V θ f} : ⟦f | θ⟧⊩[V] ∼φ ↔ ¬⟦θ.1 | f.2 θ.1 θ.2⟧⊩[V] φ := Eq.to_iff rfl


-- @@ L85-85 verbatim
end Realizable


-- @@ L87-99 verbatim
protected lemma Valid.refl (φ : Formula α) : ⊩ φ 🡒 φ := ⟨⟨id, fun _ π ↦ π⟩, by rintro V ⟨θ, π⟩; simp⟩

lemma NotValid.em (a : α) : ⊮ atom a ⋎ ∼atom a := by
  rintro (⟨⟨⟩⟩ | ⟨f⟩)
  · refine ⟨fun _ ↦ False, ⟨(), (), ()⟩, ?_⟩
    rw [Realizable.or_left]; simp
  · rcases f with ⟨f₁, f₂⟩
    have : f₁ = id := rfl
    rcases this
    have : f₂ = fun _ _ ↦ () := rfl
    rcases this
    refine ⟨fun _ ↦ true, ⟨(), (), ()⟩, ?_⟩
    rw [Realizable.or_right]; simp


-- @@ L101-101 verbatim
end FFL.Propositional.Dialectica


-- @@ L103-103 verbatim
end
