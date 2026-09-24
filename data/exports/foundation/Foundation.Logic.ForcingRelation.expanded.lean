module

public import Foundation.Logic.LogicSymbol
public import Foundation.Vorspiel.AdjunctiveSet


-- @@ L6-6 verbatim
/-! # Forcing relation -/


-- @@ L8-8 verbatim
@[expose] public section


-- @@ L10-10 verbatim
namespace FFL


-- @@ L12-13 verbatim
class ForcingRelation (W : Type*) (F : outParam Type*) where
  Forces : W → F → Prop


-- @@ L15-15 verbatim
infix:45 " ⊩ " => ForcingRelation.Forces


-- @@ L17-18 verbatim
class ForcingExists (W : Type*) (α : outParam Type*) where
  Forces : W → α → Prop


-- @@ L20-20 verbatim
infix:45 " ⊩↓ " => ForcingExists.Forces


-- @@ L22-22 verbatim
namespace ForcingRelation


-- @@ L24-24 verbatim
variable {W : Type*} {F : Type*} [ForcingRelation W F] [LogicalConnective F] [LogicalNeutral F]


-- @@ L26-26 verbatim
abbrev NotForces (w : W) (φ : F) : Prop := ¬w ⊩ φ


-- @@ L28-28 verbatim
infix:45 " ⊮ " => NotForces


-- @@ L30-30 verbatim
variable (W)


-- @@ L32-35 verbatim
class BasicSemantics where
  verum (w : W) : w ⊩ ⊤
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ


-- @@ L37-38 verbatim
class Monotone (R : outParam (W → W → Prop)) where
  monotone {w : W} : w ⊩ φ → ∀ v, R w v → v ⊩ φ


-- @@ L40-43 verbatim
class IntKripke (R : outParam (W → W → Prop)) extends BasicSemantics W, Monotone W R where
  imply (w : W) : w ⊩ φ 🡒 ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)
  falsum (w : W) : ¬w ⊩ ⊥
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → ¬v ⊩ φ)


-- @@ L45-45 verbatim
variable {W}


-- @@ L47-50 verbatim
attribute [simp, grind .]
  BasicSemantics.verum BasicSemantics.and
  BasicSemantics.or
  IntKripke.falsum


-- @@ L52-54 verbatim
attribute [grind .]
  IntKripke.imply
  IntKripke.not


-- @@ L56-58 verbatim
@[simp, grind =]
lemma iff (R : W → W → Prop) [IntKripke W R] : w ⊩ (φ 🡘 ψ) ↔ (∀ v, R w v → (v ⊩ φ ↔ v ⊩ ψ)) := by
  simp [LogicalConnective.iff, IntKripke.imply]; grind


-- @@ L60-60 verbatim
variable (W)


-- @@ L62-62 verbatim
abbrev AllForces (φ : F) : Prop := ∀ w : W, w ⊩ φ


-- @@ L64-64 verbatim
infix:45 " ∀⊩ " => AllForces


-- @@ L66-66 verbatim
abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop := ∀ φ ∈ s, W ∀⊩ φ


-- @@ L68-68 verbatim
infix:45 " ∀⊩* " => AllForcesSet


-- @@ L70-70 verbatim
variable {W}


-- @@ L72-72 verbatim
namespace AllForces


-- @@ L74-74 verbatim
@[simp] lemma verum [BasicSemantics W] : W ∀⊩ ⊤ := fun _ ↦ by simp


-- @@ L76-77 verbatim
@[simp] lemma and [BasicSemantics W] : W ∀⊩ φ ⋏ ψ ↔ W ∀⊩ φ ∧ W ∀⊩ ψ := by
  simp [AllForces]; grind


-- @@ L79-79 verbatim
end AllForces


-- @@ L81-81 verbatim
end ForcingRelation


-- @@ L83-83 verbatim
/-! ### Forcing relation for classical logic -/


-- @@ L85-86 verbatim
class WeakForcingRelation (ℙ : Type*) (F : outParam Type*) where
  WeaklyForces : ℙ → F → Prop


-- @@ L88-88 verbatim
infix:45 " ⊩ᶜ " => WeakForcingRelation.WeaklyForces


-- @@ L90-90 verbatim
namespace WeakForcingRelation


-- @@ L92-92 verbatim
variable {ℙ : Type*} {F : Type*} [WeakForcingRelation ℙ F] [LogicalConnective F] [LogicalNeutral F]


-- @@ L94-94 verbatim
abbrev NotForces (p : ℙ) (φ : F) : Prop := ¬p ⊩ᶜ φ


-- @@ L96-96 verbatim
infix:45 " ⊮ᶜ " => NotForces


-- @@ L98-98 verbatim
variable (ℙ)


-- @@ L100-103 verbatim
class BasicSemantics where
  verum (p : ℙ) : p ⊩ᶜ ⊤
  falsum (p : ℙ) : ¬p ⊩ᶜ ⊥
  and (p : ℙ) : p ⊩ᶜ φ ⋏ ψ ↔ p ⊩ᶜ φ ∧ p ⊩ᶜ ψ


-- @@ L105-110 verbatim
class ClassicalKripke (R : outParam (ℙ → ℙ → Prop)) extends BasicSemantics ℙ where
  or (p : ℙ) : p ⊩ᶜ φ ⋎ ψ ↔ ∀ q, R p q → ∃ x, R q x ∧ (x ⊩ᶜ φ ∨ x ⊩ᶜ ψ)
  not (p : ℙ) : p ⊩ᶜ ∼φ ↔ (∀ q, R p q → ¬q ⊩ᶜ φ)
  imply (p : ℙ) : p ⊩ᶜ φ 🡒 ψ ↔ (∀ q, R p q → q ⊩ᶜ φ → q ⊩ᶜ ψ)
  monotone {p : ℙ} : p ⊩ᶜ φ → ∀ q, R p q → q ⊩ᶜ φ
  generic {p : ℙ} : (∀ q, R p q → ∃ r, R q r ∧ r ⊩ᶜ φ) → p ⊩ᶜ φ


-- @@ L112-112 verbatim
variable {ℙ}


-- @@ L114-116 verbatim
attribute [simp, grind .]
  BasicSemantics.verum BasicSemantics.falsum BasicSemantics.and
  ClassicalKripke.or ClassicalKripke.imply ClassicalKripke.not


-- @@ L118-118 verbatim
variable (ℙ)


-- @@ L120-120 verbatim
abbrev AllForces (φ : F) : Prop := ∀ p : ℙ, p ⊩ᶜ φ


-- @@ L122-122 verbatim
infix:45 " ∀⊩ᶜ " => AllForces


-- @@ L124-124 verbatim
abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop := ∀ φ ∈ s, ℙ ∀⊩ᶜ φ


-- @@ L126-126 verbatim
infix:45 " ∀⊩ᶜ* " => AllForcesSet


-- @@ L128-128 verbatim
variable {ℙ}


-- @@ L130-130 verbatim
namespace AllForces


-- @@ L132-132 verbatim
@[simp] lemma verum [BasicSemantics ℙ] : ℙ ∀⊩ᶜ ⊤ := fun _ ↦ by simp


-- @@ L134-134 verbatim
@[simp] lemma falsum [BasicSemantics ℙ] [Nonempty ℙ] : ¬ℙ ∀⊩ᶜ ⊥ := fun h ↦ by simpa using h (Classical.choice inferInstance)


-- @@ L136-146 verbatim
@[simp] lemma and [BasicSemantics ℙ] : ℙ ∀⊩ᶜ φ ⋏ ψ ↔ ℙ ∀⊩ᶜ φ ∧ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces]; grind

/-
@[simp] lemma or [ClassicalKripke ℙ R] : ℙ ∀⊩ᶜ φ ⋎ ψ ↔ ℙ ∀⊩ᶜ φ ∨ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces]
  constructor
  · intro h
    by_contra! C
    rcases C with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
-/


-- @@ L148-148 verbatim
end AllForces



-- @@ L151-151 verbatim
end WeakForcingRelation


-- @@ L153-153 verbatim
end FFL


-- @@ L155-155 verbatim
end
