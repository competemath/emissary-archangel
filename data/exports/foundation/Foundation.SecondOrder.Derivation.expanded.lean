module

public import Foundation.SecondOrder.Syntax.Rew


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-9 verbatim
/-!
# Second-order one-sided $\mathbf{LK}$
-/


-- @@ L11-11 verbatim
namespace FFL.SecondOrder


-- @@ L13-13 verbatim
open FirstOrder


-- @@ L15-15 verbatim
variable {L : Language}


-- @@ L17-17 verbatim
abbrev Sequent (L : Language) := List (Proposition L)


-- @@ L19-19 verbatim
namespace Sequent


-- @@ L21-21 verbatim
def shift₀ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₀


-- @@ L23-23 verbatim
@[simp] lemma shift₀_nil : shift₀ ([] : Sequent L) = [] := rfl


-- @@ L25-26 verbatim
@[simp] lemma shift₀_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₀ (φ :: Γ) = Semiproposition.shift₀ φ :: shift₀ Γ := rfl


-- @@ L28-28 verbatim
def shift₁ (Γ : Sequent L) : Sequent L := Γ.map Semiproposition.shift₁


-- @@ L30-30 verbatim
@[simp] lemma shift₁_nil : shift₁ ([] : Sequent L) = [] := rfl


-- @@ L32-33 verbatim
@[simp] lemma shift₁_cons (φ : Proposition L) (Γ : Sequent L) :
    shift₁ (φ :: Γ) = Semiproposition.shift₁ φ :: shift₁ Γ := rfl


-- @@ L35-35 verbatim
instance : Tilde (Sequent L) := ⟨List.map (∼·)⟩


-- @@ L37-37 verbatim
@[simp] lemma tilde_nil : ∼([] : Sequent L) = [] := rfl


-- @@ L39-40 verbatim
@[simp] lemma tilde_cons (φ : Proposition L) (Γ : Sequent L) :
    ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl


-- @@ L42-42 verbatim
end Sequent


-- @@ L44-55 verbatim
/-- Second-order one-sided $\mathbf{LK}$-derivation -/
inductive Derivation : Sequent L → Type _
| identity : Derivation [φ, ∼φ]
| cut : Derivation (φ :: Γ) → Derivation (∼φ :: Γ) → Derivation Γ
| wk : Derivation Γ → Γ ⊆ Δ → Derivation Δ
| verum : Derivation [⊤]
| and : Derivation (φ :: Γ) → Derivation (ψ :: Γ) → Derivation (φ ⋏ ψ :: Γ)
| or : Derivation (φ :: ψ :: Γ) → Derivation (φ ⋎ ψ :: Γ)
| all₁ {φ : Semiproposition L 0 1} : Derivation (φ.free₀ :: Sequent.shift₀ Γ) → Derivation ((∀¹ φ) :: Γ)
| exs₁ {φ : Semiproposition L 0 1} : Derivation (φ/[t] :: Γ) → Derivation ((∃¹ φ) :: Γ)
| all₂ {φ : Semiproposition L 1 0} : Derivation (φ.free₁ :: Sequent.shift₁ Γ) → Derivation ((∀² φ) :: Γ)
| exs₂ {φ : Semiproposition L 1 0} : Derivation (φ/⟦ψ⟧ :: Γ) → Derivation ((∃² φ) :: Γ)


-- @@ L57-57 verbatim
scoped prefix:45 "⊢ᴸᴷ¹ " => Derivation


-- @@ L59-59 verbatim
namespace Derivation


-- @@ L61-61 verbatim
def cast {Γ Δ : Sequent L} (d : ⊢ᴸᴷ¹ Γ) (h : Γ = Δ) : ⊢ᴸᴷ¹ Δ := h ▸ d


-- @@ L63-63 verbatim
end Derivation


-- @@ L65-65 verbatim
abbrev Proof (φ : Sentence L) := ⊢ᴸᴷ¹ [(φ : Proposition L)]


-- @@ L67-68 verbatim
inductive Proof.Symbol (L : Language) : Type
| symbol


-- @@ L70-70 verbatim
notation "𝐋𝐊²" => Proof.Symbol.symbol


-- @@ L72-72 verbatim
instance : Entailment (Proof.Symbol L) (Sentence L) := ⟨fun _ ↦ Proof⟩


-- @@ L74-74 verbatim
/-! ## Proof system with axioms -/


-- @@ L76-76 verbatim
abbrev Schema (L : Language) := Set (Proposition L)


-- @@ L78-81 verbatim
protected structure Schema.Derivation (𝓢 : Schema L) (φ : Proposition L) where
  axioms : Sequent L
  derivation : Derivation (φ :: ∼axioms)
  isInstance : ∀ φ ∈ axioms, φ ∈ 𝓢


-- @@ L83-83 verbatim
instance : Entailment (Schema L) (Proposition L) := ⟨Schema.Derivation⟩


-- @@ L85-85 verbatim
/-! ## Theory: a set of provable sentences -/


-- @@ L87-87 verbatim
abbrev Theory (L : Language) := Set (Sentence L)


-- @@ L89-89 verbatim
instance : Entailment (Theory L) (Sentence L) := ⟨fun T φ ↦ PLift (φ ∈ T)⟩


-- @@ L91-91 verbatim
def Schema.theory (𝓢 : Schema L) : Theory L := {φ | 𝓢 ⊢ ↑φ}


-- @@ L93-93 verbatim
namespace Theory


-- @@ L95-98 verbatim
variable {T : Theory L}

lemma provable_def {φ : Sentence L} : T ⊢ φ ↔ φ ∈ T :=
  ⟨fun h ↦ PLift.down h.some, fun h ↦ ⟨⟨h⟩⟩⟩


-- @@ L100-101 verbatim
@[simp] lemma schema_theory_def {𝓢 : Schema L} {φ : Sentence L} :
    𝓢.theory ⊢ φ ↔ 𝓢 ⊢ ↑φ := by simp [provable_def, Schema.theory]


-- @@ L103-103 verbatim
end Theory


-- @@ L105-105 verbatim
end FFL.SecondOrder


-- @@ L107-107 verbatim
end
