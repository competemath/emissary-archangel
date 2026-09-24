module

public import Foundation.Propositional.Entailment.Cl


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
/-! # Faithful embeddings among logical systems -/


-- @@ L9-9 verbatim
namespace FFL.Entailment


-- @@ L11-11 verbatim
variable {F₁ F₂ F₃ : Type*} {S₁ S₂ S₃ : Type*} [Entailment S₁ F₁] [Entailment S₂ F₂] [Entailment S₃ F₃]


-- @@ L13-13 verbatim
def IsFaithfulEmbedding (𝓢₁ : S₁) (𝓢₂ : S₂) (f : F₁ → F₂) : Prop := ∀ φ, 𝓢₂ ⊢ f φ ↔ 𝓢₁ ⊢ φ


-- @@ L15-16 verbatim
class FaithfullyEmbeddable (𝓢₁ : S₁) (𝓢₂ : S₂) : Prop where
  prop : ∃ f : F₁ → F₂, IsFaithfulEmbedding 𝓢₁ 𝓢₂ f


-- @@ L18-21 verbatim
namespace FaithfullyEmbeddable

lemma fun_exists (𝓢₁ : S₁) (𝓢₂ : S₂) [FaithfullyEmbeddable 𝓢₁ 𝓢₂] :
    ∃ f : F₁ → F₂, IsFaithfulEmbedding 𝓢₁ 𝓢₂ f := FaithfullyEmbeddable.prop


-- @@ L23-24 verbatim
@[refl] protected instance refl (𝓢₁ : S₁) : FaithfullyEmbeddable 𝓢₁ 𝓢₁ where
  prop := ⟨id, by intros _; simp⟩


-- @@ L26-32 verbatim
@[trans] lemma trans (𝓢₁ : S₁) (𝓢₂ : S₂) (𝓢₃ : S₃) [FaithfullyEmbeddable 𝓢₁ 𝓢₂] [FaithfullyEmbeddable 𝓢₂ 𝓢₃] :
    FaithfullyEmbeddable 𝓢₁ 𝓢₃ where
  prop := by
    rcases fun_exists 𝓢₁ 𝓢₂ with ⟨f₁₂, h₁₂⟩
    rcases fun_exists 𝓢₂ 𝓢₃ with ⟨f₂₃, h₂₃⟩
    refine ⟨f₂₃ ∘ f₁₂, ?_⟩
    intro φ; simp [h₁₂ φ, h₂₃ (f₁₂ φ)]


-- @@ L34-34 verbatim
end FaithfullyEmbeddable


-- @@ L36-36 verbatim
end FFL.Entailment


-- @@ L38-38 verbatim
end
