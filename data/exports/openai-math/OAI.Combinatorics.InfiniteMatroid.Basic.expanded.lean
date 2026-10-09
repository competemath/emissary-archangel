import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Matroid


-- @@ L7-7 verbatim
namespace InfiniteMatroidCounterexample


-- @@ L9-9 verbatim
abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)

-- @@ L10-10 verbatim
abbrev E0 := D × Bool

-- @@ L11-11 verbatim
abbrev E := ℤ × D


-- @@ L13-14 verbatim
def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual


-- @@ L16-23 verbatim
def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C


-- @@ L25-25 verbatim
end InfiniteMatroidCounterexample


-- @@ L27-27 verbatim
end OAI
