import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace GaussianMoat


-- @@ L7-7 verbatim
abbrev PrimeVertex := {z : GaussianInt // Irreducible z}


-- @@ L9-18 verbatim
noncomputable def primeGraph (D : ℝ) : SimpleGraph PrimeVertex where
  Adj p q := p ≠ q ∧ dist (p.val : ℂ) (q.val : ℂ) ≤ D
  symm := by
    constructor
    intro p q h
    exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩
  loopless := by
    constructor
    intro p h
    exact h.1 rfl


-- @@ L20-21 verbatim
def component (D : ℝ) (p : PrimeVertex) : Set PrimeVertex :=
  {q | (primeGraph D).Reachable p q}


-- @@ L23-26 verbatim
def MainEndpoint : Prop :=
  ∀ (D : ℝ) (z : ℕ → GaussianInt),
    (∀ t, Irreducible (z t)) → Function.Injective z →
    (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False


-- @@ L28-34 verbatim
def UniformEndpoint : Prop :=
  ∀ D : ℝ, ∃ B : ℕ,
    (∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B) ∧
    (∀ (n : ℕ) (z : Fin n → GaussianInt),
      (∀ i, Irreducible (z i)) → Function.Injective z →
      (∀ i j : Fin n, j.val = i.val + 1 → dist (z j : ℂ) (z i : ℂ) ≤ D) →
      n ≤ B)


-- @@ L36-36 verbatim
end GaussianMoat


-- @@ L38-38 verbatim
end OAI
