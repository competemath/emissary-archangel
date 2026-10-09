import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace AsymptoticallyMinimalLittlewood


-- @@ L7-9 verbatim
/-- The Littlewood polynomial of length N, evaluated at z. -/
def littlewoodValue {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)


-- @@ L11-13 verbatim
/-- Real signs in every consecutive degree 0,...,N-1. -/
def IsRealSigning {N : ℕ} (ε : Fin N → ℝ) : Prop :=
  ∀ k, ε k = -1 ∨ ε k = 1


-- @@ L15-18 verbatim
def MainStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N


-- @@ L20-20 verbatim
end AsymptoticallyMinimalLittlewood


-- @@ L22-22 verbatim
end OAI
