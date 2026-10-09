import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace EuclideanSteinitzBergstrom


-- @@ L7-7 verbatim
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)


-- @@ L9-15 verbatim
def SignedPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
        ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤
            C * Real.sqrt d


-- @@ L17-22 verbatim
def OrderingPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
      ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤
          C * Real.sqrt d


-- @@ L24-24 verbatim
end EuclideanSteinitzBergstrom


-- @@ L26-26 verbatim
end OAI
