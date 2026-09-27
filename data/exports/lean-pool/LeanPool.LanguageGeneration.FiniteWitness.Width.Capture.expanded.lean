/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Simplified.Capture


-- @@ L10-16 verbatim
/-!
# Bounded capture for the separation-width hierarchy

The hierarchy uses the direct diagonal construction from `Simplified.Capture`.
These compatibility theorems keep the width API without maintaining a second
finite-state construction and a separate induction on the cardinality bound.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace GenLimit.FiniteWitness


-- @@ L22-22 verbatim
variable {α : Type*}


-- @@ L24-31 verbatim
/-- A uniformly bounded finite-set sequence is captured infinitely often by
one set containing none of the prescribed infinite cores. The universe is
arbitrary; no countability or measurability of its points is assumed. -/
theorem bounded_capture (d : ℕ) (U : ℕ → Finset α)
    (hU : ∀ n, (U n).card ≤ d) (C : ℕ → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ m, (C m).Infinite → ¬ C m ⊆ D :=
  Simplified.bounded_capture d U hU C


-- @@ L33-37 verbatim
theorem bounded_capture_indexed {ι : Type*} [Countable ι]
    (d : ℕ) (U : ℕ → Finset α) (hU : ∀ n, (U n).card ≤ d) (C : ι → Set α) :
    ∃ D : Set α, {n | (↑(U n) : Set α) ⊆ D}.Infinite ∧
      ∀ i, (C i).Infinite → ¬ C i ⊆ D :=
  Simplified.bounded_capture_indexed d U hU C


-- @@ L39-39 verbatim
end GenLimit.FiniteWitness
