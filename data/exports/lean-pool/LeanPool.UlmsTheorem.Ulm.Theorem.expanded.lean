/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import LeanPool.UlmsTheorem.PGroups.UlmInvariants
import LeanPool.UlmsTheorem.Ulm.Classification
import LeanPool.UlmsTheorem.Ulm.Invariance
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset


-- @@ L15-19 verbatim
/-!
# Ulm's theorem

Public entry point for the Ulm-theorem track of the project.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace UlmsTheorem


-- @@ L25-25 verbatim
open Cardinal Ordinal


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
variable (p : ℕ) [hp : Fact p.Prime]


-- @@ L31-39 verbatim
/-- Public easy direction of Ulm's theorem: an isomorphism preserves all
classical Ulm invariants. -/
theorem ulm_invariants_of_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (hiso : Nonempty (G ≃+ H)) :
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  rcases hiso with ⟨φ⟩
  intro α
  exact ulmInvariant_iso_invariant (p := p) φ α


-- @@ L41-49 verbatim
/-- Public hard direction of Ulm's theorem: equal classical Ulm invariants imply isomorphism
for countable reduced abelian `p`-groups. -/
theorem iso_of_ulm_invariants {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H)
    (hinv : ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H)) :
    Nonempty (G ≃+ H) := by
  exact iso_of_ulmInvariant_eq (p := p) hGred hHred hinv


-- @@ L51-61 verbatim
/-- Ulm's theorem: two countable reduced abelian p-groups are isomorphic iff
their classical Ulm invariants agree. -/
theorem ulm_theorem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H]
    (hGred : IsReducedPGroup p G) (hHred : IsReducedPGroup p H) :
    Nonempty (G ≃+ H) ↔
    ∀ α : Ordinal.{0},
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  constructor
  · exact ulm_invariants_of_iso (p := p)
  · exact iso_of_ulm_invariants (p := p) hGred hHred


-- @@ L63-63 verbatim
end UlmsTheorem
