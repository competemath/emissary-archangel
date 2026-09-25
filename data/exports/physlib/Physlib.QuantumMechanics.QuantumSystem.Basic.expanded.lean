/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded

-- @@ L9-41 verbatim
/-!

# Quantum system

## i. Overview

In non-relativistic quantum mechanics a quantum system is characterized by a Hilbert space
(complete inner product space) and self-adjoint Hamiltonian operator; these data are collected in
the `QuantumSystem` structure.

Two quantum systems are said to be "unitary equivalent" if there is a unitary bijection between
their respective Hilbert spaces which sends one Hamiltonian to the other under conjugation.
Unitary equivalent quantum systems are physically indestinguishable, as all operators, states,
matrix elements, probabilities, eigenvalues, etc. are in 1-1 correspondence.

## ii. Key results

Definitions
- `QuantumSystem` : Structure bundling together a choice of Hilbert space
    and self-adjoint Hamiltonian operator.
- `UnitaryRelation` : The unitary equivalence relation.

## iii. Table of contents

- A. Definition
- B. Creation from an essentially self-adjoint operator
- C. Zero
- D. Unitary equivalence

## iv. References

* None.
-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
namespace QuantumMechanics


-- @@ L49-49 verbatim
open LinearPMap


-- @@ L51-53 verbatim
/-!
## A. Definition
-/


-- @@ L55-67 verbatim
/-- A quantum system is identified by its Hilbert space and self-adjoint Hamiltonian operator. -/
structure QuantumSystem where
  /-- The complex Hilbert space. -/
  HS : Type*
  /-- The Hilbert space is a normed, commutative group. -/
  [instNormed : NormedAddCommGroup HS]
  /-- The Hilbert space is a complex inner product space. -/
  [instInner : InnerProductSpace ℂ HS]
  /-- The Hilbert space is complete. -/
  [instComplete : CompleteSpace HS]
  /-- The self-adjoint Hamiltonian operator. -/
  ℋ : HS →ₗ.[ℂ] HS
  ℋ_self_adjoint : IsSelfAdjoint ℋ


-- @@ L69-69 verbatim
namespace QuantumSystem


-- @@ L71-71 verbatim
instance (Q : QuantumSystem) : NormedAddCommGroup Q.HS := Q.instNormed


-- @@ L73-73 verbatim
instance (Q : QuantumSystem) : InnerProductSpace ℂ Q.HS := Q.instInner


-- @@ L75-75 verbatim
instance (Q : QuantumSystem) : CompleteSpace Q.HS := Q.instComplete


-- @@ L77-83 verbatim
/-!
## B. Creation from an essentially self-adjoint operator

An essentially self-adjoint operator has a unique self-adjoint extension
(c.f. `IsEssentiallySelfAdjoint.unique_self_adjoint_extension`).
For this reason, a quantum system can be uniquely associated to an e.s.a. Hamiltonian operator.
-/


-- @@ L85-88 verbatim
/-- Create a quantum system from a Hamiltonian operator which is merely
  essentially self-adjoint by taking its closure. -/
def mkESA {HS : Type*} [NormedAddCommGroup HS] [InnerProductSpace ℂ HS] [CompleteSpace HS]
    {ℋ : HS →ₗ.[ℂ] HS} (hℋ : IsEssentiallySelfAdjoint ℋ) : QuantumSystem := ⟨HS, ℋ.closure, hℋ⟩


-- @@ L90-92 verbatim
/-!
## C. Zero
-/


-- @@ L94-94 verbatim
instance instZero : Zero QuantumSystem := ⟨EuclideanSpace ℂ (Fin 0), 0, adjoint_zero⟩


-- @@ L96-98 verbatim
/-!
## D. Unitary equivalence
-/


-- @@ L100-105 verbatim
/-- The relation on quantum systems where `Q₁` is related to `Q₂` if there exists a linear isometry
  equivalence `e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS` between the respective Hilbert spaces satisfying
  `e ∘ Q₁.ℋ ∘ e.symm = Q₂.ℋ`. -/
def UnitaryRelation (Q₁ Q₂ : QuantumSystem) : Prop :=
  ∃ (e : Q₁.HS ≃ₗᵢ[ℂ] Q₂.HS) (h : Q₁.ℋ.domain.map e.toLinearMap = Q₂.ℋ.domain),
    ∀ ψ : Q₁.ℋ.domain, e (Q₁.ℋ ψ) = Q₂.ℋ ⟨e ψ, by simp [← h]⟩


-- @@ L107-109 verbatim
/-- The relation `UnitaryRelation` is reflexive. -/
lemma unitaryRelation_refl (Q : QuantumSystem) : UnitaryRelation Q Q :=
  ⟨LinearIsometryEquiv.refl _ _, by ext; simp [LinearIsometryEquiv.refl], by simp⟩


-- @@ L111-117 verbatim
/-- The relation `UnitaryRelation` is symmetric. -/
lemma unitaryRelation_symm {Q₁ Q₂ : QuantumSystem} (h₁₂ : UnitaryRelation Q₁ Q₂) :
    UnitaryRelation Q₂ Q₁ := by
  obtain ⟨e, h_domain, h⟩ := h₁₂
  refine ⟨e.symm, by ext; simp [← h_domain], fun ψ₂ ↦ ?_⟩
  apply e.symm_apply_eq.mpr
  simp [h ⟨e.symm ψ₂, by simpa [← h_domain] using ψ₂.2⟩]


-- @@ L119-124 verbatim
/-- The relation `UnitaryRelation` is transitive. -/
lemma unitaryRelation_trans {Q₁ Q₂ Q₃ : QuantumSystem} (h₁₂ : UnitaryRelation Q₁ Q₂)
    (h₂₃ : UnitaryRelation Q₂ Q₃) : UnitaryRelation Q₁ Q₃ := by
  obtain ⟨e₁₂, h_domain₁₂, _⟩ := h₁₂
  obtain ⟨e₂₃, h_domain₂₃, _⟩ := h₂₃
  exact ⟨e₁₂.trans e₂₃, by ext; simp [← h_domain₁₂, ← h_domain₂₃], by simp_all⟩


-- @@ L126-130 verbatim
/-- The relation `UnitaryRelation` is an equivalence relation. -/
lemma unitaryRelation_equiv : Equivalence UnitaryRelation where
  refl := unitaryRelation_refl
  symm := unitaryRelation_symm
  trans := unitaryRelation_trans


-- @@ L132-133 verbatim
/-- The setoid of quantum systems with `UnitaryRelation` for equivalence relation. -/
instance QuantumSystemSetoid : Setoid QuantumSystem := ⟨UnitaryRelation, unitaryRelation_equiv⟩


-- @@ L135-135 verbatim
end QuantumSystem

-- @@ L136-136 verbatim
end QuantumMechanics

-- @@ L137-137 verbatim
end
