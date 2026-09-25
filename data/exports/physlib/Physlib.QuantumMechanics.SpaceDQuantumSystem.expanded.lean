/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication

-- @@ L10-34 verbatim
/-!

# Single-particle quantum system on `Space d`

## i. Overview

In this module we introduce the general notion of a single-particle quantum system on `Space d`.

The structure `SpaceDQuantumSystem` encompasses the basic information needed to specify the system,
namely the number of spatial dimensions, the particle's mass and the potential function.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Operators
  - B.1. Kinetic energy
  - B.2. Potential energy
  - B.3. Hamiltonian

## iv. References

* None.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
namespace QuantumMechanics


-- @@ L40-40 verbatim
open Complex

-- @@ L41-41 verbatim
open MeasureTheory

-- @@ L42-42 verbatim
open SpaceDHilbertSpace


-- @@ L44-55 verbatim
/-- A single-particle quantum system with Hilbert space `SpaceDHilbertSpace d`,
  characterized by the number of spatial dimensions `d : ℕ`, particle's mass `m > 0`
  and potential function `potential : Space d → ℝ`. -/
@[ext]
structure SpaceDQuantumSystem where
  /-- The number of spatial dimensions. -/
  d : ℕ
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The potential function. -/
  potential : Space d → ℝ


-- @@ L57-57 verbatim
variable {Q : SpaceDQuantumSystem}


-- @@ L59-59 verbatim
namespace SpaceDQuantumSystem

-- @@ L60-60 verbatim
noncomputable section


-- @@ L62-63 verbatim
/-- The Hilbert space, `SpaceDHilbertSpace Q.d`. -/
abbrev HS := SpaceDHilbertSpace Q.d


-- @@ L65-67 verbatim
/-!
## A. Basic properties
-/


-- @@ L69-70 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L72-73 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L75-76 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L78-80 verbatim
/-!
## B. Operators
-/


-- @@ L82-82 verbatim
section

-- @@ L83-83 verbatim
open SchwartzMap

-- @@ L84-84 verbatim
open LinearPMap


-- @@ L86-88 verbatim
/-!
### B.1. Kinetic energy
-/


-- @@ L90-91 expanded
/-- The kinetic operator `(2m)⁻¹𝐩²` as a continuous linear map on Schwartz space. -/
def kineticCLM : 𝓢(Space Q.d, ℂ) →L[ℂ] 𝓢(Space Q.d, ℂ) :=
  (2 * Q.m)⁻¹ • (momentumCLM ⬝ᵥ momentumCLM)


-- @@ L93-93 expanded
lemma kineticCLM_eq : Q.kineticCLM = (2 * Q.m)⁻¹ • (momentumCLM ⬝ᵥ momentumCLM) :=
  rfl


-- @@ L95-96 verbatim
/-- The kinetic operator as an unbounded operator with domain `schwartzSubmodule Q.d`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := ofReal (2 * Q.m)⁻¹ • momentumSqOperator


-- @@ L98-98 verbatim
lemma kineticOperator_eq : Q.kineticOperator = ofReal (2 * Q.m)⁻¹ • momentumSqOperator := rfl


-- @@ L100-102 verbatim
/-!
### B.2. Potential energy
-/


-- @@ L104-106 verbatim
/-- The potential operator as a continuous linear map on Schwartz space,
  where `Q.potential` is a function of temperate growth. -/
def potentialCLM : 𝓢(Space Q.d, ℂ) →L[ℂ] 𝓢(Space Q.d, ℂ) := smulLeftCLM ℂ (ofReal ∘ Q.potential)


-- @@ L108-108 verbatim
lemma potentialCLM_eq : Q.potentialCLM = smulLeftCLM ℂ (ofReal ∘ Q.potential) := rfl


-- @@ L110-113 verbatim
lemma potentialCLM_apply (h_HTG : Q.potential.HasTemperateGrowth) (ψ : 𝓢(Space Q.d, ℂ)) :
    Q.potentialCLM ψ = fun x ↦ Q.potential x • ψ x := by
  rw [potentialCLM_eq, smulLeftCLM_apply (by fun_prop)]
  simp


-- @@ L115-119 verbatim
@[simp]
lemma potentialCLM_apply_apply
    (h_HTG : Q.potential.HasTemperateGrowth) (ψ : 𝓢(Space Q.d, ℂ)) (x : Space Q.d) :
    Q.potentialCLM ψ x = Q.potential x • ψ x := by
  rw [potentialCLM_apply h_HTG]


-- @@ L121-123 expanded
/-- The potential operator as a self-adjoint, unbounded multiplication operator
  with domain `{ψ ∈ Q.HS | Q.potential • ψ ∈ Q.HS}`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  mulOperator volume (ofReal ∘ Q.potential)


-- @@ L125-125 expanded
lemma potentialOperator_eq : Q.potentialOperator = mulOperator volume (ofReal ∘ Q.potential) :=
  rfl


-- @@ L127-129 verbatim
lemma potentialOperator_isSelfAdjoint (h_AESM : AEStronglyMeasurable Q.potential) :
    IsSelfAdjoint Q.potentialOperator :=
  mulOperator_isSelfAdjoint_ofReal (by fun_prop) (by ext; simp)


-- @@ L131-133 verbatim
lemma potentialOperator_domain_ge (h_HTG : Q.potential.HasTemperateGrowth) :
    SchwartzSubmodule Q.d ≤ Q.potentialOperator.domain :=
  mulOperator_domain_ge_of_hasTemperateGrowth (by fun_prop) volume


-- @@ L135-137 verbatim
/-!
### B.3. Hamiltonian
-/


-- @@ L139-141 verbatim
/-- The Hamiltonian operator as a continuous linear map on Schwartz space,
  where `Q.potential` is a function of temperate growth. -/
def hamiltonianCLM : 𝓢(Space Q.d, ℂ) →L[ℂ] 𝓢(Space Q.d, ℂ) := Q.kineticCLM + Q.potentialCLM


-- @@ L143-143 verbatim
lemma hamiltonianCLM_eq : Q.hamiltonianCLM = Q.kineticCLM + Q.potentialCLM := rfl


-- @@ L145-146 verbatim
/-- The Hamilontian operator as a symmetric unbounded operator. -/
def hamiltonianOperator : Q.HS →ₗ.[ℂ] Q.HS := Q.kineticOperator + Q.potentialOperator


-- @@ L148-149 verbatim
lemma hamiltonianOperator_eq : Q.hamiltonianOperator = Q.kineticOperator + Q.potentialOperator :=
  rfl


-- @@ L151-151 verbatim
end


-- @@ L153-153 verbatim
end

-- @@ L154-154 verbatim
end SpaceDQuantumSystem

-- @@ L155-155 verbatim
end QuantumMechanics
