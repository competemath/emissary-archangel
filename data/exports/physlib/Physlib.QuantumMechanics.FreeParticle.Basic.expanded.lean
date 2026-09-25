/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.QuantumSystem.Basic

-- @@ L11-33 verbatim
/-!

# The free particle on `Space d`

## i. Overview

The free quantum particle is one of the simplest quantum systems.
States for a particle of mass `m` are elements of `SpaceDHilbertSpace d` and evolve according
to the Hamiltonian `p²/2m` with no potential.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Hilbert space
- C. Hamiltonian
- D. As a quantum system

## iv. References

* None.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
noncomputable section

-- @@ L38-38 verbatim
namespace QuantumMechanics


-- @@ L40-44 verbatim
/-- A free, spinless quantum particle with mass `m > 0` in `Space d`. -/
structure FreeParticle (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m


-- @@ L46-46 verbatim
variable {d : ℕ} (Q : FreeParticle d)


-- @@ L48-48 verbatim
namespace FreeParticle


-- @@ L50-52 verbatim
/-!
## A. Basic properties
-/


-- @@ L54-55 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L57-58 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L60-61 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L63-65 verbatim
/-!
## B. Hilbert space
-/


-- @@ L67-69 verbatim
/-- The Hilbert space for the free particle. -/
@[nolint unusedArguments]
abbrev HS (_ : FreeParticle d) : Type _ := SpaceDHilbertSpace d


-- @@ L71-73 verbatim
/-!
## C. Hamiltonian
-/


-- @@ L75-76 verbatim
/-- The Hamiltonian, `p²/(2m)`. -/
def hamiltonian : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator


-- @@ L78-82 expanded
/-- The Hamiltonian for the free particle is essentially self-adjoint.
  This follows immediately from the ess. self-adjointness of the momentum-square operator. -/
def hamiltonian_essentially_self_adjoint : InformalLemma
    where
  deps := [``FreeParticle]
  tag := "QM-FP-hamESA"


-- @@ L84-86 verbatim
/-!
## D. As a quantum system
-/


-- @@ L88-91 expanded
/-- The free particle as a quantum system (self-adjoint Hamiltonian acting on a Hilbert space). -/
def toQuantumSystem : InformalDefinition
    where
  deps := [``FreeParticle]
  tag := "QM-FP-sys"


-- @@ L93-93 verbatim
end FreeParticle

-- @@ L94-94 verbatim
end QuantumMechanics

-- @@ L95-95 verbatim
end
