/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.QuantumSystem.Basic

-- @@ L12-38 verbatim
/-!

# The rectangular potential barrier

## i. Overview

The rectangular potential barrier in one dimension provides the simplest example of quantum
tunnelling. A particle of mass `m` is subject to a piece-wise constant potential which is `V₀`
on a closed interval and zero elsewhere.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Potential function
- C. Hilbert space
- D. Operators
  - D.1. Kinetic
  - D.2. Potential
  - D.3. Hamiltonian
- E. As a quantum system

## iv. References

* None.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
noncomputable section

-- @@ L43-43 verbatim
namespace QuantumMechanics


-- @@ L45-45 verbatim
open Set MeasureTheory SpaceDHilbertSpace


-- @@ L47-60 verbatim
/-- A quantum particle with mass `m > 0` on `Space 1` subject to a rectangular potential barrier.

  The potential is `V₀` on the interval `Icc lower upper` and zero elsewhere. -/
structure RectangularBarrier where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bound of the barrier. -/
  lower : ℝ
  /-- The upper bound of the barrier. -/
  upper : ℝ
  h_bounds : lower < upper
  /-- The height of the potential barrier. -/
  V₀ : ℝ


-- @@ L62-62 verbatim
variable (Q : RectangularBarrier)


-- @@ L64-64 verbatim
namespace RectangularBarrier


-- @@ L66-68 verbatim
/-!
## A. Basic properties
-/


-- @@ L70-71 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L73-74 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L76-77 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L79-81 verbatim
/-!
## B. Potential function
-/


-- @@ L83-85 verbatim
/-- The piece-wise constant potential, equal to `Q.V₀` for `x.val 0 ∈ Icc Q.lower Q.upper`
  and zero otherwise. -/
def potentialFunction : Space 1 → ℝ := fun x ↦ (Icc Q.lower Q.upper).indicator (fun _ ↦ Q.V₀) (x 0)


-- @@ L87-88 verbatim
lemma potentialFunction_eq :
    Q.potentialFunction = fun x ↦ (Icc Q.lower Q.upper).indicator (fun _ ↦ Q.V₀) (x 0) := rfl


-- @@ L90-99 verbatim
/-- The piecewise-constant potential of the rectangular barrier is a.e. strongly measurable. -/
-- This relies on `Space.val` being measure-preserving.
lemma potentialFunction_aestronglyMeasurable: AEStronglyMeasurable Q.potentialFunction volume := by
  unfold potentialFunction
  apply AEStronglyMeasurable.indicator
  · fun_prop
  · change (MeasurableSet ((Icc Q.lower Q.upper) ∘ (fun (x: Space 1) => x.val 0)))
    have hi : MeasurableSet (Icc Q.lower Q.upper) := by measurability
    have hf : Measurable ((fun x => x.val 0) : Space 1 → ℝ) := by measurability
    exact MeasurableSet.preimage hi hf


-- @@ L101-103 verbatim
/-!
## C. Hilbert space
-/


-- @@ L105-107 verbatim
/-- The Hilbert space for the 1d rectangular barrier. -/
@[nolint unusedArguments]
abbrev HS (_ : RectangularBarrier) : Type _ := SpaceDHilbertSpace 1


-- @@ L109-111 verbatim
/-!
## D. Operators
-/


-- @@ L113-115 verbatim
/-!
### D.1. Kinetic
-/


-- @@ L117-118 verbatim
/-- The kinetic energy operator, `p²/2m`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator


-- @@ L120-122 verbatim
/-!
### D.2. Potential
-/


-- @@ L124-125 expanded
/-- The potential energy operator, defined by multiplication by `Q.potentialFunction`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS :=
  mulOperator volume (Complex.ofReal ∘ Q.potentialFunction)


-- @@ L127-137 verbatim
/-- The potential operator for the rectangular barrier is self-adjoint. -/
lemma potentialOperator_isSelfAdjoint (Q : RectangularBarrier) :
    IsSelfAdjoint Q.potentialOperator := by
  unfold IsSelfAdjoint
  unfold potentialOperator
  rw [mulOperator_isSelfAdjoint_ofReal]
  swap
  ext x
  simp only [Function.comp_apply, Complex.conj_ofReal]
  have hQ := potentialFunction_aestronglyMeasurable
  fun_prop


-- @@ L139-141 verbatim
/-!
### D.3. Hamiltonian
-/


-- @@ L143-146 expanded
/-- The Hamiltonian for the rectangular barrier. -/
def hamiltonian : InformalDefinition
    where
  deps := [``RectangularBarrier]
  tag := "QM-RB-ham"


-- @@ L148-151 expanded
/-- The Hamiltonian for the rectangular barrier is essentially self-adjoint. -/
def hamiltonian_essentially_self_adjoint : InformalLemma
    where
  deps := [``RectangularBarrier.hamiltonian]
  tag := "QM-RB-hamESA"


-- @@ L153-155 verbatim
/-!
## E. As a quantum system
-/


-- @@ L157-161 expanded
/-- The rectangular barrier as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
def toQuantumSystem : InformalDefinition
    where
  deps := [``RectangularBarrier.hamiltonian_essentially_self_adjoint]
  tag := "QM-RB-sys"


-- @@ L163-163 verbatim
end RectangularBarrier

-- @@ L164-164 verbatim
end QuantumMechanics

-- @@ L165-165 verbatim
end
