/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.QuantumSystem.Basic

-- @@ L11-34 verbatim
/-!

# The infinite square well

## i. Overview

The particle in an infinite square well is one of the simplest quantum systems.
The domain is an axis-aligned cuboid (the well) and energy eigenstates are (products of)
trigonometric functions satisfying appropriate boundary conditions.

## ii. Key results

## iii. Table of contents

- A. Basic properties
- B. Domain
- C. Hilbert space
- D. Hamiltonian
- E. As a quantum system

## iv. References

* None.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section

-- @@ L39-39 verbatim
namespace QuantumMechanics


-- @@ L41-41 verbatim
open Set MeasureTheory


-- @@ L43-56 verbatim
/-- A spinless quantum particle with mass `m > 0` confined to a cuboid in `Space d`.

  The bounds of the well are specified by two functions `lower upper : Fin d → ℝ`
  satisfying `∀ i, lower i < upper i`. -/
structure InfiniteSquareWell (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The lower bounds of the well. -/
  lower : Fin d → ℝ
  /-- The upper bounds of the well. -/
  upper : Fin d → ℝ
  /-- The well is a non-empty set. -/
  h_bounds : ∀ i, lower i < upper i


-- @@ L58-58 verbatim
variable {d : ℕ} (Q : InfiniteSquareWell d)


-- @@ L60-60 verbatim
namespace InfiniteSquareWell


-- @@ L62-64 verbatim
/-!
## A. Basic properties
-/


-- @@ L66-67 verbatim
@[simp]
lemma m_pos : 0 < Q.m := Q.hm


-- @@ L69-70 verbatim
@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le


-- @@ L72-73 verbatim
@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'


-- @@ L75-77 verbatim
/-!
## B. Domain
-/


-- @@ L79-80 verbatim
/-- The domain of the infinite square well as a Cartesian product of closed intervals. -/
def well : Set (Space d) := Space.val ⁻¹' Icc Q.lower Q.upper


-- @@ L82-84 verbatim
/-!
## C. Hilbert space
-/


-- @@ L86-87 verbatim
/-- The measure associated with the domain of the infinite square well. -/
def measure : Measure (Space d) := volume.restrict Q.well


-- @@ L89-90 verbatim
/-- The Hilbert space for the infinite square well. -/
abbrev HS : Type _ := SpaceDHilbertSpace d Q.measure


-- @@ L92-94 verbatim
/-!
## D. Hamiltonian
-/


-- @@ L96-101 expanded
/-- The Hamiltonian for the infinite square well is `(2m)⁻¹momentumSqOperator` with respect
  to `InfiniteSquareWell.measure`. This requires first generalizing `momentumSqOperator`
  to `Space d` measures other than `volume`. -/
def hamiltonian : InformalDefinition
    where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-ham"


-- @@ L103-106 expanded
/-- The Hamiltonian for the infinite square well is essentially self-adjoint. -/
def hamiltonian_essentially_self_adjoint : InformalLemma
    where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-hamESA"


-- @@ L108-110 verbatim
/-!
## E. As a quantum system
-/


-- @@ L112-116 expanded
/-- The particle in an infinite square well as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
def toQuantumSystem : InformalDefinition
    where
  deps := [``InfiniteSquareWell]
  tag := "QM-ISW-sys"


-- @@ L118-118 verbatim
end InfiniteSquareWell

-- @@ L119-119 verbatim
end QuantumMechanics

-- @@ L120-120 verbatim
end
