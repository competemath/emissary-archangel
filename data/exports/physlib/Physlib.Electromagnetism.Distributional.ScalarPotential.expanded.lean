/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Distributional.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

-- @@ L10-37 verbatim
/-!

# The Scalar Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the scalar potential, and prove lemmas about it.

Since `A` is relativistic it is a distribution of `SpaceTime d`, whilst
the scalar potential is non-relativistic and is therefore a distribution of `Time` and `Space d`.

## ii. Key results

- `DistElectromagneticPotential.scalarPotential` : The scalar potential from an
  electromagnetic potential which is a distribution.

## iii. Table of contents

- A. Scalar potential for distributions

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section

-- @@ L40-40 verbatim
namespace Electromagnetism

-- @@ L41-41 verbatim
open Module realLorentzTensor

-- @@ L42-42 verbatim
open TensorSpecies

-- @@ L43-43 verbatim
open Tensor


-- @@ L45-49 verbatim
/-!

## A. Scalar potential for distributions

-/


-- @@ L51-51 verbatim
namespace DistElectromagneticPotential

-- @@ L52-52 verbatim
open TensorSpecies

-- @@ L53-53 verbatim
open Tensor

-- @@ L54-54 verbatim
open SpaceTime

-- @@ L55-55 verbatim
open TensorProduct

-- @@ L56-56 verbatim
open minkowskiMatrix

-- @@ L57-57 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L58-58 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L60-70 expanded
/-- The scalar potential of an electromagnetic potential which is a distribution. -/
noncomputable def scalarPotential {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ] Distribution ℝ (Time × Space d) ℝ
    where
  toFun A := Lorentz.Vector.temporalCLM d ∘L distTimeSlice c (c.val • A)
  map_add' A₁
    A₂ := by
    ext ε
    simp [distTimeSlice]
  map_smul' r
    A := by
    ext ε
    simp [distTimeSlice, mul_left_comm]


-- @@ L72-72 verbatim
end DistElectromagneticPotential

-- @@ L73-73 verbatim
end Electromagnetism
