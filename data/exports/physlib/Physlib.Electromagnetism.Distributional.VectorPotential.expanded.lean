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

# The vector Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the vector potential, and prove lemmas about it.

Since `A` is relativistic it is a distribution of `SpaceTime d`, whilst
the vector potential is non-relativistic and is therefore a distribution of `Time` and `Space d`.

## ii. Key results

- `DistElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential which is a distribution.

## iii. Table of contents

- A. Vector potential for distributions

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace Electromagnetism

-- @@ L42-42 verbatim
open Module realLorentzTensor

-- @@ L43-43 verbatim
open TensorSpecies

-- @@ L44-44 verbatim
open Tensor


-- @@ L46-50 verbatim
/-!

## A. Vector potential for distributions

-/


-- @@ L52-52 verbatim
namespace DistElectromagneticPotential

-- @@ L53-53 verbatim
open TensorSpecies

-- @@ L54-54 verbatim
open Tensor

-- @@ L55-55 verbatim
open SpaceTime

-- @@ L56-56 verbatim
open TensorProduct

-- @@ L57-57 verbatim
open minkowskiMatrix SchwartzMap

-- @@ L58-58 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L59-59 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L61-69 expanded
/-- The vector potential of an electromagnetic potential which is a distribution. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ] Distribution ℝ (Time × Space d) (EuclideanSpace ℝ (Fin d))
    where
  toFun A := Lorentz.Vector.spatialCLM d ∘L distTimeSlice c A
  map_add' A₁ A₂ := by simp [distTimeSlice]
  map_smul' r A := by simp [distTimeSlice]


-- @@ L71-71 verbatim
end DistElectromagneticPotential


-- @@ L73-73 verbatim
end Electromagnetism
