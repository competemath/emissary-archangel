/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
public import Physlib.FluidDynamics.FluidFlow.Newtonian

-- @@ L10-29 verbatim
/-!

# Newtonian stress law for Cauchy flows

## i. Overview

This module defines the Newtonian constitutive stress law for `CauchyFlow`.

## ii. Key results

- `CauchyFlow.IsNewtonian` : Predicate saying the Cauchy stress has Newtonian constitutive form.

## iii. Table of contents

- A. Newtonian Cauchy flows

## iv. References

* None.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
namespace FluidDynamics


-- @@ L35-35 verbatim
namespace CauchyFlow


-- @@ L37-41 verbatim
/-!

## A. Newtonian Cauchy flows

-/


-- @@ L43-50 verbatim
/-- A Cauchy flow is Newtonian when its stress tensor has the Newtonian constitutive form. -/
def IsNewtonian
    (d : ℕ) (flow : CauchyFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : Prop :=
  ∀ t x,
    flow.stress t x =
      FluidFlow.newtonianStressTensor d flow.toFluidFlow
        pressure shearViscosity secondViscosity t x


-- @@ L52-52 verbatim
end CauchyFlow


-- @@ L54-54 verbatim
end FluidDynamics
