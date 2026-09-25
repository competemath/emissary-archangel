/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Div

-- @@ L10-32 verbatim
/-!

# Newtonian stress tensors for fluid flows

## i. Overview

This module defines the velocity gradient and Newtonian stress tensor associated to a
`FluidFlow`.

## ii. Key results

- `FluidFlow.velocityGradient` : The spatial velocity-gradient matrix.
- `FluidFlow.newtonianStressTensor` : The Newtonian stress tensor determined by pressure and
  viscosity.

## iii. Table of contents

- A. Newtonian stress tensor

## iv. References

* None.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open Space


-- @@ L38-38 verbatim
namespace FluidDynamics


-- @@ L40-40 verbatim
namespace FluidFlow


-- @@ L42-46 verbatim
/-!

## A. Newtonian stress tensor

-/


-- @@ L48-51 expanded
/-- The spatial velocity-gradient matrix, with entries `partial_j u_i`. -/
noncomputable def velocityGradient (d : ℕ) (flow : FluidFlow d) :
    Time → Space d → Matrix (Fin d) (Fin d) ℝ := fun t x i j =>
  (deriv j) (fun x' => flow.velocity t x' i) x


-- @@ L53-65 expanded
/-- The Newtonian stress tensor
`-p I + mu (grad u + grad u^T) + lambda (div u) I`.

The scalar fields are pressure, shear viscosity, and second viscosity.
-/
noncomputable def newtonianStressTensor (d : ℕ) (flow : FluidFlow d)
    (pressure shearViscosity secondViscosity : ScalarField d) : StressTensor d := fun t x =>
  (-(pressure t x)) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      shearViscosity t x •
        (velocityGradient d flow t x + Matrix.transpose (velocityGradient d flow t x)) +
    (secondViscosity t x * (div (flow.velocity t)) x) • (1 : Matrix (Fin d) (Fin d) ℝ)


-- @@ L67-67 verbatim
end FluidFlow


-- @@ L69-69 verbatim
end FluidDynamics
