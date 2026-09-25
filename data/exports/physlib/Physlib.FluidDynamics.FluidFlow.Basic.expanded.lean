/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.Basic

-- @@ L9-37 verbatim
/-!

# Basic API for fluid flows

## i. Overview

This module defines `FluidFlow`, the kinematic and mass-transport layer of the fluid API.

The fluid API is split according to which physical processes require which data. Density and
velocity are sufficient at this first layer: they determine the mass flux, momentum density,
convective momentum flux, and material derivatives used in continuity and kinematic statements.

Stress, body force, and thermodynamic fields are deliberately excluded. Kinematic and
mass-transport statements do not require them, while adding them here would force those statements
to depend on unrelated dynamic or constitutive choices. The extension structures add such data
only at the layer where it becomes necessary.

## ii. Key results

- `FluidFlow` : The density and velocity fields of a fluid.

## iii. Table of contents

- A. Fluid-flow structure

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace FluidDynamics


-- @@ L43-47 verbatim
/-!

## A. Fluid-flow structure

-/


-- @@ L49-58 verbatim
/-- The density and velocity fields of a fluid on `d`-dimensional space.

These fields are the independent data needed for kinematics and mass transport. Quantities such as
mass flux, momentum density, and material acceleration are derived from them. Dynamic and
thermodynamic fields are introduced only by extension structures whose statements need them. -/
structure FluidFlow (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d


-- @@ L60-60 verbatim
namespace FluidFlow


-- @@ L62-62 verbatim
end FluidFlow


-- @@ L64-64 verbatim
end FluidDynamics
