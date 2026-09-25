/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Physlib.SpaceAndTime.Time.InnerProductSpace

-- @@ L10-36 verbatim
/-!

# Basic field types for fluid dynamics

## i. Overview

This module defines the basic field types used to describe a fluid on `d`-dimensional space.
The structure-specific APIs are organized in the corresponding `FluidFlow`, `CauchyFlow`, and
`ThermodynamicCauchyFlow` subdirectories.

## ii. Key results

- `ScalarField` : A time-dependent scalar field on space.
- `VectorField` : A time-dependent vector field on space.
- `MassDensity` : A time-dependent scalar density field.
- `VelocityField` : A time-dependent vector velocity field.
- `MomentumDensityField` : A time-dependent vector momentum density field.
- `StressTensor` : A time-dependent matrix-valued stress field.

## iii. Table of contents

- A. Field types

## iv. References

* None.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
open Space

-- @@ L41-41 verbatim
open Time


-- @@ L43-43 verbatim
namespace FluidDynamics


-- @@ L45-49 verbatim
/-!

## A. Field types

-/


-- @@ L51-52 verbatim
/-- A scalar field on `d`-dimensional space, depending on time. -/
abbrev ScalarField (d : ℕ) := Time → Space d → ℝ


-- @@ L54-55 verbatim
/-- A vector field on `d`-dimensional space, depending on time. -/
abbrev VectorField (d : ℕ) := Time → Space d → EuclideanSpace ℝ (Fin d)


-- @@ L57-58 verbatim
/-- A mass density field on `d`-dimensional space. -/
abbrev MassDensity (d : ℕ) := ScalarField d


-- @@ L60-61 verbatim
/-- A velocity field on `d`-dimensional space. -/
abbrev VelocityField (d : ℕ) := VectorField d


-- @@ L63-64 verbatim
/-- A momentum density field on `d`-dimensional space. -/
abbrev MomentumDensityField (d : ℕ) := VectorField d


-- @@ L66-67 verbatim
/-- A matrix-valued stress tensor field on `d`-dimensional space. -/
abbrev StressTensor (d : ℕ) := Time → Space d → Matrix (Fin d) (Fin d) ℝ


-- @@ L69-69 verbatim
end FluidDynamics
