/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.Electromagnetism.Kinematics.MagneticField

-- @@ L9-21 verbatim
/-!

# Three-Dimensional Electromagnetism

This directory provides a three-dimensional, vector-calculus-facing layer for
electromagnetism.

The backend theory is formulated in a tensorial and dimension-general way.
Here we re-express the relevant constructions in the familiar language of
scalar and vector potentials, electric and magnetic fields, and spatial
derivatives.

-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Electromagnetism

-- @@ L26-26 verbatim
namespace ThreeDimension


-- @@ L28-28 verbatim
open Time

-- @@ L29-29 verbatim
open Space

-- @@ L30-30 verbatim
open ElectromagneticPotential


-- @@ L32-32 verbatim
variable (c : SpeedOfLight) (V : ElectromagneticPotential 3)


-- @@ L34-34 verbatim
local notation "φ" => V.scalarPotential c

-- @@ L35-35 verbatim
local notation "A" => V.vectorPotential c

-- @@ L36-36 verbatim
local notation "E" => V.electricField c


-- @@ L38-46 verbatim
/-!

# Fields from potentials

In this section we rewrite the electric and magnetic fields associated to an
electromagnetic potential in terms of the scalar and vector potentials, using
the standard vector-calculus expressions.

-/


-- @@ L48-50 verbatim
/-- The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`. -/
theorem electricField_eq_3D :
    E = fun t x => - ∇ (φ t) x - ∂ₜ (fun t => A t x) t := electricField_eq V


-- @@ L52-52 verbatim
local notation "B" => V.magneticField c


-- @@ L54-56 expanded
/-- The magnetic field written as the curl of the vector potential as `∇ ⨯ A`. -/
theorem magneticField_eq_3D : B = fun t x => (curl (A t)) x :=
  magneticField_eq V


-- @@ L58-58 verbatim
end ThreeDimension

-- @@ L59-59 verbatim
end Electromagnetism
