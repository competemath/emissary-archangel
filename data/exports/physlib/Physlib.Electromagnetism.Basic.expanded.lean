/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic

-- @@ L9-37 verbatim
/-!

# A. Electromagnetism

Electromagnetism describes electric and magnetic fields, their potentials and sources, and the
relations between them on space and spacetime. This module provides a compact foundational API used
by more specialized electromagnetism modules in Physlib.

## A.1. Main definitions

The module contains coordinate-level types for electric and magnetic fields, a spacetime vector
potential, charge and current densities, and the constants describing an electromagnetic system.
For an `EMSystem`, it also defines the speed of light and Coulomb's constant in terms of the vacuum
permittivity and permeability.

## A.2. Current status

The definitions here are intentionally lightweight. More developed APIs are organized under the
`Kinematics`, `Dynamics`, `Distributional`, `ThreeDimension`, and `Vacuum` subdirectories. The
abbreviations in this file remain useful as shared entry points while those APIs continue to
converge.

## A.3. Future work

Charge and current densities should be generalized to signed measures while remaining convenient
for integration and tensor notation. As the specialized APIs stabilize, overlapping legacy
interfaces should be consolidated without breaking the physical meaning of existing declarations.

-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace Electromagnetism


-- @@ L43-44 verbatim
/-- The electric field is a map from `(d + 1)`-dimensional spacetime to `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)


-- @@ L46-47 verbatim
/-- The magnetic field is a map from `(d + 1)`-dimensional spacetime to `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)


-- @@ L49-49 verbatim
open realLorentzTensor


-- @@ L51-52 expanded
/-- The vector potential of an electromagnetic field. -/
abbrev VectorPotential (d : ℕ := 3) :=
  SpaceTime d → ((realLorentzTensor d).Tensor (vecCons .up ![]))


-- @@ L54-59 verbatim
/-- The electric permittivity and the magnetic permeability of free space. -/
structure EMSystem where
  /-- The permittivity of free space. -/
  ε₀ : ℝ
  /-- The permeability of free space. -/
  μ₀ : ℝ


-- @@ L61-65 verbatim
TODO "Charge density and current density should be generalized to signed measures,
  in such a way
  that they are still easy to work with and can be integrated with tensor notation.
  See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/Maxwell's.20Equations"


-- @@ L67-68 verbatim
/-- The charge density. -/
abbrev ChargeDensity := Time → Space → ℝ


-- @@ L70-71 verbatim
/-- The current density. -/
abbrev CurrentDensity := Time → Space → EuclideanSpace ℝ (Fin 3)


-- @@ L73-73 verbatim
namespace EMSystem

-- @@ L74-74 verbatim
variable (𝓔 : EMSystem)

-- @@ L75-75 verbatim
open SpaceTime


-- @@ L77-78 verbatim
/-- The speed of light. -/
noncomputable def c : ℝ := 1/(√(𝓔.μ₀ * 𝓔.ε₀))


-- @@ L80-81 verbatim
/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)


-- @@ L83-83 verbatim
end EMSystem


-- @@ L85-85 verbatim
end Electromagnetism
