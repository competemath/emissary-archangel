/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner, Michał Mogielnicki
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Div

-- @@ L10-35 verbatim
/-!

# Incompressible fluid flows

## i. Overview

This module defines general incompressibility predicates for fluid flows. These predicates are
not tied to a particular equation of motion, so they can be reused later by incompressible
Navier-Stokes, incompressible Euler, and Bernoulli-style developments.

## ii. Key results

- `FluidFlow.incompressibilityResidual` : The divergence of the velocity field.
- `FluidFlow.ClassicalIncompressible` : Incompressibility guarded by velocity differentiability.
- `FluidFlow.SmoothIncompressible` : Incompressibility with globally differentiable velocity.
- `FluidFlow.classicalIncompressible_of_smoothIncompressible` : Smooth incompressibility implies
  classical incompressibility.

## iii. Table of contents

- A. Incompressibility predicates

## iv. References

* None.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
open Space


-- @@ L41-41 verbatim
namespace FluidDynamics


-- @@ L43-43 verbatim
namespace FluidFlow


-- @@ L45-49 verbatim
/-!

## A. Incompressibility predicates

-/


-- @@ L51-54 expanded
/-- The incompressibility residual, given by the divergence of the velocity field. -/
noncomputable def incompressibilityResidual (d : ℕ) (fluid : FluidFlow d) : Time → Space d → ℝ :=
  fun t x => (div (fluid.velocity t)) x


-- @@ L56-60 verbatim
/-- A classical incompressible flow has divergence-free velocity at points where the velocity
field is differentiable. -/
def ClassicalIncompressible (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x, DifferentiableAt ℝ (fluid.velocity t) x →
    incompressibilityResidual d fluid t x = 0


-- @@ L62-66 verbatim
/-- A smooth incompressible flow has globally differentiable velocity and vanishing
incompressibility residual everywhere. -/
def SmoothIncompressible (d : ℕ) (fluid : FluidFlow d) : Prop :=
  (∀ t, Differentiable ℝ (fluid.velocity t)) ∧
    ∀ t x, incompressibilityResidual d fluid t x = 0


-- @@ L68-73 verbatim
/-- A smooth incompressible flow is classically incompressible. -/
lemma classicalIncompressible_of_smoothIncompressible
    (d : ℕ) (fluid : FluidFlow d) :
    SmoothIncompressible d fluid → ClassicalIncompressible d fluid := by
  intro hSmooth t x _
  simpa [incompressibilityResidual] using hSmooth.2 t x


-- @@ L75-75 verbatim
end FluidFlow


-- @@ L77-77 verbatim
end FluidDynamics
