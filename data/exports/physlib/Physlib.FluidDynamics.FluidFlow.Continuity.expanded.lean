/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.FluidFlow.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Div
public import Physlib.SpaceAndTime.Time.Derivatives

-- @@ L11-36 verbatim
/-!

# Continuity equation for fluid flows

## i. Overview

This module defines the classical conservative mass-balance equation for a fluid flow and the
corresponding continuity residual. These definitions are independent of a particular momentum
equation, so they can be reused by Navier-Stokes, Euler, and other fluid models.

## ii. Key results

- `FluidFlow.ClassicalContinuityEquation` : Classical conservation of mass in conservative form.
- `FluidFlow.continuityResidual` : The scalar residual `partial_t rho + div (rho u)`.
- `FluidFlow.SmoothContinuityEquation` : Continuity for globally differentiable fields.
- `FluidFlow.classicalContinuityEquation_of_smoothContinuityEquation` : A smooth continuity
  equation implies the classical continuity equation.

## iii. Table of contents

- A. Continuity equations

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


-- @@ L45-45 verbatim
namespace FluidFlow


-- @@ L47-51 verbatim
/-!

## A. Continuity equations

-/


-- @@ L53-61 expanded
/-- Classical conservation of mass in conservative form, `partial_t rho + div (rho u) = 0`.

The equation is asserted at points where the time derivative of `rho` and the spatial
divergence of `rho u` are classical derivatives.
-/
def ClassicalContinuityEquation (d : ℕ) (fluid : FluidFlow d) : Prop :=
  ∀ t x,
    DifferentiableAt ℝ (fluid.rho · x) t →
      DifferentiableAt ℝ (fun x' => fluid.rho t x' • fluid.velocity t x') x →
        deriv (fluid.rho · x) t + (div fun x' => fluid.rho t x' • fluid.velocity t x') x = 0


-- @@ L63-66 expanded
/-- The scalar continuity-equation residual
`partial_t rho + div (rho u)`. -/
noncomputable def continuityResidual (d : ℕ) (fluid : FluidFlow d) : Time → Space d → ℝ :=
  fun t x => deriv (fluid.rho · x) t + (div fun x' => fluid.rho t x' • fluid.velocity t x') x


-- @@ L68-77 verbatim
/-- A stronger continuity equation for globally differentiable fields.

This version records the first-order regularity needed by the classical continuity equation:
the density is differentiable in time, the mass flux `rho u` is differentiable in space, and
the continuity residual vanishes everywhere.
-/
def SmoothContinuityEquation (d : ℕ) (fluid : FluidFlow d) : Prop :=
  (∀ x, Differentiable ℝ (fluid.rho · x)) ∧
    (∀ t, Differentiable ℝ (fun x => fluid.rho t x • fluid.velocity t x)) ∧
      ∀ t x, continuityResidual d fluid t x = 0


-- @@ L79-84 verbatim
/-- A smooth continuity equation satisfies the guarded classical continuity equation. -/
lemma classicalContinuityEquation_of_smoothContinuityEquation
    (d : ℕ) (fluid : FluidFlow d) :
    SmoothContinuityEquation d fluid → ClassicalContinuityEquation d fluid := by
  intro hSmooth t x _ _
  simpa [continuityResidual] using hSmooth.2.2 t x


-- @@ L86-86 verbatim
end FluidFlow


-- @@ L88-88 verbatim
end FluidDynamics
