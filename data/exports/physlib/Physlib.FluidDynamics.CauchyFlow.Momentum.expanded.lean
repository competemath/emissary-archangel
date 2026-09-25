/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.FluidDynamics.CauchyFlow.Basic
public import Physlib.FluidDynamics.FluidFlow.Momentum

-- @@ L10-37 verbatim
/-!

# Cauchy momentum equations

## i. Overview

This module defines the conservative and convective Cauchy momentum equations for a fluid flow
with stress and specific body-force fields. The stress tensor is left as an input field, so this
is the balance-law layer before specializing to a constitutive law, such as Euler or
Navier-Stokes.

## ii. Key results

- `CauchyFlow.CauchyMomentumEquation` : Conservation of momentum using `Space.matrixDiv`.
- `CauchyFlow.ConvectiveCauchyMomentumEquation` : The Cauchy momentum equation in convective
  form.
- `CauchyFlow.cauchyMomentumEquation_iff_convectiveCauchyMomentumEquation` : Equivalence of the
  two Cauchy momentum equations when continuity holds and the fields are differentiable.

## iii. Table of contents

- A. Cauchy momentum equations
- B. Equivalence of conservative and convective Cauchy momentum

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
open Space

-- @@ L42-42 verbatim
open Time


-- @@ L44-44 verbatim
namespace FluidDynamics


-- @@ L46-46 verbatim
namespace CauchyFlow


-- @@ L48-52 verbatim
/-!

## A. Cauchy momentum equations

-/


-- @@ L54-66 expanded
/-- Conservation of momentum in conservative matrix-divergence form.

The equation is

`partial_t (rho u) + matrixDiv (rho u ⊗ u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a constitutive law.
-/
def CauchyMomentumEquation (d : ℕ) (flow : CauchyFlow d) : Prop :=
  ∀ t x,
    deriv (FluidFlow.momentumDensity d flow.toFluidFlow · x) t +
        matrixDiv d (FluidFlow.momentumFlux d flow.toFluidFlow t) x =
      matrixDiv d (flow.stress t) x + flow.rho t x • flow.specificBodyForce t x


-- @@ L68-79 verbatim
/-- Conservation of momentum in convective form.

The equation is

`rho (partial_t u + (u · ∇)u) = matrixDiv sigma + rho f`.

Here `stress` is intentionally not yet specialized to a constitutive law.
-/
def ConvectiveCauchyMomentumEquation (d : ℕ) (flow : CauchyFlow d) : Prop :=
  ∀ t x,
    flow.rho t x • FluidFlow.materialAcceleration d flow.toFluidFlow t x =
      matrixDiv d (flow.stress t) x + flow.rho t x • flow.specificBodyForce t x


-- @@ L81-85 verbatim
/-!

## B. Equivalence of conservative and convective Cauchy momentum

-/


-- @@ L87-113 expanded
/-- The conservative and convective Cauchy momentum equations are equivalent when the classical
continuity equation holds.

The differentiability assumptions are exactly the product-rule assumptions used to rewrite
`partial_t (rho u)` and `matrixDiv (rho u ⊗ u)`.
-/
lemma cauchyMomentumEquation_iff_convectiveCauchyMomentumEquation (d : ℕ) (flow : CauchyFlow d)
    (hContinuity : FluidFlow.ClassicalContinuityEquation d flow.toFluidFlow)
    (hRhoTime : ∀ t x, DifferentiableAt ℝ (flow.rho · x) t)
    (hVelocityTime : ∀ t x, DifferentiableAt ℝ (flow.velocity · x) t)
    (hMomentumDensity : ∀ t, Differentiable ℝ (FluidFlow.momentumDensity d flow.toFluidFlow t))
    (hVelocitySpace : ∀ t, Differentiable ℝ (flow.velocity t)) :
    CauchyMomentumEquation d flow ↔ ConvectiveCauchyMomentumEquation d flow :=
  by
  have conservative_eq_convective_lhs :
    ∀ t x,
      deriv (FluidFlow.momentumDensity d flow.toFluidFlow · x) t +
          matrixDiv d (FluidFlow.momentumFlux d flow.toFluidFlow t) x =
        flow.rho t x • FluidFlow.materialAcceleration d flow.toFluidFlow t x :=
    by
    intro t x
    have hResidual : FluidFlow.continuityResidual d flow.toFluidFlow t x = 0 := by
      simpa [FluidFlow.continuityResidual] using
        hContinuity t x (by simpa using hRhoTime t x) (hMomentumDensity t).differentiableAt
    rw [FluidFlow.momentumTransport_eq_materialAcceleration_add_continuityResidual d
        flow.toFluidFlow t x (hRhoTime t x) (hVelocityTime t x) (hMomentumDensity t)
        (hVelocitySpace t),
      hResidual, zero_smul, add_zero]
  exact
    ⟨fun h t x => (conservative_eq_convective_lhs t x).symm.trans (h t x), fun h t x =>
      (conservative_eq_convective_lhs t x).trans (h t x)⟩


-- @@ L115-115 verbatim
end CauchyFlow


-- @@ L117-117 verbatim
end FluidDynamics
