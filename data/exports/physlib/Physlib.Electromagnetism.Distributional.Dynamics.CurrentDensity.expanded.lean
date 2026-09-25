/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

-- @@ L9-36 verbatim
/-!

# The Lorentz Current Density

## i. Overview

In this module we define the Lorentz current density
and its decomposition into charge density and current density.
The Lorentz current density is often called the four-current and given then the symbol `J`.

The current density is given in terms of the charge density `ρ` and the current density
` \vec j` as `J = (c ρ, \vec j)`.

## ii. Key results

- `DistLorentzCurrentDensity` : The type of Lorentz current densities
  as distributions.

## iii. Table of contents

- A. The Lorentz current density as a distribution
  - A.1. The underlying charge density
  - A.2. The underlying current density

## iv. References

* None.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
namespace Electromagnetism

-- @@ L41-41 verbatim
open TensorSpecies

-- @@ L42-42 verbatim
open SpaceTime

-- @@ L43-43 verbatim
open TensorProduct

-- @@ L44-44 verbatim
open minkowskiMatrix

-- @@ L45-45 verbatim
open InnerProductSpace


-- @@ L47-47 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L48-48 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L50-54 verbatim
/-!

## A. The Lorentz current density as a distribution

-/

-- @@ L55-56 expanded
/-- The Lorentz current density, also called four-current as a distribution. -/
abbrev DistLorentzCurrentDensity (d : ℕ := 3) :=
  Distribution ℝ (SpaceTime d) (Lorentz.Vector d)


-- @@ L58-58 verbatim
namespace DistLorentzCurrentDensity


-- @@ L60-64 verbatim
/-!

### A.1. The underlying charge density

-/


-- @@ L66-74 expanded
/-- The charge density underlying a Lorentz current density which is a distribution. -/
noncomputable def chargeDensity {d : ℕ} (c : SpeedOfLight) :
    (DistLorentzCurrentDensity d) →ₗ[ℝ] Distribution ℝ (Time × Space d) ℝ
    where
  toFun J := (1 / (c : ℝ)) • (Lorentz.Vector.temporalCLM d ∘L distTimeSlice c J)
  map_add' J1 J2 := by simp
  map_smul' r
    J := by
    simp only [one_div, map_smul, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply]
    rw [smul_comm]


-- @@ L76-80 verbatim
/-!

### A.2. The underlying current density

-/


-- @@ L82-90 expanded
/-- The underlying (non-Lorentz) current density associated with a distributive
  Lorentz current density. -/
noncomputable def currentDensity (c : SpeedOfLight) :
    DistLorentzCurrentDensity d →ₗ[ℝ] Distribution ℝ (Time × Space d) (EuclideanSpace ℝ (Fin d))
    where
  toFun J := Lorentz.Vector.spatialCLM d ∘L distTimeSlice c J
  map_add' J1 J2 := by simp
  map_smul' r J := by simp


-- @@ L92-92 verbatim
end DistLorentzCurrentDensity

-- @@ L93-93 verbatim
end Electromagnetism
