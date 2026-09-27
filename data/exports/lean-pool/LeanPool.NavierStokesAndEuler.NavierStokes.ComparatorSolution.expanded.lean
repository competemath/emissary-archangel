/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorDefinitions
import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorR3Theorem
import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorTheorem


-- @@ L13-18 verbatim
/-!
# Navier–Stokes Comparator submission: options (C) and (D)

Expose the project's proof adapters under the reference theorem names.
The adapters import `ComparatorDefinitions`, never the challenge module.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
namespace NavierStokes.Comparator


-- @@ L25-25 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L27-32 verbatim
/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu


-- @@ L34-39 verbatim
/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu


-- @@ L41-41 verbatim
end NavierStokes.Comparator
