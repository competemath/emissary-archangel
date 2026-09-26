import NavierStokes.ComparatorR3Theorem
import NavierStokes.ComparatorTheorem


-- @@ L4-9 verbatim
/-!
# Navier–Stokes Comparator submission: options (C) and (D)

Expose the project's proof adapters under the reference theorem names.
The adapters import `ComparatorDefinitions`, never the challenge module.
-/


-- @@ L11-11 verbatim
namespace NavierStokes.Comparator


-- @@ L13-13 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L15-20 verbatim
/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu


-- @@ L22-27 verbatim
/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu


-- @@ L29-29 verbatim
end NavierStokes.Comparator


-- @@ L31-31 verbatim
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3

-- @@ L32-32 verbatim
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
