/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Trace
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic


-- @@ L11-17 verbatim
/-!

# Density-operator states

Construction of states from positive trace-one continuous linear endomorphisms.

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open ComplexOrder ContinuousLinearMap


-- @@ L23-23 verbatim
namespace UnitalPositiveLinearMap


-- @@ L25-25 verbatim
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- @@ L26-26 verbatim
variable {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)


-- @@ L28-30 expanded
/-- A trace-one positive continuous linear map defines a state. -/
noncomputable def ofDensity : UnitalPositiveLinearMap ℂ (H →L[ℂ] H) ℂ :=
  { ρ.traceMulOpₚ with map_one' := by simp_all }


-- @@ L32-36 verbatim
@[simp]
lemma ofDensity_apply {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ)
    (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) (x : H →L[ℂ] H) :
    ofDensity hpos hnorm x = (↑x * ↑ρ : H →ₗ[ℂ] H).trace ℂ H :=
  ρ.traceMulOpₚ_apply_of_nonneg hpos x


-- @@ L38-38 verbatim
end UnitalPositiveLinearMap
