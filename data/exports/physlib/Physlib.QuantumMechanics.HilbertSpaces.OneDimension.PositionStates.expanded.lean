/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

-- @@ L9-18 verbatim
/-!

# Position states

We define position state as a member of the dual of the Schwartz submodule of the 1d Hilbert space.

This module has been generalized to d-dimensions in
`QuantumMechanics/HilbertSpaces/SpaceD/PositionStates.lean` and will be removed in the near future.

-/


-- @@ L20-20 verbatim
@[expose] public section

-- @@ L21-21 verbatim
namespace QuantumMechanics


-- @@ L23-23 verbatim
namespace OneDimension


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace HilbertSpace

-- @@ L28-28 verbatim
open MeasureTheory SchwartzMap


-- @@ L30-32 verbatim
/-- Position state as a member of the dual of the
  Schwartz submodule of the Hilbert space. -/
def positionState (x : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := TemperedDistribution.delta x


-- @@ L34-35 verbatim
lemma positionState_apply (x : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    positionState x ψ = ψ x := rfl


-- @@ L37-43 verbatim
/-- Two elements of the `𝓢(ℝ, ℂ)` are equal if they
  are equal on all position states. -/
lemma eq_of_eq_positionState {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ x, positionState x ψ1 = positionState x ψ2) :
    ψ1 = ψ2 := by
  ext x
  exact h x


-- @@ L45-45 verbatim
end HilbertSpace

-- @@ L46-46 verbatim
end

-- @@ L47-47 verbatim
end OneDimension

-- @@ L48-48 verbatim
end QuantumMechanics
