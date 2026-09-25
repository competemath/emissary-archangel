/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

-- @@ L9-18 verbatim
/-!

# Plane waves

We define plane waves as a member of the dual of the Schwartz submodule of the 1d Hilbert space.

This module has been generalized to d-dimensions in
`QuantumMechanics/HilbertSpaces/SpaceD/MomentumStates.lean` and will be removed in the near future.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace QuantumMechanics


-- @@ L24-24 verbatim
namespace OneDimension


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace HilbertSpace

-- @@ L29-29 verbatim
open MeasureTheory SchwartzMap TemperedDistribution


-- @@ L31-37 verbatim
/-- Plane waves as a member of the dual of the
  Schwartz submodule of the Hilbert space.

  For a given `k` this corresponds to the plane wave
  `exp (2π I k x)`. -/
def planewaveFunctional (k : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (TemperedDistribution.delta k : SchwartzMap ℝ ℂ →L[ℂ] ℂ) ∘L (SchwartzMap.fourierTransformCLM ℂ)


-- @@ L39-41 verbatim
open FourierTransform in
lemma planewaveFunctional_apply (k : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    planewaveFunctional k ψ = 𝓕 ψ k := rfl


-- @@ L43-48 verbatim
/-- Two elements of the Schwartz submodule are equal if and only if they are equal on
  all applications of `planewaveFunctional`. -/
lemma eq_of_eq_planewaveFunctional {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ k, planewaveFunctional k ψ1 = planewaveFunctional k ψ2) :
    ψ1 = ψ2 :=
  (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective (SchwartzMap.ext h)


-- @@ L50-50 verbatim
end HilbertSpace

-- @@ L51-51 verbatim
end

-- @@ L52-52 verbatim
end OneDimension

-- @@ L53-53 verbatim
end QuantumMechanics
