/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Layercake


-- @@ L11-23 verbatim
/-!
# Tail Layer-Cake Formula

A real-valued specialization of the layer-cake formula for nonnegative random variables.

## Main definitions

This module introduces no new definitions.

## Main results

* `lintegral_eq_lintegral_tail`: a nonnegative function is the integral of its upper tails.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace LeanPool


-- @@ L29-29 verbatim
open MeasureTheory Set Real Filter Topology

-- @@ L30-30 verbatim
open scoped ENNReal NNReal BigOperators


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
variable {Ω : Type*} [MeasurableSpace Ω]


-- @@ L36-41 verbatim
/-- The expected value of a non-negative random variable equals the integral
    of its tail probabilities. This is the layer-cake formula. -/
theorem lintegral_eq_lintegral_tail {μ : Measure Ω} {X : Ω → ℝ}
    (hX_meas : AEMeasurable X μ) (hX_nonneg : 0 ≤ᵐ[μ] X) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∫⁻ t in Ioi 0, μ {ω | t ≤ X ω} :=
  lintegral_eq_lintegral_meas_le μ hX_nonneg hX_meas



-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
end LeanPool
