/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Probability.ConditionalProbability


-- @@ L11-16 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.ConditionalProbability

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.ConditionalProbability`.
-/


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
open MeasureTheory


-- @@ L22-23 verbatim
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}


-- @@ L25-25 verbatim
namespace ProbabilityTheory


-- @@ L27-33 verbatim
/--
The axiomatic definition of conditional probability derived from a measure-theoretic
one.
-/
lemma cond_real_apply (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]


-- @@ L35-45 verbatim
/-- The conditional probability measure of any finite measure on any set of positive
measure
is a probability measure. -/
theorem cond_isProbabilityMeasure_of_real {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  apply cond_isProbabilityMeasure_of_finite
  · intro h
    simp [measureReal_def, h] at hcs
  · intro h
    simp [measureReal_def, h] at hcs


-- @@ L47-47 verbatim
end ProbabilityTheory
