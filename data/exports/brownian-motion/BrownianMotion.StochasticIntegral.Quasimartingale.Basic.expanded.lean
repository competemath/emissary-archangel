/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.SimpleProcess
public import Mathlib.Probability.Notation


-- @@ L11-11 verbatim
/-! # Real quasimartingales -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open scoped ProbabilityTheory.SimpleProcess


-- @@ L18-18 verbatim
namespace ProbabilityTheory


-- @@ L20-22 verbatim
variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ}


-- @@ L24-26 verbatim
/-! ### Almost-sure regularity along countable time sets -/

-- todo: to be superceded by a more general `IsQuasimartingale`

-- @@ L27-33 expanded
/-- A real quasimartingale is a real-valued stochastic process that is adapted, integrable,
and has bounded variation. -/
structure IsRealQuasimartingale (𝓕 : Filtration ι mΩ) (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  adapted : Adapted 𝓕 X
  integrable : ∀ t, Integrable (X t) μ
  boundedVariation :
    ∀ t,
      ∃ C,
        ∀ S : ElementaryPredictableSet 𝓕,
          μ[(integral (ContinuousLinearMap.mul ℝ ℝ) (S.indicator (1 : ℝ)) X) t] ≤ C


-- @@ L35-38 expanded
/-- The minimal bound on the variation of the process. -/
noncomputable def variationBound (X : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (μ : Measure Ω) (t : ι) :
    ℝ :=
  ⨆ S : ElementaryPredictableSet 𝓕,
    μ[(integral (ContinuousLinearMap.mul ℝ ℝ) (S.indicator (1 : ℝ)) X) t]


-- @@ L40-46 expanded
lemma IsRealQuasimartingale.integral_indicator_le_variationBound (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (S : ElementaryPredictableSet 𝓕) :
    μ[(integral (ContinuousLinearMap.mul ℝ ℝ) (S.indicator (1 : ℝ)) X) t] ≤
      variationBound X 𝓕 μ t :=
  by
  unfold variationBound
  refine
    le_ciSup (f := fun S ↦ ∫ x, (integral (ContinuousLinearMap.mul ℝ ℝ) (S.indicator 1) X) t x ∂μ)
      ?_ S
  obtain ⟨C, hC⟩ := hX.boundedVariation t
  exact ⟨C, by simp [mem_upperBounds, hC]⟩


-- @@ L48-49 verbatim
lemma IsRealQuasimartingale.stronglyAdapted (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 X := hX.adapted.stronglyAdapted


-- @@ L51-52 verbatim
lemma IsRealQuasimartingale.measurable (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (X t) := (hX.adapted t).mono (𝓕.le t) le_rfl


-- @@ L54-54 verbatim
end ProbabilityTheory
