/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
import LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real


-- @@ L13-18 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Real

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Real`.
-/


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
open Function Set

-- @@ L23-23 verbatim
open scoped ENNReal NNReal


-- @@ L25-25 verbatim
namespace MeasureTheory

-- @@ L26-27 verbatim
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}


-- @@ L29-31 verbatim
lemma _root_.MeasureTheory.Measure.ennreal_smul_real_apply
    (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp


-- @@ L33-35 verbatim
lemma _root_.MeasureTheory.Measure.nnreal_smul_real_apply
    (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by simp [Measure.real, NNReal.smul_def]


-- @@ L37-41 verbatim
lemma _root_.MeasureTheory.Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s,
      MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (Measure.comap f μ).real s = μ.real (f '' s) := by
  simp [Measure.real, Measure.comap_apply _ hfi hf μ hs]


-- @@ L43-47 verbatim
lemma _root_.MeasureTheory.Measure.prod_real_singleton
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x :
  α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]


-- @@ L49-49 verbatim
variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']


-- @@ L51-56 verbatim
lemma measureReal_preimage_fst_singleton_eq_sum [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all


-- @@ L58-63 verbatim
lemma measureReal_preimage_snd_singleton_eq_sum [Fintype Ω] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (y : Ω') :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : Ω, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all


-- @@ L65-65 verbatim
end MeasureTheory
