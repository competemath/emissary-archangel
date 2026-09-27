/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic


-- @@ L11-15 verbatim
/-!
# TODO

Rename `setLIntegral_congr` to `setLIntegral_congr_set`
-/


-- @@ L17-17 verbatim
public section


-- @@ L19-19 verbatim
open ENNReal


-- @@ L21-21 verbatim
namespace MeasureTheory

-- @@ L22-22 verbatim
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}


-- @@ L24-29 verbatim
lemma lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s,
  f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero sᶜ f hs,
    setLIntegral_congr_fun (f := f) (g := fun _ ↦ 0) hmes hf]
  simp


-- @@ L31-33 verbatim
lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]


-- @@ L35-35 verbatim
end MeasureTheory
