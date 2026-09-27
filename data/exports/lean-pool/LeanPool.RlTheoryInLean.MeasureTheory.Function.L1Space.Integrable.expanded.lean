/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable


-- @@ L10-12 verbatim
/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Function.L1Space.Integrable
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open Filter


-- @@ L18-18 verbatim
namespace MeasureTheory

-- @@ L19-19 verbatim
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]


-- @@ L21-28 verbatim
lemma integrable_of_norm_le {α : Type*} {β : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] [NormedAddCommGroup β] {f : α → β}
  (hm : AEStronglyMeasurable f μ) (hbdd : ∃ C, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C)
  : Integrable f μ := by
  obtain ⟨C, hC⟩ := hbdd
  apply integrable_of_norm_sub_le (f₀ := 0) (g := fun ω => C) hm (integrable_const _)
    (integrable_const _)
  exact hC.mono fun ω hω => by simp [hω]


-- @@ L30-39 verbatim
lemma Integrable.finset_sum
  {α ι : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι} {f : ι → α → ℝ}
  (hf : ∀ i ∈ s, Integrable (f i) μ) :
  Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_all


-- @@ L41-41 verbatim
end MeasureTheory
