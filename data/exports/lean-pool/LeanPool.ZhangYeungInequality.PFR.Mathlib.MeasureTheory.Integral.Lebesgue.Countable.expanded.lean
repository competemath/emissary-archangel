/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable


-- @@ L12-17 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Countable

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Integral.Lebesgue.Countable`.
-/


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
open ENNReal


-- @@ L23-23 verbatim
namespace MeasureTheory

-- @@ L24-24 verbatim
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

-- @@ L25-27 verbatim
variable [MeasurableSingletonClass α]

-- TODO: Change RHS of `lintegral_fintype`

-- @@ L28-30 verbatim
lemma lintegral_eq_sum (μ : Measure α) (f : α → ℝ≥0∞) [Fintype α] :
    ∫⁻ x, f x ∂μ = ∑ x, μ {x} * f x := by
  simp_rw [lintegral_fintype, mul_comm]


-- @@ L32-36 verbatim
lemma lintegral_eq_tsum (μ : Measure α) (f : α → ℝ≥0∞) [Countable α] :
    ∫⁻ x, f x ∂μ = ∑' x, μ {x} * f x := by
  simp_rw [lintegral_countable', mul_comm]

-- TODO: Change RHS of `lintegral_finset`

-- @@ L37-39 verbatim
lemma setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]


-- @@ L41-47 verbatim
lemma lintegral_eq_single (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a,
  f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [← lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton,
    setLIntegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a)),
    lintegral_zero, add_zero]
  simp +contextual [Set.EqOn, ha]


-- @@ L49-49 verbatim
end MeasureTheory
