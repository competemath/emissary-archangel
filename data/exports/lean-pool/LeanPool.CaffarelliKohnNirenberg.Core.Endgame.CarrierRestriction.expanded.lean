/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem


-- @@ L12-16 verbatim
/-! # Restriction of indicated Morrey data

Smaller carriers retain the same numerical Morrey bound. Joint measurability
on a spatial-time strip gives globally measurable past-cylinder indications.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Set MeasureTheory

-- @@ L21-21 verbatim
open scoped ENNReal

-- @@ L22-22 verbatim
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


-- @@ L24-24 verbatim
noncomputable section

-- @@ L25-25 verbatim
namespace CKN.Core.Endgame


-- @@ L27-36 verbatim
/-- Restricting an indicated source cannot increase its Morrey norm. -/
theorem morreyNorm_indicator_mono_set {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} (hST : S ⊆ T) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (S.indicator f) ≤ morreyNorm P τ (T.indicator f) := by
  apply morreyNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _


-- @@ L38-49 verbatim
/-- Componentwise ball-Morrey membership restricts to any smaller carrier. -/
theorem morreyVecMem_mono_carrier {P τ : ℝ} (hP : 0 ≤ P)
    {S T : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    (hST : S ⊆ T) (hu : morreyVecMem P τ T u) : morreyVecMem P τ S u := by
  intro i
  apply lt_of_le_of_lt _ (hu i)
  apply morreyBallNorm_mono hP
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem (hST hz)]
  · rw [indicator_of_notMem hz, abs_zero]
    exact abs_nonneg _



-- @@ L52-52 verbatim
end CKN.Core.Endgame
