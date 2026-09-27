/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic


-- @@ L12-17 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Dirac

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Dirac`.
-/


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
namespace MeasureTheory.Measure

-- @@ L22-22 verbatim
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}


-- @@ L24-26 verbatim
@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]


-- @@ L28-28 verbatim
end MeasureTheory.Measure
