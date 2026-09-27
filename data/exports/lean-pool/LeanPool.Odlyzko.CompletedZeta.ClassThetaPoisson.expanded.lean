/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

public import LeanPool.Odlyzko.Theta.TraceDualIdeal
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.ArithMult.Init


-- @@ L17-17 verbatim
/-! TODO: Add doc-string. -/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Complex NumberField NumberField.InfinitePlace

-- @@ L24-24 verbatim
open scoped nonZeroDivisors


-- @@ L26-26 verbatim
namespace NumberField.Odlyzko



-- @@ L29-29 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L31-37 verbatim
open Classical in
/-- A fractional shape covolume constant used in the Odlyzko-bound argument. -/
noncomputable def fractionalShapeCovolumeConstant
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  FractionalIdeal.absNorm
      (I : FractionalIdeal (𝓞 K)⁰ K) *
    √|discr K|


-- @@ L39-49 verbatim
omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeCovolumeConstant_traceDual
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalShapeCovolumeConstant K (traceDualIdealUnit K I) =
      (fractionalShapeCovolumeConstant K I)⁻¹ := by
  rw [fractionalShapeCovolumeConstant,
    fractionalShapeCovolumeConstant,
    absNorm_traceDualIdealUnit, absNorm_traceDual_one]
  push_cast
  grind


-- @@ L51-51 verbatim
end NumberField.Odlyzko
