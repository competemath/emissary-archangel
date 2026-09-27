/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.DedekindZeta


-- @@ L11-11 verbatim
/-! TODO: Add doc-string. -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Complex NumberField NumberField.InfinitePlace


-- @@ L19-19 verbatim
namespace NumberField.Odlyzko


-- @@ L21-21 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L23-25 verbatim
/-- A discriminant factor used in the Odlyzko-bound argument. -/
def CompletedZeta.discriminantFactor (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)


-- @@ L27-29 verbatim
/-- An archimedean factor used in the Odlyzko-bound argument. -/
def CompletedZeta.archimedeanFactor (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ nrRealPlaces K * (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K


-- @@ L31-33 verbatim
/-- A completed used in the Odlyzko-bound argument. -/
def CompletedZeta.completed (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s * CompletedZeta.archimedeanFactor K s * dedekindZeta K s


-- @@ L35-36 verbatim
theorem discr_abs_pos : 0 < |(discr K : ℝ)| := by
  exact abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))


-- @@ L38-41 verbatim
theorem dedekindDiscriminantFactor_ne_zero (s : ℂ) :
    CompletedZeta.discriminantFactor K s ≠ 0 := by
  rw [CompletedZeta.discriminantFactor, cpow_ne_zero_iff]
  exact Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')


-- @@ L43-47 verbatim
theorem differentiable_dedekindDiscriminantFactor :
    Differentiable ℂ (CompletedZeta.discriminantFactor K) := by
  unfold CompletedZeta.discriminantFactor
  exact (differentiable_id.div_const _).const_cpow <|
    Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')


-- @@ L49-49 verbatim
end NumberField.Odlyzko
