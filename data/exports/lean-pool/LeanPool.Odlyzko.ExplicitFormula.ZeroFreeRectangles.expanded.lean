/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
import LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
import Mathlib.Tactic.ArithMult.Init


-- @@ L12-16 verbatim
/-!
# Zero Free Rectangles

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Complex NumberField Set


-- @@ L24-24 verbatim
namespace NumberField.Odlyzko


-- @@ L26-26 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L28-34 verbatim
theorem poleClearedCompletedDedekindZetaContinuation_ne_zero_of_re_lt_zero
    {s : ℂ} (hs : s.re < 0) :
    poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
  rw [poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
  apply poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
  simp only [sub_re, one_re]
  linarith


-- @@ L36-36 verbatim
end NumberField.Odlyzko
