/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.UniversalHenselNumerator
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum


-- @@ L11-17 verbatim
/-!
# Universal numerator recurrence acceptance clients

The nonlinear equation `V² + 2V - U = 0` distinguishes the first two numerators and tests
both omission of the current coefficient and the zero constant prefix. Reduction modulo two
checks that naturality requires no injectivity and remains a ring identity at a zero slope.
-/


-- @@ L19-19 verbatim
open Polynomial Polynomial.UniversalHenselNumerator


-- @@ L21-22 verbatim
private noncomputable def shifted : Polynomial (Polynomial ℤ) :=
  X ^ 2 + C 2 * X - C X


-- @@ L24-26 verbatim
example : numerators shifted 2 2 1 = 1 := by
  norm_num [numerators_succ, numeratorStep, residualTerm, positivePrefix,
    shifted, Finset.sum_range_succ]


-- @@ L28-30 verbatim
private theorem second_numerator : numerators shifted 2 2 2 = -1 := by
  norm_num [numerators_succ, numeratorStep, residualTerm, positivePrefix,
    shifted, Finset.sum_range_succ, coeff_X, coeff_one, coeff_monomial]


-- @@ L32-35 verbatim
example : numerators (shifted.map (mapRingHom (Int.castRingHom (ZMod 2)))) 0 2 2 = 1 := by
  have h := numerators_map (Int.castRingHom (ZMod 2)) shifted 2 2 2
  norm_num [second_numerator] at h
  exact h.symm


-- @@ L37-38 verbatim
example : (positivePrefix (fun i ↦ (i + 7 : ℤ)) 3).coeff 0 = 0 := by
  simp [positivePrefix_coeff]
