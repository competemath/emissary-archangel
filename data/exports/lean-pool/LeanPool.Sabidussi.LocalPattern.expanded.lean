/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import LeanPool.Sabidussi.Color
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L17-23 verbatim
/-!
# Local difference patterns

For every number `n + 2` of transition occurrences we construct three admissible local patterns.
The construction is the degree-splitting step of the manuscript written without changing the
graph: remove pairs of occurrences recursively, ending with a pair or a triple.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace Sabidussi


-- @@ L29-29 verbatim
open scoped BigOperators


-- @@ L31-32 verbatim
/-- A fixed enumeration of the three nonzero colours. -/
def choiceColor (c : Fin 3) : Color := tripleDifference (1, 0) c


-- @@ L34-36 verbatim
theorem choiceColor_ne_zero (c : Fin 3) : choiceColor c ≠ 0 := by
  apply tripleDifference_ne_zero
  norm_num [Prod.ext_iff]


-- @@ L38-39 verbatim
theorem sum_choiceColor : ∑ c, choiceColor c = 0 := by
  exact sum_tripleDifference (1, 0)


-- @@ L41-44 verbatim
theorem sum_tripleDifference_choice (i : Fin 3) :
    ∑ c, tripleDifference (choiceColor c) i = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, choiceColor, tripleDifference, Prod.ext_iff]


-- @@ L46-53 verbatim
/-- Three local patterns on `n + 2` occurrences.  For `2` occurrences the difference is constant;
for `3` it is the anisotropic triple; every additional pair receives the same nonzero colour and
is then removed recursively. -/
def localDifference : (n : ℕ) → Fin 3 → Fin (n + 2) → Color
  | 0, c => doubleDifference (choiceColor c)
  | 1, c => tripleDifference (choiceColor c)
  | n + 2, c =>
      Fin.cases (choiceColor c) (Fin.cases (choiceColor c) (localDifference n c))


-- @@ L55-57 verbatim
@[simp]
theorem localDifference_zero (c : Fin 3) :
    localDifference 0 c = doubleDifference (choiceColor c) := rfl


-- @@ L59-61 verbatim
@[simp]
theorem localDifference_one (c : Fin 3) :
    localDifference 1 c = tripleDifference (choiceColor c) := rfl


-- @@ L63-71 verbatim
theorem localDifference_ne_zero (n : ℕ) (c : Fin 3) (i : Fin (n + 2)) :
    localDifference n c i ≠ 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact doubleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | one => exact tripleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact choiceColor_ne_zero c
      · exact choiceColor_ne_zero c


-- @@ L73-84 verbatim
theorem sum_localDifference_occurrences (n : ℕ) (c : Fin 3) :
    ∑ i, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact sum_doubleDifference (choiceColor c)
  | one => exact sum_tripleDifference (choiceColor c)
  | more n ih _ =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [localDifference, Fin.cases_zero, Fin.cases_succ]
      calc
        choiceColor c + (choiceColor c + ∑ i, localDifference n c i) =
            (choiceColor c + choiceColor c) + ∑ i, localDifference n c i := by abel
        _ = 0 := by rw [color_add_self, zero_add, ih]


-- @@ L86-94 verbatim
theorem sum_localDifference_choices (n : ℕ) (i : Fin (n + 2)) :
    ∑ c, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => fin_cases i <;> simpa [doubleDifference] using sum_choiceColor
  | one => exact sum_tripleDifference_choice i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact sum_choiceColor
      · exact sum_choiceColor


-- @@ L96-96 verbatim
end Sabidussi
