/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.PropertyT
import LeanPool.ConnesRigidity.Paper.Section7.TheoremACompletion
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


-- @@ L16-18 verbatim
/-!
Completion boundary for Zhou's Theorem A.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Connes


-- @@ L24-24 verbatim
universe v


-- @@ L26-37 verbatim
/-- Zhou's Theorem A. The only external mathematical input is the cited EJZK
property-(T) theorem for `EL₃(𝔽₂[t])`; every construction and all other
paper arguments are proved in this project. Paper: §7. -/
theorem theoremA
    (hEJZK : HasKazhdanPropertyT.{0, v} PaperPropertyT.elementaryGroup) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT.{0, v} Γ₁ ∧ HasKazhdanPropertyT.{0, v} Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  exact PaperTheoremACompletion.theoremA
    ⟨hEJZK⟩


-- @@ L39-39 verbatim
end Connes
