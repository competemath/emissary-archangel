/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Positivity.Finset

-- @@ L12-14 verbatim
/-!
# LeanPool.SelbergSieve4.ForMathlib.Basic
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Aux


-- @@ L20-22 verbatim
open BigOperators ArithmeticFunction
/- Lemmas in this file are singled out as suitable for addition to Mathlib with minor
modifications. -/


-- @@ L24-24 verbatim
variable {R : Type*}


-- @@ L26-31 verbatim
theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : ArithmeticFunction R)
    (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp


-- @@ L33-37 verbatim
theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]


-- @@ L39-39 verbatim
end Aux
