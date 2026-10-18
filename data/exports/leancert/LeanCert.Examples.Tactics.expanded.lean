/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Interval
import Mathlib.Analysis.Complex.ExponentialBounds


-- @@ L9-32 verbatim
/-!
# Tactic Examples

This file demonstrates using LeanCert's interval arithmetic to prove
bounds on expressions.

## Verified Examples

All examples in this file are FULLY PROVED using interval arithmetic.
No sorry, no axioms beyond the standard Lean/Mathlib foundations.

## Computability Design

We have two evaluation strategies:

1. **Core (computable)**: For expressions in `ExprSupportedCore`
   (const, var, add, mul, neg, sin, cos), we use `LeanCert.Internal.Rational.evalTotalCore1`
   which is fully computable. The `interval_le`, `interval_ge`, etc.
   tactics work with `native_decide`.

2. **Extended (noncomputable)**: For expressions with `exp`, we use
   `LeanCert.Internal.Rational.evalUnchecked1` which requires noncomputable evaluation due to
   Real.exp floor/ceil bounds. These proofs use FTIA directly.
-/


-- @@ L34-34 verbatim
namespace LeanCert.Examples.Tactics


-- @@ L36-36 verbatim
open LeanCert.Core

-- @@ L37-37 verbatim
open LeanCert.Engine

-- @@ L38-38 verbatim
open LeanCert.Tactic


-- @@ L40-40 verbatim
/-! ### Basic interval bound examples -/


-- @@ L42-43 verbatim
/-- The expression x² -/
def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)


-- @@ L45-47 verbatim
/-- Proof that x² is in the core (computable) subset -/
theorem exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)


-- @@ L49-51 verbatim
/-- Proof that x² is supported -/
theorem exprXSq_supp : ADSupported exprXSq :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)


-- @@ L53-54 verbatim
/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L56-59 expanded
/-- Example: x² ≤ 1 for all x ∈ [0, 1] using the interval_le tactic.
    This uses the computable core evaluator with native_decide. -/
theorem xsq_le_one_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) := by
  apply proveCore_forall_le_by_interval exprXSq exprXSq_core I01 1 <;> leancert_verify_cert


-- @@ L61-63 expanded
/-- Example: 0 ≤ x² for all x ∈ [0, 1] using native_decide. -/
theorem zero_le_xsq_native : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq := by
  apply proveCore_forall_ge_by_interval exprXSq exprXSq_core I01 0 <;> leancert_verify_cert


-- @@ L65-76 verbatim
/-- Example: x² ≤ 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) := by
  intro x hx
  simp only [exprXSq, Expr.eval_mul, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hmul : x * x ≤ (1 : ℝ) := by
    calc x * x ≤ x * 1 := by apply mul_le_mul_of_nonneg_left h1 h0
      _ = x := mul_one x
      _ ≤ 1 := h1
  exact_mod_cast hmul


-- @@ L78-85 verbatim
/-- Example: 0 ≤ x² for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem zero_le_xsq : ∀ x ∈ I01, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprXSq := by
  intro x hx
  simp only [exprXSq, Expr.eval_mul, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hmul : (0 : ℝ) ≤ x * x := mul_nonneg h0 h0
  exact_mod_cast hmul


-- @@ L87-87 verbatim
/-! ### Trigonometric bounds -/


-- @@ L89-90 verbatim
/-- The expression sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)


-- @@ L92-94 verbatim
/-- Proof that sin(x) is in the core subset -/
theorem exprSin_core : ExprSupportedCore exprSin :=
  ExprSupportedCore.sin (ExprSupportedCore.var 0)


-- @@ L96-98 verbatim
/-- Proof that sin(x) is supported -/
theorem exprSin_supp : ADSupported exprSin :=
  ADSupported.sin (ADSupported.var 0)


-- @@ L100-102 expanded
/-- Example: sin(x) ≤ 1 for all x ∈ [0, 1] using native_decide. -/
theorem sin_le_one_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprSin ≤ (1 : ℚ) := by
  apply proveCore_forall_le_by_interval exprSin exprSin_core I01 1 <;> leancert_verify_cert


-- @@ L104-106 expanded
/-- Example: -1 ≤ sin(x) for all x ∈ [0, 1] using native_decide. -/
theorem neg_one_le_sin_native : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprSin := by
  apply proveCore_forall_ge_by_interval exprSin exprSin_core I01 (-1) <;> leancert_verify_cert


-- @@ L108-114 verbatim
/-- Example: sin(x) ≤ 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem sin_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprSin ≤ (1 : ℚ) := by
  intro x _hx
  simp only [exprSin, Expr.eval_sin, Expr.eval_var]
  have h := Real.sin_le_one x
  exact_mod_cast h


-- @@ L116-122 verbatim
/-- Example: -1 ≤ sin(x) for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem neg_one_le_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprSin := by
  intro x _hx
  simp only [exprSin, Expr.eval_sin, Expr.eval_var]
  have h := Real.neg_one_le_sin x
  exact_mod_cast h


-- @@ L124-124 verbatim
/-! ### Combined expressions -/


-- @@ L126-128 verbatim
/-- The expression x² + sin(x) -/
def exprXSqPlusSin : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.sin (Expr.var 0))


-- @@ L130-134 verbatim
/-- Proof that x² + sin(x) is in the core subset -/
theorem exprXSqPlusSin_core : ExprSupportedCore exprXSqPlusSin :=
  ExprSupportedCore.add
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    (ExprSupportedCore.sin (ExprSupportedCore.var 0))


-- @@ L136-140 verbatim
/-- Proof that x² + sin(x) is supported -/
theorem exprXSqPlusSin_supp : ADSupported exprXSqPlusSin :=
  ADSupported.add
    (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
    (ADSupported.sin (ADSupported.var 0))


-- @@ L142-144 expanded
/-- Example: x² + sin(x) ≤ 2 for all x ∈ [0, 1] using native_decide. -/
theorem xsq_plus_sin_le_two_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqPlusSin ≤ (2 : ℚ) :=
  by
  apply proveCore_forall_le_by_interval exprXSqPlusSin exprXSqPlusSin_core I01 2 <;>
    leancert_verify_cert


-- @@ L146-148 expanded
/-- Example: -1 ≤ x² + sin(x) for all x ∈ [0, 1] using native_decide. -/
theorem neg_one_le_xsq_plus_sin_native :
    ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprXSqPlusSin := by
  apply proveCore_forall_ge_by_interval exprXSqPlusSin exprXSqPlusSin_core I01 (-1) <;>
    leancert_verify_cert


-- @@ L150-161 verbatim
/-- Example: x² + sin(x) ≤ 2 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_plus_sin_le_two : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqPlusSin ≤ (2 : ℚ) := by
  intro x hx
  simp only [exprXSqPlusSin, Expr.eval_add, Expr.eval_mul, Expr.eval_sin, Expr.eval_var]
  have h1 : x * x ≤ (1 : ℝ) := by
    have := xsq_le_one x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have h2 : Real.sin x ≤ 1 := Real.sin_le_one x
  calc x * x + Real.sin x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num


-- @@ L163-174 verbatim
/-- Example: -1 ≤ x² + sin(x) for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem neg_one_le_xsq_plus_sin : ∀ x ∈ I01, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprXSqPlusSin := by
  intro x hx
  simp only [exprXSqPlusSin, Expr.eval_add, Expr.eval_mul, Expr.eval_sin, Expr.eval_var]
  have h1 : (0 : ℝ) ≤ x * x := by
    have := zero_le_xsq x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have h2 : (-1 : ℝ) ≤ Real.sin x := Real.neg_one_le_sin x
  have hsum : (-1 : ℝ) ≤ x * x + Real.sin x := by linarith
  exact_mod_cast hsum


-- @@ L176-176 verbatim
/-! ### Strict bounds -/


-- @@ L178-180 verbatim
/-- The expression x² - 2 -/
def exprXSqMinus2 : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))


-- @@ L182-186 verbatim
/-- Proof that x² - 2 is in the core subset -/
theorem exprXSqMinus2_core : ExprSupportedCore exprXSqMinus2 :=
  ExprSupportedCore.add
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
    (ExprSupportedCore.neg (ExprSupportedCore.const 2))


-- @@ L188-192 verbatim
/-- Proof that x² - 2 is supported -/
theorem exprXSqMinus2_supp : ADSupported exprXSqMinus2 :=
  ADSupported.add
    (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
    (ADSupported.neg (ADSupported.const 2))


-- @@ L194-197 expanded
/-- Example: x² - 2 < 0 for all x ∈ [0, 1] using native_decide.
    Since x² ≤ 1 on [0,1], we have x² - 2 ≤ -1 < 0. -/
theorem xsq_minus_two_lt_zero_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqMinus2 < (0 : ℚ) :=
  by
  apply proveCore_forall_lt_by_interval exprXSqMinus2 exprXSqMinus2_core I01 0 <;>
    leancert_verify_cert


-- @@ L199-209 verbatim
/-- Example: x² - 2 < 0 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem xsq_minus_two_lt_zero : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSqMinus2 < (0 : ℚ) := by
  intro x hx
  simp only [exprXSqMinus2, Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_const, Expr.eval_var]
  have h1 : x * x ≤ (1 : ℝ) := by
    have := xsq_le_one x hx
    simp only [exprXSq, Expr.eval_mul, Expr.eval_var] at this
    exact_mod_cast this
  have hlt : x * x + (-(2 : ℝ)) < (0 : ℝ) := by linarith
  exact_mod_cast hlt


-- @@ L211-211 verbatim
/-! ### Working with polynomials -/


-- @@ L213-219 verbatim
/-- The expression 2x² + 3x + 1 -/
def exprPoly : Expr :=
  Expr.add
    (Expr.add
      (Expr.mul (Expr.const 2) (Expr.mul (Expr.var 0) (Expr.var 0)))
      (Expr.mul (Expr.const 3) (Expr.var 0)))
    (Expr.const 1)


-- @@ L221-228 verbatim
/-- Proof that 2x² + 3x + 1 is in the core subset -/
theorem exprPoly_core : ExprSupportedCore exprPoly :=
  ExprSupportedCore.add
    (ExprSupportedCore.add
      (ExprSupportedCore.mul (ExprSupportedCore.const 2)
        (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)))
      (ExprSupportedCore.mul (ExprSupportedCore.const 3) (ExprSupportedCore.var 0)))
    (ExprSupportedCore.const 1)


-- @@ L230-237 verbatim
/-- Proof that 2x² + 3x + 1 is supported -/
theorem exprPoly_supp : ADSupported exprPoly :=
  ADSupported.add
    (ADSupported.add
      (ADSupported.mul (ADSupported.const 2)
        (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)))
      (ADSupported.mul (ADSupported.const 3) (ADSupported.var 0)))
    (ADSupported.const 1)


-- @@ L239-242 expanded
/-- Example: 2x² + 3x + 1 ≤ 6 for all x ∈ [0, 1] using native_decide.
    At x=1: 2 + 3 + 1 = 6. -/
theorem poly_le_six_native : ∀ x ∈ I01, Expr.eval (fun _ => x) exprPoly ≤ 6 := by
  apply proveCore_forall_le_by_interval exprPoly exprPoly_core I01 6 <;> leancert_verify_cert


-- @@ L244-247 expanded
/-- Example: 1 ≤ 2x² + 3x + 1 for all x ∈ [0, 1] using native_decide.
    At x=0: 0 + 0 + 1 = 1. -/
theorem one_le_poly_native : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprPoly := by
  apply proveCore_forall_ge_by_interval exprPoly exprPoly_core I01 1 <;> leancert_verify_cert


-- @@ L249-262 verbatim
/-- Example: 2x² + 3x + 1 ≤ 6 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem poly_le_six : ∀ x ∈ I01, Expr.eval (fun _ => x) exprPoly ≤ 6 := by
  intro x hx
  simp only [exprPoly, I01, IntervalRat.mem_def, Expr.eval_add, Expr.eval_mul,
             Expr.eval_const, Expr.eval_var] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hx2 : x * x ≤ 1 := by
    calc x * x ≤ x * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = x := mul_one x
      _ ≤ 1 := h1
  have hbound : (2 : ℝ) * (x * x) + (3 : ℝ) * x + 1 ≤ 6 := by linarith
  exact_mod_cast hbound


-- @@ L264-274 verbatim
/-- Example: 1 ≤ 2x² + 3x + 1 for all x ∈ [0, 1].
    Manual proof for reference. -/
theorem one_le_poly : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprPoly := by
  intro x hx
  simp only [exprPoly, I01, IntervalRat.mem_def, Expr.eval_add, Expr.eval_mul,
             Expr.eval_const, Expr.eval_var] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hx2_pos : (0 : ℝ) ≤ x * x := mul_nonneg h0 h0
  have h3x_pos : (0 : ℝ) ≤ 3 * x := by linarith
  have hbound : (1 : ℝ) ≤ (2 : ℝ) * (x * x) + (3 : ℝ) * x + 1 := by linarith
  exact_mod_cast hbound


-- @@ L276-281 verbatim
/-! ### Examples with exp (noncomputable)

Expressions containing `exp` use the extended evaluator `LeanCert.Internal.Rational.evalUnchecked1`,
which is noncomputable due to Real.exp floor/ceil bounds. These examples
demonstrate bounds using direct FTIA application rather than native_decide.
-/


-- @@ L283-284 verbatim
/-- The expression exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)


-- @@ L286-288 verbatim
/-- Proof that exp(x) is supported (but NOT in ExprSupportedCore) -/
theorem exprExp_supp : ADSupported exprExp :=
  ADSupported.exp (ADSupported.var 0)


-- @@ L290-302 verbatim
/-- Example: exp(x) ≤ 3 for all x ∈ [0, 1].
    Since exp(1) ≈ 2.718, this bound holds.
    This uses the extended evaluator and requires direct proof. -/
theorem exp_le_three : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) := by
  intro x hx
  simp only [exprExp, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp_of_le h1
  have he_bound : Real.exp 1 < 3 := by
    have hd9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlt : Real.exp x < (3 : ℝ) := lt_of_le_of_lt hexp he_bound
  exact_mod_cast le_of_lt hlt


-- @@ L304-312 verbatim
/-- Example: 1 ≤ exp(x) for all x ∈ [0, 1].
    Since exp(0) = 1 and exp is increasing, this holds. -/
theorem one_le_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprExp := by
  intro x hx
  simp only [exprExp, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hexp : Real.exp 0 ≤ Real.exp x := Real.exp_le_exp_of_le h0
  simp only [Real.exp_zero] at hexp
  exact_mod_cast hexp


-- @@ L314-315 verbatim
/-- The expression x + exp(x) -/
def exprXPlusExp : Expr := Expr.add (Expr.var 0) (Expr.exp (Expr.var 0))


-- @@ L317-319 verbatim
/-- Proof that x + exp(x) is supported -/
theorem exprXPlusExp_supp : ADSupported exprXPlusExp :=
  ADSupported.add (ADSupported.var 0) (ADSupported.exp (ADSupported.var 0))


-- @@ L321-332 verbatim
/-- Example: x + exp(x) ≤ 4 for all x ∈ [0, 1].
    x ≤ 1 and exp(x) ≤ 3, so x + exp(x) ≤ 4. -/
theorem x_plus_exp_le_four : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXPlusExp ≤ (4 : ℚ) := by
  intro x hx
  simp only [exprXPlusExp, Expr.eval_add, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h1 : x ≤ (1 : ℝ) := by simpa using hx.2
  have hexp : Real.exp x ≤ 3 := by
    have := exp_le_three x hx
    simp only [exprExp, Expr.eval_exp, Expr.eval_var] at this
    exact_mod_cast this
  have hbound : x + Real.exp x ≤ 4 := by linarith
  exact_mod_cast hbound


-- @@ L334-345 verbatim
/-- Example: 1 ≤ x + exp(x) for all x ∈ [0, 1].
    x ≥ 0 and exp(x) ≥ 1, so x + exp(x) ≥ 1. -/
theorem one_le_x_plus_exp : ∀ x ∈ I01, (1 : ℚ) ≤ Expr.eval (fun _ => x) exprXPlusExp := by
  intro x hx
  simp only [exprXPlusExp, Expr.eval_add, Expr.eval_exp, Expr.eval_var, I01, IntervalRat.mem_def] at *
  have h0 : (0 : ℝ) ≤ x := by simpa using hx.1
  have hexp : (1 : ℝ) ≤ Real.exp x := by
    have := one_le_exp x hx
    simp only [exprExp, Expr.eval_exp, Expr.eval_var] at this
    exact_mod_cast this
  have hbound : (1 : ℝ) ≤ x + Real.exp x := by linarith
  exact_mod_cast hbound


-- @@ L347-347 verbatim
end LeanCert.Examples.Tactics
