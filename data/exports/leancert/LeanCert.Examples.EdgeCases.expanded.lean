/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Interval
import LeanCert.Discovery
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.Optimization.Global


-- @@ L11-17 verbatim
/-!
# Edge Case Stress Tests

This file tests boundary conditions, singularities, and "tricky" mathematical
scenarios to ensure the library behaves safely (soundly) even when exact
answers are impossible.
-/


-- @@ L19-19 verbatim
namespace LeanCert.Examples.EdgeCases


-- @@ L21-21 verbatim
open LeanCert.Core

-- @@ L22-22 verbatim
open LeanCert.Engine

-- @@ L23-23 verbatim
open LeanCert.Engine.Optimization


-- @@ L25-28 verbatim
/-! ## 1. The "Division by Zero" Singularity

The checked interval evaluator rejects reciprocal domains containing zero.
-/


-- @@ L30-30 verbatim
def I_cross_zero : IntervalRat := ⟨-1, 1, by norm_num⟩


-- @@ L32-36 verbatim
theorem inv_zero_rejected :
    (match evalIntervalChecked (Expr.inv (Expr.var 0)) (fun _ => I_cross_zero) with
      | .error _ => true
      | .ok _ => false) = true := by
  native_decide


-- @@ L38-42 verbatim
/-! ## 2. The "Square Root of Negative" Edge Case

Mathlib defines `Real.sqrt x = 0` for `x < 0`. LeanCert's interval arithmetic
must respect this convention to remain sound with respect to the standard library.
-/


-- @@ L44-46 verbatim
def I_negative : IntervalRat := ⟨-5, -1, by norm_num⟩

-- sqrt(x) on [-5, -1] should contain 0 since Real.sqrt returns 0 for negative inputs

-- @@ L47-47 verbatim
def exprSqrt : Expr := Expr.sqrt (Expr.var 0)

-- @@ L48-51 verbatim
theorem exprSqrt_core : ExprSupportedCore exprSqrt :=
  ExprSupportedCore.sqrt (ExprSupportedCore.var 0)

-- The interval for sqrt on negative domain should be [0, something]

-- @@ L52-57 verbatim
theorem sqrt_neg_contains_zero :
    let result := LeanCert.Internal.Rational.evalTotalCore1 exprSqrt I_negative {}
    result.lo = 0 := by
  native_decide

-- sqrt(x) on [-1, 4] should evaluate to [0, ≤ 5] (conservative bound)

-- @@ L58-58 verbatim
def I_mixed : IntervalRat := ⟨-1, 4, by norm_num⟩


-- @@ L60-63 verbatim
theorem sqrt_mixed_contains_two :
    let result := LeanCert.Internal.Rational.evalTotalCore1 exprSqrt I_mixed {}
    result.lo = 0 ∧ result.hi ≥ 2 := by
  native_decide


-- @@ L65-76 verbatim
/-! ## 3. Root Finding: Tangential Roots (Multiplicity > 1)

Bisection relies on sign change (IVT). It works for crossings (x³) but fails
for touching roots (x²). This test confirms the library handles "no sign change"
correctly.

NOTE: Interval arithmetic overestimates: [-1, 1] * [-1, 1] = [-1, 1], not [0, 1].
So x² on [-1, 1] gives interval [-1, 1], which includes negative values.
This is sound (conservative) but not tight.
-/

-- x² touches 0 at x=0, but f(-1) > 0 and f(1) > 0.

-- @@ L77-79 verbatim
def exprX2 : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

-- Check that x² is bounded above by 1 on [-1, 1]

-- @@ L80-81 verbatim
theorem exprX2_core : ExprSupportedCore exprX2 :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)


-- @@ L83-86 expanded
theorem x_sq_bounded_above : ∀ x ∈ I_cross_zero, Expr.eval (fun _ => x) exprX2 ≤ (1 : ℚ) := by
  apply
      proveCore_forall_le_by_interval exprX2 exprX2_core I_cross_zero
        1
          -- On a non-negative interval, x² is correctly bounded below
           <;>
    leancert_verify_cert


-- @@ L87-87 verbatim
def I_positive : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L89-92 expanded
theorem x_sq_nonneg_on_positive : ∀ x ∈ I_positive, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprX2 := by
  apply
      proveCore_forall_ge_by_interval exprX2 exprX2_core I_positive
        0
          -- x³ on [-1, 1] spans zero
           <;>
    leancert_verify_cert


-- @@ L93-93 verbatim
def exprX3 : Expr := Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0))

-- @@ L94-98 verbatim
theorem exprX3_core : ExprSupportedCore exprX3 :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0)
    (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))

-- x³ can be positive or negative on [-1, 1]

-- @@ L99-102 verbatim
theorem x_cube_spans_zero :
    let result := LeanCert.Internal.Rational.evalTotalCore1 exprX3 I_cross_zero {}
    result.lo < 0 ∧ 0 < result.hi := by
  native_decide


-- @@ L104-114 verbatim
/-! ## 4. The "Sinc" Singularity at 0

sin(x)/x has a removable singularity at 0.
Checked evaluation rejects `Expr.div (sin x) x` on a box containing 0;
`Expr.sinc x` represents the removable extension and is safe there.

NOTE: sinc is not in ExprSupportedCore, so we test using checked evaluation
or direct evaluation.
-/

-- Method 1: Explicit division is rejected at zero.

-- @@ L115-115 verbatim
def exprSinDivX : Expr := Expr.mul (Expr.sin (Expr.var 0)) (Expr.inv (Expr.var 0))


-- @@ L117-123 verbatim
theorem sin_div_x_rejected_at_zero :
    (match evalIntervalChecked exprSinDivX (fun _ => I_cross_zero) with
      | .error _ => true
      | .ok _ => false) = true := by
  native_decide

-- Method 2: Sinc intrinsic (safe at 0) - tested via direct evaluation

-- @@ L124-126 verbatim
def exprSinc : Expr := Expr.sinc (Expr.var 0)

-- Verify sinc(0) = 1 semantically

-- @@ L127-130 verbatim
theorem sinc_at_zero : Expr.eval (fun _ => 0) exprSinc = 1 := by
  simp only [exprSinc, Expr.eval_sinc, Expr.eval_var, Real.sinc_zero]

-- Verify sinc is bounded using the checked evaluator.

-- @@ L131-135 verbatim
theorem sinc_bounded_check :
    (match evalIntervalChecked exprSinc (fun _ => I_cross_zero) with
    | .ok result => decide (result.lo ≥ -2 ∧ result.hi ≤ 2)
    | .error _ => false) = true := by
  native_decide


-- @@ L137-143 verbatim
/-! ## 5. Precision Stress Test (Deep Polynomial)

Deep composition of polynomials causes rational denominators to explode in size.
We test if the evaluator can handle depths that might choke naive implementations.
-/

-- A polynomial x^16 on [0.5, 1.0]

-- @@ L144-149 verbatim
def exprDeepPoly : Expr :=
  let x := Expr.var 0
  let x2 := Expr.mul x x
  let x4 := Expr.mul x2 x2
  let x8 := Expr.mul x4 x4
  Expr.mul x8 x8 -- x^16


-- @@ L151-156 verbatim
theorem exprDeepPoly_core : ExprSupportedCore exprDeepPoly :=
  let xc := ExprSupportedCore.var 0
  let x2c := ExprSupportedCore.mul xc xc
  let x4c := ExprSupportedCore.mul x2c x2c
  let x8c := ExprSupportedCore.mul x4c x4c
  ExprSupportedCore.mul x8c x8c


-- @@ L158-160 verbatim
def I_half_one : IntervalRat := ⟨1/2, 1, by norm_num⟩

-- x^16 on [0.5, 1] should be in [0, 1]

-- @@ L161-163 expanded
theorem deep_poly_bounded : ∀ x ∈ I_half_one, Expr.eval (fun _ => x) exprDeepPoly ≤ (1 : ℚ) := by
  apply proveCore_forall_le_by_interval exprDeepPoly exprDeepPoly_core I_half_one 1 <;>
    leancert_verify_cert


-- @@ L165-167 expanded
theorem deep_poly_nonneg : ∀ x ∈ I_half_one, (0 : ℚ) ≤ Expr.eval (fun _ => x) exprDeepPoly := by
  apply proveCore_forall_ge_by_interval exprDeepPoly exprDeepPoly_core I_half_one 0 <;>
    leancert_verify_cert


-- @@ L169-172 verbatim
/-! ## 6. The "Wiggle" Function

Test a function with oscillating behavior: x · sin(10x) on [0.1, 1].
-/


-- @@ L174-175 verbatim
def exprWiggle : Expr :=
  Expr.mul (Expr.var 0) (Expr.sin (Expr.mul (Expr.const 10) (Expr.var 0)))


-- @@ L177-180 verbatim
theorem exprWiggle_core : ExprSupportedCore exprWiggle :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0)
    (ExprSupportedCore.sin
      (ExprSupportedCore.mul (ExprSupportedCore.const 10) (ExprSupportedCore.var 0)))


-- @@ L182-184 verbatim
def I_wiggle : IntervalRat := ⟨1/10, 1, by norm_num⟩

-- The wiggle function is bounded: |x · sin(10x)| ≤ |x| ≤ 1

-- @@ L185-187 expanded
theorem wiggle_bounded : ∀ x ∈ I_wiggle, Expr.eval (fun _ => x) exprWiggle ≤ (1 : ℚ) := by
  apply proveCore_forall_le_by_interval exprWiggle exprWiggle_core I_wiggle 1 <;>
    leancert_verify_cert


-- @@ L189-191 expanded
theorem wiggle_bounded_below : ∀ x ∈ I_wiggle, (-1 : ℚ) ≤ Expr.eval (fun _ => x) exprWiggle := by
  apply proveCore_forall_ge_by_interval exprWiggle exprWiggle_core I_wiggle (-1) <;>
    leancert_verify_cert


-- @@ L193-199 verbatim
/-! ## 7. Type Safety of IntervalRat

The `IntervalRat` structure requires `lo ≤ hi` as a field, so invalid intervals
cannot be constructed. This is proven by the type system itself.
-/

-- This demonstrates that IntervalRat is always valid by construction

-- @@ L200-200 verbatim
example : ∀ I : IntervalRat, I.lo ≤ I.hi := fun I => I.le


-- @@ L202-205 verbatim
/-! ## 8. Zero-Dimensional Evaluation

Evaluating a constant expression (0 variables) on an empty domain.
-/


-- @@ L207-207 verbatim
def exprConst5 : Expr := Expr.const 5

-- @@ L208-211 verbatim
theorem exprConst5_core : ExprSupportedCore exprConst5 :=
  ExprSupportedCore.const 5

-- A constant function evaluates correctly

-- @@ L212-216 verbatim
theorem const_eval_correct :
    Expr.eval (fun _ => 0) exprConst5 = 5 := by
  simp only [exprConst5, Expr.eval_const, Rat.cast_ofNat]

-- Constant interval evaluation

-- @@ L217-217 verbatim
def I_any : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L219-222 verbatim
theorem const_interval_correct :
    let result := LeanCert.Internal.Rational.evalTotalCore1 exprConst5 I_any {}
    result.lo = 5 ∧ result.hi = 5 := by
  native_decide


-- @@ L224-229 verbatim
/-! ## 9. Dyadic Interval Evaluation

Test the dyadic (floating-point style) evaluator for performance comparison.
-/

-- Create a dyadic interval [0, 1]

-- @@ L230-233 verbatim
def I_unit_dyadic : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨1, 0⟩, by native_decide⟩  -- Dyadic 0 = 0 * 2^0, Dyadic 1 = 1 * 2^0

-- Evaluate using dyadic arithmetic (faster for deep expressions)

-- @@ L234-237 verbatim
theorem dyadic_x2_bounded :
    let result := LeanCert.Internal.Dyadic.evalUnchecked exprX2 (fun _ => I_unit_dyadic) {}
    result.lo.toRat ≥ 0 := by
  native_decide


-- @@ L239-241 verbatim
/-! ## 10. Global Optimization Edge Cases -/

-- Minimize x² on [-1, 1] - interval arithmetic gives conservative lower bound

-- @@ L242-245 verbatim
def box_sym : Box := [I_cross_zero]

-- Due to interval overestimation, the computed lower bound may be negative
-- But the upper bound should be correct

-- @@ L246-251 verbatim
theorem x2_max_correct :
    let result := globalMaximizeCore exprX2 box_sym {}
    result.bound.hi ≤ 1 := by
  native_decide

-- Test on a box where optimization is more precise

-- @@ L252-252 verbatim
def box_positive : Box := [I_positive]


-- @@ L254-259 verbatim
theorem x2_min_on_positive :
    let result := globalMinimizeCore exprX2 box_positive {}
    result.bound.lo ≥ 0 := by
  native_decide

-- Minimize x³ on [-1, 1] - minimum is at x = -1, value = -1

-- @@ L260-263 verbatim
theorem x3_min_at_neg_one :
    let result := globalMinimizeCore exprX3 box_sym {}
    result.bound.lo ≥ -1 := by
  native_decide


-- @@ L265-265 verbatim
end LeanCert.Examples.EdgeCases
