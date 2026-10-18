/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Integrate
import LeanCert.Engine.Optimize
import LeanCert.Engine.RootFinding.Main
import LeanCert.Engine.IntervalEvalRefined
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


-- @@ L12-23 verbatim
/-!
# Numerics Examples

This file demonstrates numerical integration, optimization, and
root finding using LeanCert.

## Verified Integration Examples

The `integrateInterval_correct_n1` theorem is **FULLY PROVED** for the
supported expression subset {const, var, add, mul, neg, sin, cos}.
This demonstrates end-to-end verified numerical integration.
-/


-- @@ L25-25 verbatim
namespace LeanCert.Examples.Numerics


-- @@ L27-27 verbatim
open LeanCert.Core

-- @@ L28-28 verbatim
open LeanCert.Engine

-- @@ L29-29 verbatim
open MeasureTheory


-- @@ L31-31 verbatim
/-! ### Verified Integration Examples -/


-- @@ L33-34 verbatim
/-- The constant function 1 -/
def constOne : Expr := Expr.const 1


-- @@ L36-37 verbatim
/-- Proof that constOne is in the supported subset -/
theorem constOne_supported : ADSupported constOne := ADSupported.const 1


-- @@ L39-40 verbatim
/-- The identity function x -/
def identity : Expr := Expr.var 0


-- @@ L42-43 verbatim
/-- Proof that identity is supported -/
theorem identity_supported : ADSupported identity := ADSupported.var 0


-- @@ L45-46 verbatim
/-- The expression x² -/
def xSquared : Expr := Expr.mul (Expr.var 0) (Expr.var 0)


-- @@ L48-50 verbatim
/-- Proof that xSquared is supported -/
theorem xSquared_supported : ADSupported xSquared :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)


-- @@ L52-53 verbatim
/-- Unit interval for integration -/
def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L55-62 verbatim
/-!
### Example: Verified integration of constant function

For the constant function 1 over [0,1], the integral is exactly 1.
We can prove that our computed interval bound contains this value.

This uses the FULLY PROVED `integrateInterval_correct_n1` theorem.
-/


-- @@ L64-66 verbatim
/-- The computed interval bound for ∫₀¹ 1 dx -/
noncomputable def constOne_integral_bound : IntervalRat :=
  integrateInterval constOne unitInterval 1 (by norm_num)


-- @@ L68-76 verbatim
/-- Verified: the true integral ∫₀¹ 1 dx lies in our computed bound.
    This theorem has NO SORRY - it's a direct application of the
    fully-verified `integrateInterval_correct_n1`. -/
theorem constOne_integral_verified
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) constOne)
                               volume unitInterval.lo unitInterval.hi) :
    ∫ x in (unitInterval.lo : ℝ)..unitInterval.hi, Expr.eval (fun _ => x) constOne ∈
    constOne_integral_bound :=
  integrateInterval_correct_n1 constOne constOne_supported unitInterval hInt


-- @@ L78-83 verbatim
/-!
### Example: Verified integration of x²

For x² over [0,1], the true integral is 1/3.
Our interval bound is guaranteed to contain this value.
-/


-- @@ L85-87 verbatim
/-- The computed interval bound for ∫₀¹ x² dx -/
noncomputable def xSquared_integral_bound : IntervalRat :=
  integrateInterval xSquared unitInterval 1 (by norm_num)


-- @@ L89-95 verbatim
/-- Verified: the true integral ∫₀¹ x² dx lies in our computed bound. -/
theorem xSquared_integral_verified
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) xSquared)
                               volume unitInterval.lo unitInterval.hi) :
    ∫ x in (unitInterval.lo : ℝ)..unitInterval.hi, Expr.eval (fun _ => x) xSquared ∈
    xSquared_integral_bound :=
  integrateInterval_correct_n1 xSquared xSquared_supported unitInterval hInt


-- @@ L97-101 verbatim
/-!
### Example: Verified integration with sin

For sin(x) over [0, 1], we get verified bounds using the global [-1,1] bound.
-/


-- @@ L103-104 verbatim
/-- The expression sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)


-- @@ L106-108 verbatim
/-- Proof that sin(x) is supported -/
theorem exprSin_supported : ADSupported exprSin :=
  ADSupported.sin (ADSupported.var 0)


-- @@ L110-112 verbatim
/-- The computed interval bound for ∫₀¹ sin(x) dx -/
noncomputable def sin_integral_bound : IntervalRat :=
  integrateInterval exprSin unitInterval 1 (by norm_num)


-- @@ L114-120 verbatim
/-- Verified: the true integral ∫₀¹ sin(x) dx lies in our computed bound. -/
theorem sin_integral_verified
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) exprSin)
                               volume unitInterval.lo unitInterval.hi) :
    ∫ x in (unitInterval.lo : ℝ)..unitInterval.hi, Expr.eval (fun _ => x) exprSin ∈
    sin_integral_bound :=
  integrateInterval_correct_n1 exprSin exprSin_supported unitInterval hInt


-- @@ L122-126 verbatim
/-! ### Optimization examples

The optimization module (`LeanCert.Engine.Optimize`) is fully verified
with theorems like `minimizeInterval_correct` for the `ADSupported` subset.
-/


-- @@ L128-132 verbatim
/-- The expression x² - 2x + 1 = (x-1)² with minimum at x = 1 -/
def quadratic : Expr :=
  Expr.add (Expr.sub (Expr.mul (Expr.var 0) (Expr.var 0))
                     (Expr.mul (Expr.const 2) (Expr.var 0)))
           (Expr.const 1)


-- @@ L134-138 verbatim
/-! ### Root finding examples

The root finding module (`LeanCert.Engine.RootFinding.Main`) is fully verified
with all theorems proved including `newton_contraction_has_root` and bisection correctness.
-/


-- @@ L140-142 verbatim
/-- x² - 2 has root at √2 ≈ 1.414 -/
def xSquaredMinus2 : Expr :=
  Expr.sub (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 2)


-- @@ L144-145 verbatim
/-- Search interval for √2 -/
def searchInterval : IntervalRat := ⟨1, 2, by norm_num⟩


-- @@ L147-151 verbatim
/-- ADSupported proof for x² - 2 -/
theorem xSquaredMinus2_supported : ADSupported xSquaredMinus2 :=
  ADSupported.add
    (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
    (ADSupported.neg (ADSupported.const 2))


-- @@ L153-157 verbatim
/-! ### Bisection root finding example

For x² - 2, we know the root is √2 ∈ [1, 2]. We demonstrate bisection
and prove that when it reports `hasRoot`, there truly exists a root.
-/


-- @@ L159-161 verbatim
/-- Bisection result for x² - 2 on [1, 2] with 20 iterations and tol = 1/100 -/
noncomputable def sqrt2_bisect_result : BisectionResult :=
  bisectRoot xSquaredMinus2 searchInterval 20 (1/100) (by norm_num)


-- @@ L163-171 verbatim
/-- x² - 2 evaluates to a polynomial in x, which is continuous -/
theorem xSquaredMinus2_continuous :
    ContinuousOn (fun x => Expr.eval (fun _ => x) xSquaredMinus2) (Set.Icc searchInterval.lo searchInterval.hi) := by
  -- x² - 2 expands to x*x + (-2), which is just a polynomial
  simp only [xSquaredMinus2]
  -- Apply continuity: x*x - 2 is continuous
  apply ContinuousOn.sub
  · apply ContinuousOn.mul <;> exact continuousOn_id
  · exact continuousOn_const


-- @@ L173-180 verbatim
/-- Correctness: every interval marked `hasRoot` in bisection result contains a true root.
    This uses `bisectRoot_hasRoot_correct` from the verified bisection module. -/
theorem sqrt2_bisect_hasRoot_correct :
    ∀ J s, (J, s) ∈ sqrt2_bisect_result.intervals →
      s = RootStatus.hasRoot →
      ∃ x ∈ J, Expr.eval (fun _ => x) xSquaredMinus2 = 0 := by
  apply bisectRoot_hasRoot_correct xSquaredMinus2 xSquaredMinus2_supported
    searchInterval 20 (1/100) (by norm_num) xSquaredMinus2_continuous


-- @@ L182-186 verbatim
/-! ### Optimization example

The quadratic (x-1)² = x² - 2x + 1 has minimum value 0 at x = 1.
We demonstrate using minimizeInterval to get verified bounds.
-/


-- @@ L188-194 verbatim
/-- ADSupported proof for quadratic (x² - 2x + 1) -/
theorem quadratic_supported : ADSupported quadratic :=
  ADSupported.add
    (ADSupported.add
      (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
      (ADSupported.neg (ADSupported.mul (ADSupported.const 2) (ADSupported.var 0))))
    (ADSupported.const 1)


-- @@ L196-197 verbatim
/-- Interval [0, 2] for optimization -/
def I02 : IntervalRat := ⟨0, 2, by norm_num⟩


-- @@ L199-201 verbatim
/-- Minimization result for quadratic on [0, 2] -/
noncomputable def quad_min_result : OptResult :=
  minimizeInterval quadratic I02 0 5


-- @@ L203-211 verbatim
/-- UsesOnlyVar0 proof for quadratic -/
theorem quadratic_var0 : UsesOnlyVar0 quadratic :=
  -- quadratic = (x² - 2x) + 1 = add (add (mul x x) (neg (mul 2 x))) 1
  UsesOnlyVar0.add _ _
    (UsesOnlyVar0.add _ _
      (UsesOnlyVar0.mul _ _ UsesOnlyVar0.var0 UsesOnlyVar0.var0)
      (UsesOnlyVar0.neg _
        (UsesOnlyVar0.mul _ _ (UsesOnlyVar0.const 2) UsesOnlyVar0.var0)))
    (UsesOnlyVar0.const 1)


-- @@ L213-219 verbatim
/-- Correctness: the computed lower bound is indeed a lower bound on the true minimum.

    For all x in [0, 2], we have quad_min_result.valueBound.lo ≤ quadratic(x).
    This uses `minimizeInterval_correct` from the verified optimization module. -/
theorem quad_min_correct :
    ∀ x ∈ I02, (quad_min_result.valueBound.lo : ℝ) ≤ Expr.eval (fun _ => x) quadratic :=
  minimizeInterval_correct quadratic quadratic_supported quadratic_var0 I02 5


-- @@ L221-225 verbatim
/-! ### Inverse function example

The partial evaluator `evalInterval?` supports expressions with division (Expr.inv)
when the divisor interval excludes zero. This example demonstrates its usage.
-/


-- @@ L227-228 verbatim
/-- The expression 1/x (inverse of x) -/
def invX : Expr := Expr.inv (Expr.var 0)


-- @@ L230-231 verbatim
/-- Interval [1, 2] - excludes zero, so 1/x is safe to evaluate -/
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩


-- @@ L233-237 verbatim
/-- The interval [1, 2] doesn't contain zero -/
theorem I12_excludes_zero : ¬IntervalRat.containsZero I12 := by
  simp only [IntervalRat.containsZero, I12, not_and_or, not_le]
  left
  norm_num


-- @@ L239-242 verbatim
/-- Evaluation of 1/x on [1, 2] succeeds because the interval excludes zero -/
theorem invX_eval_some :
    evalInterval?1 invX I12 = some (IntervalRat.invNonzero ⟨I12, I12_excludes_zero⟩) := by
  simp only [evalInterval?1, evalInterval?, invX, I12_excludes_zero, ↓reduceDIte]


-- @@ L244-247 verbatim
/-- Evaluation succeeds -/
theorem invX_eval_succeeds : (evalInterval?1 invX I12).isSome := by
  rw [invX_eval_some]
  rfl


-- @@ L249-251 verbatim
/-- Get the bound result when evaluation succeeds -/
noncomputable def invX_bound : IntervalRat :=
  IntervalRat.invNonzero ⟨I12, I12_excludes_zero⟩


-- @@ L253-260 verbatim
/-- Correctness: if evaluation succeeds, the result contains the true value.

    For 1/x on [1, 2], we have 1/x ∈ [1/2, 1] (since x ∈ [1, 2] implies 1/x ∈ [1/2, 1]).
    The computed bound is guaranteed to contain this. -/
theorem invX_correct (x : ℝ) (hx : x ∈ I12) :
    Expr.eval (fun _ => x) invX ∈ invX_bound := by
  simp only [invX_bound]
  exact evalInterval?1_correct invX I12 _ invX_eval_some x hx


-- @@ L262-265 verbatim
/-! ### Refined evaluation example

The refined evaluators use Taylor models for tighter bounds on transcendentals.
-/


-- @@ L267-269 verbatim
/-- sin(x) on [0, 0.5] - the refined evaluator gives tighter bounds than [-1, 1] -/
noncomputable def sinSmall_refined : IntervalRat :=
  evalIntervalRefined1 exprSin exprSin_supported ⟨0, 1/2, by norm_num⟩


-- @@ L271-274 verbatim
/-- Correctness of refined evaluation -/
theorem sinSmall_refined_correct (x : ℝ) (hx : x ∈ (⟨0, 1/2, by norm_num⟩ : IntervalRat)) :
    Expr.eval (fun _ => x) exprSin ∈ sinSmall_refined :=
  evalIntervalRefined1_correct exprSin exprSin_supported x ⟨0, 1/2, by norm_num⟩ hx


-- @@ L276-276 verbatim
end LeanCert.Examples.Numerics
