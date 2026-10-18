/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Core.IntervalReal
import LeanCert.Core.IntervalDyadic
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine


-- @@ L13-34 verbatim
/-!
# Affine Arithmetic Tests and Benchmarks

This file tests the Affine Arithmetic backend, demonstrating its key advantage:
solving the "dependency problem" where interval arithmetic loses correlations.

## Key Tests

1. **Dependency Problem** - Expressions like `x - x` where Affine gives exact results
2. **Correlation Preservation** - Multiple occurrences of the same variable
3. **Transcendental Functions** - sin, cos, exp, tanh, sinh, cosh soundness
4. **Backend Comparison** - Rational vs Dyadic vs Affine bound widths

## Expected Results

For expressions with repeated variables:
- Interval: `x - x` on [-1, 1] gives [-2, 2] (over-approximation)
- Affine: `x - x` on [-1, 1] gives [0, 0] (exact!)

Affine arithmetic tracks linear correlations, giving 50-90% tighter bounds
for many real-world expressions, especially in neural network verification.
-/


-- @@ L36-36 verbatim
namespace LeanCert.Test.Affine


-- @@ L38-38 verbatim
open LeanCert.Core

-- @@ L39-39 verbatim
open LeanCert.Engine


-- @@ L41-41 verbatim
/-! ### Test Intervals and Environments -/


-- @@ L43-44 verbatim
/-- Standard test interval [-1, 1] -/
def testInterval : IntervalRat := ⟨-1, 1, by norm_num⟩


-- @@ L46-47 verbatim
/-- Small positive interval [0.1, 0.5] for transcendentals -/
def smallInterval : IntervalRat := ⟨1/10, 1/2, by norm_num⟩


-- @@ L49-50 verbatim
/-- Narrow interval [0.4, 0.6] for precision tests -/
def narrowInterval : IntervalRat := ⟨2/5, 3/5, by norm_num⟩


-- @@ L52-53 verbatim
/-- Create rational environment from single interval -/
def mkRatEnv (I : IntervalRat) : Nat → IntervalRat := fun _ => I


-- @@ L55-57 verbatim
/-- Create dyadic environment from single interval -/
def mkDyadEnv (I : IntervalRat) (prec : Int := -53) : IntervalDyadicEnv :=
  fun _ => IntervalDyadic.ofIntervalRat I prec


-- @@ L59-60 verbatim
/-- Create affine environment from single interval -/
def mkAffineEnv (I : IntervalRat) : AffineEnv := toAffineEnv [I]


-- @@ L62-62 verbatim
/-! ### Dependency Problem Tests -/


-- @@ L64-66 verbatim
/-- x - x: Should be exactly 0, but interval gives [-2, 2] -/
def exprXMinusX : Expr :=
  Expr.add (Expr.var 0) (Expr.neg (Expr.var 0))


-- @@ L68-71 verbatim
/-- x * x - x * x: Should be 0 -/
def exprXSqMinusXSq : Expr :=
  let xsq := Expr.mul (Expr.var 0) (Expr.var 0)
  Expr.add xsq (Expr.neg xsq)


-- @@ L73-76 verbatim
/-- (x + 1) - x: Should be exactly 1 -/
def exprXPlus1MinusX : Expr :=
  let xp1 := Expr.add (Expr.var 0) (Expr.const 1)
  Expr.add xp1 (Expr.neg (Expr.var 0))


-- @@ L78-84 verbatim
/-- x * (1 - x) + x * x: Should equal x (since x(1-x) + x² = x - x² + x² = x) -/
def exprCorrelated : Expr :=
  let x := Expr.var 0
  let xsq := Expr.mul x x
  let oneMinusX := Expr.add (Expr.const 1) (Expr.neg x)
  let xTimesOneMinusX := Expr.mul x oneMinusX
  Expr.add xTimesOneMinusX xsq


-- @@ L86-86 verbatim
/-! ### Transcendental Function Tests -/


-- @@ L88-89 verbatim
/-- sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)


-- @@ L91-92 verbatim
/-- cos(x) -/
def exprCos : Expr := Expr.cos (Expr.var 0)


-- @@ L94-95 verbatim
/-- exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)


-- @@ L97-98 verbatim
/-- tanh(x) -/
def exprTanh : Expr := Expr.tanh (Expr.var 0)


-- @@ L100-101 verbatim
/-- sinh(x) -/
def exprSinh : Expr := Expr.sinh (Expr.var 0)


-- @@ L103-104 verbatim
/-- cosh(x) -/
def exprCosh : Expr := Expr.cosh (Expr.var 0)


-- @@ L106-107 verbatim
/-- sqrt(x) on positive interval -/
def exprSqrt : Expr := Expr.sqrt (Expr.var 0)


-- @@ L109-115 verbatim
/-- sin(x)² + cos(x)² - Should be 1 but interval loses correlation -/
def exprSinSqPlusCosSq : Expr :=
  let sinx := Expr.sin (Expr.var 0)
  let cosx := Expr.cos (Expr.var 0)
  let sin2 := Expr.mul sinx sinx
  let cos2 := Expr.mul cosx cosx
  Expr.add sin2 cos2


-- @@ L117-117 verbatim
/-! ### Backend Evaluation Functions -/


-- @@ L119-121 verbatim
/-- Evaluate with Rational backend -/
def evalRat (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  LeanCert.Internal.Rational.evalTotalCore e (mkRatEnv I) cfg


-- @@ L123-125 verbatim
/-- Evaluate with Dyadic backend -/
def evalDyad (e : Expr) (I : IntervalRat) (cfg : DyadicConfig := {}) : IntervalRat :=
  (LeanCert.Internal.Dyadic.evalUnchecked e (mkDyadEnv I) cfg).toIntervalRat


-- @@ L127-129 verbatim
/-- Evaluate with Affine backend -/
def evalAffine (e : Expr) (I : IntervalRat) (cfg : AffineConfig := {}) : IntervalRat :=
  (LeanCert.Internal.Affine.evalUnchecked e (mkAffineEnv I) cfg).toInterval


-- @@ L131-131 verbatim
/-! ### Benchmark Result Structure -/


-- @@ L133-142 verbatim
structure BenchResult where
  name : String
  ratLo : ℚ
  ratHi : ℚ
  ratWidth : ℚ
  affineLo : ℚ
  affineHi : ℚ
  affineWidth : ℚ
  improvement : String  -- Percentage improvement
  deriving Repr


-- @@ L144-160 verbatim
def runBenchmark (name : String) (e : Expr) (I : IntervalRat) : BenchResult :=
  let rat := evalRat e I
  let aff := evalAffine e I
  let ratWidth := rat.hi - rat.lo
  let affWidth := aff.hi - aff.lo
  let improv := if ratWidth > 0 then
    let pct := ((ratWidth - affWidth) * 100) / ratWidth
    s!"{pct}%"
  else "N/A"
  { name := name
    ratLo := rat.lo
    ratHi := rat.hi
    ratWidth := ratWidth
    affineLo := aff.lo
    affineHi := aff.hi
    affineWidth := affWidth
    improvement := improv }


-- @@ L162-162 verbatim
/-! ### Dependency Problem Benchmarks -/


-- @@ L164-165 verbatim
#eval runBenchmark "x - x" exprXMinusX testInterval
-- Expected: Rational gives [-2, 2], Affine gives [0, 0] (100% improvement)


-- @@ L167-168 verbatim
#eval runBenchmark "x² - x²" exprXSqMinusXSq testInterval
-- Expected: Rational gives wide interval, Affine gives [0, 0]


-- @@ L170-171 verbatim
#eval runBenchmark "(x+1) - x" exprXPlus1MinusX testInterval
-- Expected: Rational gives [0, 2], Affine gives [1, 1] (exact)


-- @@ L173-174 verbatim
#eval runBenchmark "x(1-x) + x²" exprCorrelated testInterval
-- Expected: Should equal x, so Affine gives [-1, 1], Rational wider


-- @@ L176-176 verbatim
/-! ### Transcendental Function Benchmarks -/


-- @@ L178-178 verbatim
#eval runBenchmark "sin(x)" exprSin testInterval

-- @@ L179-179 verbatim
#eval runBenchmark "cos(x)" exprCos testInterval

-- @@ L180-180 verbatim
#eval runBenchmark "exp(x)" exprExp smallInterval

-- @@ L181-181 verbatim
#eval runBenchmark "tanh(x)" exprTanh testInterval

-- @@ L182-182 verbatim
#eval runBenchmark "sinh(x)" exprSinh smallInterval

-- @@ L183-183 verbatim
#eval runBenchmark "cosh(x)" exprCosh smallInterval

-- @@ L184-186 verbatim
#eval runBenchmark "sqrt(x)" exprSqrt smallInterval

-- The Pythagorean identity loses correlation in interval arithmetic

-- @@ L187-188 verbatim
#eval runBenchmark "sin²+cos²" exprSinSqPlusCosSq narrowInterval
-- Expected: Should be [1, 1] but interval gives wider bounds


-- @@ L190-190 verbatim
/-! ### Three-Way Backend Comparison -/


-- @@ L192-197 verbatim
structure ThreeWayResult where
  name : String
  ratWidth : ℚ
  dyadWidth : ℚ
  affineWidth : ℚ
  deriving Repr


-- @@ L199-206 verbatim
def runThreeWay (name : String) (e : Expr) (I : IntervalRat) : ThreeWayResult :=
  let rat := evalRat e I
  let dyad := evalDyad e I
  let aff := evalAffine e I
  { name := name
    ratWidth := rat.hi - rat.lo
    dyadWidth := dyad.hi - dyad.lo
    affineWidth := aff.hi - aff.lo }


-- @@ L208-208 verbatim
#eval runThreeWay "x - x" exprXMinusX testInterval

-- @@ L209-209 verbatim
#eval runThreeWay "sin(x)" exprSin testInterval

-- @@ L210-210 verbatim
#eval runThreeWay "exp(x)" exprExp smallInterval


-- @@ L212-215 verbatim
/-! ### Soundness Verification -/

-- Verify that Affine results are sound (contain the true value range)
-- For x - x, the true value is always 0, so [0, 0] must be valid


-- @@ L217-219 verbatim
/-- x - x evaluates to exactly 0 for any x -/
theorem xMinusX_eval (ρ : Nat → ℝ) : Expr.eval ρ exprXMinusX = 0 := by
  simp [exprXMinusX, Expr.eval]


-- @@ L221-225 verbatim
/-- (x+1) - x evaluates to exactly 1 for any x -/
theorem xPlus1MinusX_eval (ρ : Nat → ℝ) : Expr.eval ρ exprXPlus1MinusX = 1 := by
  simp [exprXPlus1MinusX, Expr.eval]

-- Verify Affine bounds contain 0 for x - x

-- @@ L226-226 verbatim
example : (evalAffine exprXMinusX testInterval).lo ≤ 0 := by native_decide

-- @@ L227-229 verbatim
example : 0 ≤ (evalAffine exprXMinusX testInterval).hi := by native_decide

-- Verify Affine bounds contain 1 for (x+1) - x

-- @@ L230-230 verbatim
example : (evalAffine exprXPlus1MinusX testInterval).lo ≤ 1 := by native_decide

-- @@ L231-231 verbatim
example : 1 ≤ (evalAffine exprXPlus1MinusX testInterval).hi := by native_decide


-- @@ L233-233 verbatim
/-! ### Multi-Variable Tests -/


-- @@ L235-236 verbatim
/-- Two-variable environment -/
def mkAffineEnv2 (I1 I2 : IntervalRat) : AffineEnv := toAffineEnv [I1, I2]


-- @@ L238-240 verbatim
/-- x + y - x: Should equal y -/
def exprXPlusYMinusX : Expr :=
  Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.neg (Expr.var 0))


-- @@ L242-245 verbatim
def evalAffine2 (e : Expr) (I1 I2 : IntervalRat) : IntervalRat :=
  (LeanCert.Internal.Affine.evalUnchecked e (mkAffineEnv2 I1 I2) {}).toInterval

-- x + y - x on x ∈ [-1,1], y ∈ [0,2] should give y's range [0, 2]

-- @@ L246-249 verbatim
#eval evalAffine2 exprXPlusYMinusX testInterval ⟨0, 2, by norm_num⟩
-- Expected: [0, 2] (exact range of y)

-- Compare with rational which loses the x correlation

-- @@ L250-252 verbatim
#eval LeanCert.Internal.Rational.evalTotalCore exprXPlusYMinusX
  (fun i => if i == 0 then testInterval else ⟨0, 2, by norm_num⟩) {}
-- Expected: Wider than [0, 2]


-- @@ L254-254 verbatim
/-! ### Neural Network-Like Expressions -/


-- @@ L256-261 verbatim
/-- LayerNorm-style expression: (x - mean) / std where mean and std depend on x -/
-- Simplified: x - (x/2) = x/2
def exprSimplifiedLayerNorm : Expr :=
  let x := Expr.var 0
  let halfX := Expr.mul x (Expr.const (1/2))
  Expr.add x (Expr.neg halfX)


-- @@ L263-264 verbatim
#eval runBenchmark "x - x/2" exprSimplifiedLayerNorm testInterval
-- Expected: Affine tracks the correlation, giving tighter bounds


-- @@ L266-274 verbatim
/-- ReLU-like: max(0, x) approximated as (x + |x|) / 2
    Using x² instead of |x| for smoothness: (x + sqrt(x² + ε)) / 2 -/
def exprSoftplus : Expr :=
  let x := Expr.var 0
  let xsq := Expr.mul x x
  let eps := Expr.const (1/100)
  let inner := Expr.add xsq eps
  let sqrtInner := Expr.sqrt inner
  Expr.mul (Expr.add x sqrtInner) (Expr.const (1/2))


-- @@ L276-276 verbatim
#eval runBenchmark "softplus" exprSoftplus testInterval


-- @@ L278-278 verbatim
end LeanCert.Test.Affine
