/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.AD


-- @@ L9-19 verbatim
/-!
# Basic Examples

This file demonstrates LeanCert's verified interval arithmetic core.

All examples in this file use only the fully-verified subset of expressions:
const, var, add, mul, neg, sin, cos

The correctness theorems (evalInterval_correct, evalDual_val_correct) are
FULLY PROVED with no sorry, no axioms for this subset.
-/


-- @@ L21-21 verbatim
namespace LeanCert.Examples.Basic


-- @@ L23-23 verbatim
open LeanCert.Core

-- @@ L24-24 verbatim
open LeanCert.Engine


-- @@ L26-26 verbatim
/-! ### Building supported expressions -/


-- @@ L28-29 verbatim
/-- The expression x² (x squared) -/
def xSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)


-- @@ L31-33 verbatim
/-- Proof that x² is in the supported subset -/
theorem xSq_supported : ADSupported xSq :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)


-- @@ L35-39 verbatim
/-- The expression x² + 2x + 1 = (x + 1)² -/
def exprSquare : Expr :=
  Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                     (Expr.mul (Expr.const 2) (Expr.var 0)))
           (Expr.const 1)


-- @@ L41-47 verbatim
/-- Proof that x² + 2x + 1 is in the supported subset -/
theorem exprSquare_supported : ADSupported exprSquare :=
  ADSupported.add
    (ADSupported.add
      (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
      (ADSupported.mul (ADSupported.const 2) (ADSupported.var 0)))
    (ADSupported.const 1)


-- @@ L49-51 verbatim
/-- The expression sin(x) + cos(x) -/
def exprSinCos : Expr :=
  Expr.add (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))


-- @@ L53-57 verbatim
/-- Proof that sin(x) + cos(x) is in the supported subset -/
theorem exprSinCos_supported : ADSupported exprSinCos :=
  ADSupported.add
    (ADSupported.sin (ADSupported.var 0))
    (ADSupported.cos (ADSupported.var 0))


-- @@ L59-59 verbatim
/-! ### Interval construction -/


-- @@ L61-62 verbatim
/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩


-- @@ L64-65 verbatim
/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩


-- @@ L67-68 verbatim
/-- A small interval around 0: [-1/10, 1/10] -/
def smallInterval : IntervalRat := ⟨-1/10, 1/10, by norm_num⟩


-- @@ L70-70 verbatim
/-! ### Interval membership examples -/


-- @@ L72-74 verbatim
example : (1 : ℝ) / 2 ∈ I01 := by
  simp only [IntervalRat.mem_def, I01]
  norm_num


-- @@ L76-78 verbatim
example : (0 : ℝ) ∈ symInterval := by
  simp only [IntervalRat.mem_def, symInterval]
  norm_num


-- @@ L80-80 verbatim
/-! ### Expression evaluation examples -/


-- @@ L82-85 verbatim
/-- Evaluate x² + 2x + 1 at x = 2, should give 9 -/
example : Expr.eval (fun _ => 2) exprSquare = 9 := by
  simp only [exprSquare, Expr.eval_add, Expr.eval_mul, Expr.eval_var, Expr.eval_const]
  norm_num


-- @@ L87-90 verbatim
/-- Evaluate x² at x = 3, should give 9 -/
example : Expr.eval (fun _ => 3) xSq = 9 := by
  simp only [xSq, Expr.eval_mul, Expr.eval_var]
  norm_num


-- @@ L92-92 verbatim
/-! ### Verified interval evaluation -/


-- @@ L94-98 verbatim
/-- Key example: x² evaluated over [0, 1] gives a value in the computed interval.
    This uses the FULLY PROVED evalInterval1_correct theorem. -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) xSq ∈ LeanCert.Internal.Rational.evalUnchecked1 xSq I01 :=
  evalInterval1_correct xSq xSq_supported x I01 hx


-- @@ L100-103 verbatim
/-- x² + 2x + 1 evaluated over [0, 1] gives a value in the computed interval. -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprSquare ∈ LeanCert.Internal.Rational.evalUnchecked1 exprSquare I01 :=
  evalInterval1_correct exprSquare exprSquare_supported x I01 hx


-- @@ L105-108 verbatim
/-- sin(x) + cos(x) evaluated over [-1, 1] gives a value in the computed interval. -/
example (x : ℝ) (hx : x ∈ symInterval) :
    Expr.eval (fun _ => x) exprSinCos ∈ LeanCert.Internal.Rational.evalUnchecked1 exprSinCos symInterval :=
  evalInterval1_correct exprSinCos exprSinCos_supported x symInterval hx


-- @@ L110-110 verbatim
/-! ### Using smart constructors -/


-- @@ L112-114 verbatim
/-- Build x² using smart constructors that carry the support proof -/
def xSq' : { e : Expr // ADSupported e } :=
  mkMul (mkVar 0) (mkVar 0)


-- @@ L116-119 verbatim
/-- Using smart constructors makes proofs trivial -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) xSq'.val ∈ LeanCert.Internal.Rational.evalUnchecked1 xSq'.val I01 :=
  evalInterval1_correct xSq'.val xSq'.property x I01 hx


-- @@ L121-121 verbatim
/-! ### Multi-variable example -/


-- @@ L123-124 verbatim
/-- The expression x * y (product of two variables) -/
def exprXY : Expr := Expr.mul (Expr.var 0) (Expr.var 1)


-- @@ L126-127 verbatim
theorem exprXY_supported : ADSupported exprXY :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 1)


-- @@ L129-130 verbatim
/-- Multi-variable interval environment -/
def ρ_xy : IntervalEnv := fun i => if i = 0 then I01 else symInterval


-- @@ L132-141 verbatim
/-- Verified evaluation with multiple variables -/
example (x y : ℝ) (hx : x ∈ I01) (hy : y ∈ symInterval) :
    Expr.eval (fun i => if i = 0 then x else y) exprXY ∈
    LeanCert.Internal.Rational.evalUnchecked exprXY ρ_xy := by
  apply evalInterval_correct exprXY exprXY_supported
  intro i
  simp only [ρ_xy]
  split_ifs with h
  · exact hx
  · exact hy


-- @@ L143-143 verbatim
end LeanCert.Examples.Basic
