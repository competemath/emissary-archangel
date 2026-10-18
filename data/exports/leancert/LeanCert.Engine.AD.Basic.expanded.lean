/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval


-- @@ L8-23 verbatim
/-!
# Automatic Differentiation - Basic Definitions

This file provides the core types and algebraic operations for forward-mode
automatic differentiation using interval arithmetic.

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `DualInterval.const` - Constant dual (derivative is zero)
* `DualInterval.varActive` - Active variable (derivative is 1)
* `DualInterval.varPassive` - Passive variable (derivative is 0)
* `DualInterval.add` - Addition with sum rule
* `DualInterval.mul` - Multiplication with product rule
* `DualInterval.neg` - Negation
-/


-- @@ L25-25 verbatim
namespace LeanCert.Engine


-- @@ L27-27 verbatim
open LeanCert.Core


-- @@ L29-33 verbatim
/-- Dual number with interval components: represents (value, derivative) -/
structure DualInterval where
  val : IntervalRat
  der : IntervalRat
  deriving Repr


-- @@ L35-37 verbatim
/-- Default DualInterval for unsupported expression branches -/
instance : Inhabited DualInterval where
  default := ⟨default, default⟩


-- @@ L39-39 verbatim
namespace DualInterval


-- @@ L41-44 verbatim
/-- Dual interval for a constant (derivative is zero) -/
def const (q : ℚ) : DualInterval :=
  { val := IntervalRat.singleton q
    der := IntervalRat.singleton 0 }


-- @@ L46-49 verbatim
/-- Dual interval for the constant π (derivative is zero) -/
def piConst : DualInterval :=
  { val := piInterval
    der := IntervalRat.singleton 0 }


-- @@ L51-54 verbatim
/-- Dual interval for the Euler–Mascheroni constant γ (derivative is zero) -/
def eulerMascheroniConst : DualInterval :=
  { val := eulerMascheroniInterval
    der := IntervalRat.singleton 0 }


-- @@ L56-59 verbatim
/-- Dual interval for a named mathematical constant (derivative is zero) -/
def ofMathConst (c : MathConst) : DualInterval :=
  { val := c.interval
    der := IntervalRat.singleton 0 }


-- @@ L61-64 verbatim
/-- Dual interval for the variable we're differentiating with respect to -/
def varActive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 1 }


-- @@ L66-69 verbatim
/-- Dual interval for a passive variable -/
def varPassive (I : IntervalRat) : DualInterval :=
  { val := I
    der := IntervalRat.singleton 0 }


-- @@ L71-74 verbatim
/-- Add two dual intervals -/
def add (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.add d₁.val d₂.val
    der := IntervalRat.add d₁.der d₂.der }


-- @@ L76-82 verbatim
/-- Multiply two dual intervals (product rule) -/
def mul (d₁ d₂ : DualInterval) : DualInterval :=
  { val := IntervalRat.mul d₁.val d₂.val
    -- d(f*g) = f'*g + f*g'
    der := IntervalRat.add
             (IntervalRat.mul d₁.der d₂.val)
             (IntervalRat.mul d₁.val d₂.der) }


-- @@ L84-87 verbatim
/-- Negate a dual interval -/
def neg (d : DualInterval) : DualInterval :=
  { val := IntervalRat.neg d.val
    der := IntervalRat.neg d.der }


-- @@ L89-97 verbatim
/-- Inverse of a dual interval (quotient rule: d(1/f) = -f'/f²)
    Uses invInterval for the value component.
    For intervals containing zero, returns wide bounds. -/
def inv (d : DualInterval) : DualInterval :=
  let inv_val := invInterval d.val
  -- d(1/f) = -f'/f² = -f' * (1/f)²
  let inv_sq := IntervalRat.mul inv_val inv_val
  let der' := IntervalRat.neg (IntervalRat.mul d.der inv_sq)
  { val := inv_val, der := der' }


-- @@ L99-99 verbatim
end DualInterval


-- @@ L101-101 verbatim
end LeanCert.Engine
