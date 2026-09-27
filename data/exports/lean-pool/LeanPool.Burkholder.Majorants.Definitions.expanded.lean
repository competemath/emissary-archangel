/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset



-- @@ L16-21 verbatim
/-!
# Burkholder majorants: basic definitions

Defines the conjugate exponent `q`, `pStar`, the Burkholder expression `v`, and
the sector parameters used to build the majorant.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Majorants


-- @@ L29-30 verbatim
/-- The conjugate exponent, with a harmless value at `p = 1`. -/
def q (p : ℝ) : ℝ := if p = 1 then 0 else p / (p - 1)


-- @@ L32-33 verbatim
/-- `pStar = max p q`; in the main `p ≥ 2` regime this is just `p`. -/
def pStar (p : ℝ) : ℝ := max p (q p)


-- @@ L35-38 verbatim
/-- The original Burkholder-type expression, written with `pStar`. -/
def v (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (|pStar p - 1|) p * Real.rpow (|((x - y) / 2)|) p


-- @@ L40-41 verbatim
/-- The slope parameter separating the two smooth sectors in the first quadrant. -/
  def a (p : ℝ) : ℝ := 1 - 2 / (pStar p)


-- @@ L43-44 verbatim
/-- Normalization constant for the affine-in-`y` sector formula. -/
  def alpha (p : ℝ) : ℝ :=  p* Real.rpow (pStar p/(pStar p - 1)) (1-p)



-- @@ L47-47 verbatim
end Majorants
