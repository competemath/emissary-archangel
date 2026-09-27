/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-20 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskAtFacts
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L26-26 verbatim
namespace N1000000MaskAtFacts


-- @@ L28-28 verbatim
open Distributed2Coloring.LowerBound.N1000000StructureConstants


-- @@ L30-31 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask

-- @@ L32-33 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx


-- @@ L35-37 verbatim
theorem maskAt_testBit_eq_decide_colMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (colMatch (maskAt d) j = some i) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide


-- @@ L39-41 verbatim
theorem maskAt_testBit_eq_decide_rowMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide


-- @@ L43-43 verbatim
end N1000000MaskAtFacts


-- @@ L45-45 verbatim
end Distributed2Coloring.LowerBound

