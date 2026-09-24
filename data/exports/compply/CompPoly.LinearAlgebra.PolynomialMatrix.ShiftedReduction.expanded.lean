/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.LinearAlgebra.PolynomialMatrix.RowSpan


-- @@ L10-12 verbatim
/-!
# Shifted Row Reduction Contexts
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace CompPoly


-- @@ L18-18 verbatim
namespace PolynomialMatrix


-- @@ L20-47 verbatim
/-- Executable shifted row-reduction backend over `F[X]`. -/
structure ShiftedRowReducerContext
    (F : Type*) [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] where
  reduce : PolynomialMatrix F → Array Nat → PolynomialMatrix F
  shape_preserved :
    ∀ M shift,
      WellFormed M →
        MatrixShape (reduce M shift) = MatrixShape M
  rowSpan_eq :
    ∀ M shift,
      WellFormed M →
        RowSpan (reduce M shift) = RowSpan M
  weakPopov :
    ∀ M shift,
      WellFormed M →
      shift.size = MatrixWidth M →
        ShiftedWeakPopov (reduce M shift) shift
  least_row_minimal :
    ∀ M shift row,
      WellFormed M →
      shift.size = MatrixWidth M →
      row ∈ RowSpan M →
      rowShiftedDegree? row shift ≠ none →
        ∃ outRow outDeg rowDeg,
          outRow ∈ MatrixRows (reduce M shift) ∧
          rowShiftedDegree? outRow shift = some outDeg ∧
          rowShiftedDegree? row shift = some rowDeg ∧
          outDeg ≤ rowDeg


-- @@ L49-49 verbatim
end PolynomialMatrix


-- @@ L51-51 verbatim
end CompPoly
