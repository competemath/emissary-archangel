/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Univariate.Basic


-- @@ L10-14 verbatim
/-!
# Polynomial Rows and Matrices

Minimal row-oriented polynomial-matrix infrastructure for shifted row reduction.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace CompPoly


-- @@ L20-21 verbatim
/-- A polynomial row over `F[X]`. -/
abbrev PolynomialRow (F : Type*) [Zero F] := Array (CPolynomial F)


-- @@ L23-24 verbatim
/-- A polynomial matrix over `F[X]`, stored as an array of rows. -/
abbrev PolynomialMatrix (F : Type*) [Zero F] := Array (PolynomialRow F)


-- @@ L26-30 verbatim
/-- Runtime rectangular shape of a polynomial matrix. -/
structure PolynomialMatrixShape where
  rows : Nat
  width : Nat
deriving Repr, BEq, DecidableEq


-- @@ L32-32 verbatim
namespace PolynomialMatrix


-- @@ L34-34 verbatim
variable {F : Type*}


-- @@ L36-38 verbatim
/-- Width of a row. -/
def RowWidth [Zero F] (row : PolynomialRow F) : Nat :=
  row.size


-- @@ L40-44 verbatim
/-- Matrix width, using the first row and width `0` for an empty matrix. -/
def MatrixWidth [Zero F] (M : PolynomialMatrix F) : Nat :=
  match M[0]? with
  | none => 0
  | some row => row.size


-- @@ L46-48 verbatim
/-- Runtime matrix shape. -/
def MatrixShape [Zero F] (M : PolynomialMatrix F) : PolynomialMatrixShape :=
  { rows := M.size, width := MatrixWidth M }


-- @@ L50-52 verbatim
/-- Matrix rows as a list, for membership statements. -/
def MatrixRows [Zero F] (M : PolynomialMatrix F) : List (PolynomialRow F) :=
  M.toList


-- @@ L54-56 verbatim
/-- A matrix is rectangular when every row has the matrix width. -/
def WellFormed [Zero F] (M : PolynomialMatrix F) : Prop :=
  ∀ row, row ∈ MatrixRows M → row.size = MatrixWidth M


-- @@ L58-60 verbatim
/-- Read a row coefficient with zero default. -/
def rowGet [Zero F] (row : PolynomialRow F) (j : Nat) : CPolynomial F :=
  row.getD j 0


-- @@ L62-64 verbatim
/-- The zero row of a fixed width. -/
def zeroRow [Zero F] (width : Nat) : PolynomialRow F :=
  Array.replicate width 0


-- @@ L66-70 verbatim
/-- Pointwise row addition over the maximum input width. -/
def rowAdd [Semiring F] [BEq F] [LawfulBEq F]
    (a b : PolynomialRow F) : PolynomialRow F :=
  (List.range (max a.size b.size)).map
    (fun j ↦ rowGet a j + rowGet b j) |>.toArray


-- @@ L72-75 verbatim
/-- Pointwise row negation. -/
def rowNeg [Ring F] [BEq F] [LawfulBEq F] (row : PolynomialRow F) :
    PolynomialRow F :=
  row.map fun p ↦ -p


-- @@ L77-80 verbatim
/-- Pointwise row subtraction over the maximum input width. -/
def rowSub [Ring F] [BEq F] [LawfulBEq F]
    (a b : PolynomialRow F) : PolynomialRow F :=
  rowAdd a (rowNeg b)


-- @@ L82-85 verbatim
/-- Multiply a row by a univariate polynomial. -/
def rowScalePolynomial [Semiring F] [BEq F] [LawfulBEq F]
    (c : CPolynomial F) (row : PolynomialRow F) : PolynomialRow F :=
  row.map fun p ↦ c * p


-- @@ L87-90 verbatim
/-- Multiply a row by `c * X^d`. -/
def rowScaleMonomial [Semiring F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (c : F) (d : Nat) (row : PolynomialRow F) : PolynomialRow F :=
  rowScalePolynomial (CPolynomial.monomial d c) row


-- @@ L92-99 verbatim
/-- Fused `a - c * X^d * b` over the maximum input width, entrywise via
`CPolynomial.subMulMonomial`. One call costs `O(deg + d)` per entry instead of
the `O(d * deg)` convolution behind `rowSub a (rowScaleMonomial c d b)`. -/
def rowSubScaledShift [Ring F] [BEq F] [LawfulBEq F]
    (a : PolynomialRow F) (c : F) (d : Nat) (b : PolynomialRow F) :
    PolynomialRow F :=
  (List.range (max a.size b.size)).map
    (fun j ↦ CPolynomial.subMulMonomial (rowGet a j) c d (rowGet b j)) |>.toArray


-- @@ L101-104 verbatim
/-- Replace a row if the index is in bounds. -/
def replaceRow [Zero F] (M : PolynomialMatrix F) (idx : Nat) (row : PolynomialRow F) :
    PolynomialMatrix F :=
  M.setIfInBounds idx row


-- @@ L106-106 verbatim
end PolynomialMatrix


-- @@ L108-108 verbatim
end CompPoly
