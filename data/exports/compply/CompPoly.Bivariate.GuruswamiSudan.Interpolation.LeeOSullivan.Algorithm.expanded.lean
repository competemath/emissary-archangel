/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
public import CompPoly.LinearAlgebra.PolynomialMatrix.ShiftedReduction


-- @@ L11-21 verbatim
/-!
# Executable Lee-O'Sullivan Interpolation

Executable Lee-O'Sullivan interpolation via an explicit `F[X]` module basis and
shifted polynomial-row reduction.

## References

* [Lee, K., and O'Sullivan, M. E., *List decoding of Reed-Solomon codes from a
    Groebner basis perspective*][LOS06]
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace CompPoly


-- @@ L27-27 verbatim
namespace GuruswamiSudan


-- @@ L29-29 verbatim
namespace LeeOSullivan


-- @@ L31-31 verbatim
open PolynomialMatrix


-- @@ L33-33 verbatim
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]


-- @@ L35-39 verbatim
/-- Candidate row selected by least-shifted-degree scanning. -/
structure RowChoice (F : Type*) [Zero F] where
  index : Nat
  row : PolynomialRow F
  degree : Nat


-- @@ L41-44 verbatim
/-- Tie-breaking order for least-shifted-degree row selection. -/
def betterRowChoice (candidate current : RowChoice F) : Bool :=
  candidate.degree < current.degree ||
    (candidate.degree == current.degree && candidate.index < current.index)


-- @@ L46-58 verbatim
/-- One left-to-right scan step for least-shifted-degree row selection. -/
def leastShiftedDegreeRowStep?
    (M : PolynomialMatrix F) (shift : Array Nat)
    (best : Option (RowChoice F)) (i : Nat) : Option (RowChoice F) :=
  let row := M.getD i #[]
  match rowShiftedDegree? row shift with
  | none => best
  | some degree =>
      let candidate : RowChoice F := { index := i, row := row, degree := degree }
      match best with
      | none => some candidate
      | some current =>
          if betterRowChoice candidate current then some candidate else best


-- @@ L60-63 verbatim
/-- Scan row indices for the best least-shifted-degree candidate. -/
def leastShiftedDegreeChoice?
    (M : PolynomialMatrix F) (shift : Array Nat) : Option (RowChoice F) :=
  (List.range M.size).foldl (leastShiftedDegreeRowStep? M shift) none


-- @@ L65-68 verbatim
/-- Select a nonzero row of least shifted degree from a reduced matrix. -/
def leastShiftedDegreeRow? (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (PolynomialRow F) :=
  (leastShiftedDegreeChoice? M shift).map fun choice ↦ choice.row


-- @@ L70-74 verbatim
/-- Normalize a row-derived candidate using the shared interpolation vector policy. -/
def normalizeLeeCandidate? (params : GSInterpParams) (Q : CBivariate F) :
    Option (CBivariate F) :=
  normalizeInterpolationPolynomial? params
    (interpolationCoefficientVector params Q)


-- @@ L76-103 verbatim
/-- Positive-`Y`-weight Lee-O'Sullivan interpolation branch. -/
def leeOSullivanPositiveInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if distinctXCoordinatesBool points then
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    let basis := leeOSullivanBasisRowsWithRG R G params
    let shift := leeOSullivanShifts params
    let reduced := reducer.reduce basis shift
    match leastShiftedDegreeRow? reduced shift with
    | none => none
    | some row =>
        match rowShiftedDegree? row shift with
        | none => none
        | some degree =>
            if degree ≤ params.weightedDegreeBound then
              let rawQ := CBivariate.ofCoeffRow row
              match normalizeLeeCandidate? params rawQ with
              | none => none
              | some Q => some Q
            else
              none
  else
    none


-- @@ L105-115 verbatim
/-- Lee-O'Sullivan interpolation with the shared low-message branch. -/
def leeOSullivanInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    leeOSullivanPositiveInterpolate V E reducer points params


-- @@ L117-117 verbatim
end LeeOSullivan


-- @@ L119-119 verbatim
end GuruswamiSudan


-- @@ L121-121 verbatim
end CompPoly
