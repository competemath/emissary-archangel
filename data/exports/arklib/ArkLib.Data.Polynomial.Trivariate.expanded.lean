/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import ArkLib.Data.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial


-- @@ L11-41 verbatim
/-!
# Trivariate Polynomials

We define trivariate polynomials to match their representation in statements and proofs of
[BCIKS20]. A value of type `F[Z][X][Y]` is nested with `Y` outermost, `X` in the middle, and `Z`
innermost. The semantic evaluation and degree operations in this namespace make those axes explicit.

Applying `Polynomial.Bivariate` operations directly to `F[Z][X][Y]` instead treats it as a
bivariate polynomial over `F[Z]`. In particular, its `evalX` specializes the middle `X` variable,
while its `totalDegree` measures only `(X, Y)` and ignores `Z`.

## Main Definitions

### Notation, evaluation, and degree projections
- `eval_on_Z₀`: Evaluate a rational function on a point.
- `evalAtX`, `evalAtY`, `evalAtZ`: Evaluate the named variable of a trivariate polynomial.
- `degreeInX`, `degreeInY`, `degreeInZ`: The degree in one named variable.
- `degreeXY`, `degreeYZ`, `totalDegreeXYZ`: The projected or full total degrees.
- `toRatFuncPoly`: Maps a trivariate polynomial to a bivariate polynomial over the rational
  function field.
- `D_Y`: The `Y`-degree of a trivariate polynomial.
- `D_YZ`: The `YZ`-degree of a trivariate polynomial.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
namespace Trivariate


-- @@ L47-55 verbatim
open Polynomial Bivariate

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial R))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)


-- @@ L57-57 verbatim
section Semiring


-- @@ L59-59 verbatim
variable {R : Type*} [CommSemiring R]


-- @@ L61-64 verbatim
/-- Evaluate the middle `X` variable of `p : R[Z][X][Y]` at `x`, leaving a polynomial in
`(Z, Y)`. This is the semantic wrapper around bivariate `evalX` over the coefficient ring `R[Z]`. -/
noncomputable def evalAtX (x : R) (p : R[Z][X][Y]) : Polynomial (Polynomial R) :=
  Bivariate.evalX (Polynomial.C x) p


-- @@ L66-69 verbatim
/-- Evaluate the outer `Y` variable of `p : R[Z][X][Y]` at `y`, leaving a polynomial in
`(Z, X)`. -/
noncomputable def evalAtY (y : R) (p : R[Z][X][Y]) : R[Z][X] :=
  Bivariate.evalY (Polynomial.C y) p


-- @@ L71-74 verbatim
/-- Evaluate the innermost `Z` variable of `p : R[Z][X][Y]` at `z`, leaving a polynomial in
`(X, Y)`. -/
noncomputable def evalAtZ (z : R) (p : R[Z][X][Y]) : R[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))


-- @@ L76-77 verbatim
/-- Backwards-compatible name for `evalAtZ`. New code should use the axis-explicit API. -/
@[deprecated evalAtZ (since := "2026-08-21")]

-- @@ L78-79 verbatim
noncomputable abbrev eval_on_Z (p : R[Z][X][Y]) (z : R) : R[X][Y] :=
  evalAtZ z p


-- @@ L81-83 verbatim
/-- The maximum exponent of the middle `X` variable in a trivariate polynomial. -/
noncomputable def degreeInX (p : R[Z][X][Y]) : ℕ :=
  Bivariate.degreeX p


-- @@ L85-87 verbatim
/-- The maximum exponent of the outer `Y` variable in a trivariate polynomial. -/
noncomputable def degreeInY (p : R[Z][X][Y]) : ℕ :=
  Bivariate.natDegreeY p


-- @@ L89-91 verbatim
/-- The maximum exponent of the innermost `Z` variable in a trivariate polynomial. -/
noncomputable def degreeInZ (p : R[Z][X][Y]) : ℕ :=
  p.support.sup fun j => (p.coeff j).support.sup fun i => ((p.coeff j).coeff i).natDegree


-- @@ L93-97 verbatim
/-- The projected `(X, Y)` total degree of a trivariate polynomial. This is the quantity computed
by `Bivariate.totalDegree p`; naming the projection prevents it from being mistaken for the full
trivariate total degree. -/
noncomputable def degreeXY (p : R[Z][X][Y]) : ℕ :=
  Bivariate.totalDegree p


-- @@ L99-104 verbatim
/-- The generic bivariate total degree on a trivariate value is exactly the `(X, Y)` projection.
This bridge is intentionally named so callers do not silently read it as a `(Y, Z)` or full
trivariate bound. -/
theorem degreeXY_eq_bivariate_totalDegree (p : R[Z][X][Y]) :
    degreeXY p = Bivariate.totalDegree p :=
  rfl


-- @@ L106-122 verbatim
/-- The projected `(Y, Z)` total degree of a trivariate polynomial: the maximum of `degY + degZ`
over its monomials. The middle `X` exponent is deliberately ignored.

Here `j` is the outer `Y` exponent and `i` is the middle `X` exponent.
`Bivariate.coeff p i j = (p.coeff j).coeff i` is then a polynomial in `Z`, whose `natDegree`
supplies the `Z` exponent. -/
noncomputable def degreeYZ (p : R[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
      (fun j =>
        Option.getD
          (Finset.max
            (Finset.image
              (fun i => j + (Bivariate.coeff p i j).natDegree)
              (p.coeff j).support))
          0)
      p.support)


-- @@ L124-126 verbatim
/-- The full `(X, Y, Z)` total degree of a trivariate polynomial. -/
noncomputable def totalDegreeXYZ (p : R[Z][X][Y]) : ℕ :=
  p.support.sup fun j => Bivariate.totalDegree (p.coeff j) + j


-- @@ L128-134 verbatim
/-- Each `Y`-coefficient's `(Z, X)` total-degree contribution is bounded by the full trivariate
total degree. -/
theorem coeff_totalDegree_add_index_le_totalDegree (p : R[Z][X][Y]) {j : ℕ}
    (hj : j ∈ p.support) :
    Bivariate.totalDegree (p.coeff j) + j ≤ totalDegreeXYZ p := by
  classical
  exact Finset.le_sup (f := fun j => Bivariate.totalDegree (p.coeff j) + j) hj


-- @@ L136-139 verbatim
/-- `evalAtX` is the corresponding coefficient-ring map. -/
theorem evalAtX_eq_map_evalRingHom (x : R) (p : R[Z][X][Y]) :
    evalAtX x p = p.map (Polynomial.evalRingHom (Polynomial.C x)) := by
  simp [evalAtX, Bivariate.evalX_eq_map]


-- @@ L141-144 verbatim
/-- `evalAtZ` is the coefficient-wise evaluation map on the innermost variable. -/
theorem evalAtZ_eq_map_map_evalRingHom (z : R) (p : R[Z][X][Y]) :
    evalAtZ z p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl


-- @@ L146-147 verbatim
/-- Following [BCIKS20], this is the `Y`-degree of a trivariate polynomial `Q`. -/
noncomputable def D_Y (Q : R[Z][X][Y]) : ℕ := degreeInY Q


-- @@ L149-150 verbatim
/-- Following [BCIKS20], this is the total `(Y, Z)`-degree of a trivariate polynomial `Q`. -/
noncomputable def D_YZ (Q : R[Z][X][Y]) : ℕ := degreeYZ Q


-- @@ L152-154 verbatim
/-- The paper-facing `D_YZ` is the semantic `(Y, Z)` projection. -/
theorem D_YZ_eq_degreeYZ (Q : R[Z][X][Y]) : D_YZ Q = degreeYZ Q :=
  rfl


-- @@ L156-156 verbatim
end Semiring


-- @@ L158-162 verbatim
/-! ### Axis regression checks

The unequal exponents in this monomial make accidental permutations observable. In particular,
the `(X, Y)` projection is `10`, the `(Y, Z)` projection is `8`, and the full degree is `15`.
-/


-- @@ L164-166 verbatim
private noncomputable def axisRegressionPolynomial :
    Polynomial (Polynomial (Polynomial ℚ)) :=
  Polynomial.monomial 3 (Polynomial.monomial 7 (Polynomial.monomial 5 1))


-- @@ L168-169 verbatim
example : degreeInX axisRegressionPolynomial = 7 := by
  norm_num [axisRegressionPolynomial, degreeInX, Bivariate.degreeX]


-- @@ L171-172 verbatim
example : degreeInY axisRegressionPolynomial = 3 := by
  norm_num [axisRegressionPolynomial, degreeInY, Bivariate.natDegreeY]


-- @@ L174-175 verbatim
example : degreeInZ axisRegressionPolynomial = 5 := by
  norm_num [axisRegressionPolynomial, degreeInZ]


-- @@ L177-178 verbatim
example : degreeXY axisRegressionPolynomial = 10 := by
  norm_num [axisRegressionPolynomial, degreeXY, Bivariate.totalDegree]


-- @@ L180-181 verbatim
example : degreeYZ axisRegressionPolynomial = 8 := by
  norm_num [axisRegressionPolynomial, degreeYZ, Bivariate.coeff, Option.getD]


-- @@ L183-184 verbatim
example : Bivariate.totalDegree axisRegressionPolynomial ≠ degreeYZ axisRegressionPolynomial := by
  norm_num [axisRegressionPolynomial, degreeYZ, Bivariate.totalDegree, Bivariate.coeff, Option.getD]


-- @@ L186-187 verbatim
example : totalDegreeXYZ axisRegressionPolynomial = 15 := by
  norm_num [axisRegressionPolynomial, totalDegreeXYZ, Bivariate.totalDegree]


-- @@ L189-193 verbatim
example : evalAtX 2 axisRegressionPolynomial =
    Polynomial.monomial 3 (Polynomial.monomial 5 ((2 : ℚ) ^ 7)) := by
  norm_num [evalAtX, axisRegressionPolynomial, Bivariate.evalX_eq_map]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]
  norm_num


-- @@ L195-200 verbatim
example : evalAtY 2 axisRegressionPolynomial =
    Polynomial.monomial 7 (Polynomial.monomial 5 ((2 : ℚ) ^ 3)) := by
  norm_num [evalAtY, axisRegressionPolynomial, Bivariate.evalY]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]
  rw [← Polynomial.C_pow, Polynomial.monomial_mul_C]
  norm_num


-- @@ L202-204 verbatim
example : evalAtZ 2 axisRegressionPolynomial =
    Polynomial.monomial 3 (Polynomial.monomial 7 ((2 : ℚ) ^ 5)) := by
  norm_num [evalAtZ, axisRegressionPolynomial]


-- @@ L206-206 verbatim
section Field


-- @@ L208-208 verbatim
variable {F : Type*} [Field F] [DecidableEq (RatFunc F)]


-- @@ L210-212 verbatim
/-- Evaluate a rational function on a point. -/
noncomputable def eval_on_Z₀ (p : RatFunc F) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p


-- @@ L214-218 verbatim
open Polynomial.Bivariate in
/-- A ring homomorphism mapping a trivariate polynomial to an element in the field of rational
functions of polynomial ring in two variables. -/
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))


-- @@ L220-220 verbatim
end Field


-- @@ L222-222 verbatim
end Trivariate
