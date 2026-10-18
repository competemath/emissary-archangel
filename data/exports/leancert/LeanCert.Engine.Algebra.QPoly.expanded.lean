/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


-- @@ L11-18 verbatim
/-!
# Executable exact rational polynomials

`Polynomial ℚ` is the semantic representation used by Mathlib, but its sparse
implementation is not a suitable native certificate payload. `QPoly` stores
ascending coefficients in an `Array ℚ` and supplies a small exact executable
kernel. The `toPoly` lemmas connect successful computations to Mathlib.
-/


-- @@ L20-20 verbatim
namespace LeanCert.Engine


-- @@ L22-22 verbatim
open LeanCert.Core


-- @@ L24-30 verbatim
/-- An exact executable rational polynomial.

`coeffs[i]` is the coefficient of `x^i`. Trailing zero coefficients are
allowed; use `trim` when a canonical certificate representation is useful. -/
structure QPoly where
  coeffs : Array ℚ
  deriving DecidableEq, Repr, Inhabited


-- @@ L32-32 verbatim
namespace QPoly


-- @@ L34-37 verbatim
private def addCoeffs : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addCoeffs xs ys


-- @@ L39-41 verbatim
private def scaleCoeffs (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | x :: xs => (c * x) :: scaleCoeffs c xs


-- @@ L43-45 verbatim
private def mulCoeffs : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => addCoeffs (scaleCoeffs x ys) (0 :: mulCoeffs xs ys)


-- @@ L47-53 verbatim
/-- Remove trailing zero coefficients. -/
private def trimCoeffs : List ℚ → List ℚ
  | [] => []
  | x :: xs =>
      match trimCoeffs xs with
      | [] => if x = 0 then [] else [x]
      | y :: ys => x :: y :: ys


-- @@ L55-57 verbatim
private def weightedDerivativeCoeffs (n : Nat) : List ℚ → List ℚ
  | [] => []
  | x :: xs => ((n : ℚ) * x) :: weightedDerivativeCoeffs (n + 1) xs


-- @@ L59-62 verbatim
/-- Formal derivative on ascending coefficients. -/
private def derivativeCoeffs : List ℚ → List ℚ
  | [] => []
  | _ :: xs => weightedDerivativeCoeffs 1 xs


-- @@ L64-66 verbatim
private def antiderivativeCoeffs (n : Nat) : List ℚ → List ℚ
  | [] => []
  | x :: xs => (x / (n : ℚ)) :: antiderivativeCoeffs (n + 1) xs


-- @@ L68-70 verbatim
private def evalCoeffs (x : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: cs => c + x * evalCoeffs x cs


-- @@ L72-74 verbatim
private noncomputable def listToPoly : List ℚ → Polynomial ℚ
  | [] => 0
  | x :: xs => Polynomial.C x + Polynomial.X * listToPoly xs


-- @@ L76-78 verbatim
/-- The semantic Mathlib polynomial represented by an executable `QPoly`. -/
noncomputable def toPoly (p : QPoly) : Polynomial ℚ :=
  listToPoly p.coeffs.toList


-- @@ L80-80 verbatim
def zero : QPoly := ⟨#[]⟩


-- @@ L82-82 verbatim
def constant (c : ℚ) : QPoly := ⟨#[c]⟩


-- @@ L84-85 verbatim
/-- The polynomial variable. -/
def X : QPoly := ⟨#[0, 1]⟩


-- @@ L87-88 verbatim
def add (p q : QPoly) : QPoly :=
  ⟨(addCoeffs p.coeffs.toList q.coeffs.toList).toArray⟩


-- @@ L90-91 verbatim
def mul (p q : QPoly) : QPoly :=
  ⟨(mulCoeffs p.coeffs.toList q.coeffs.toList).toArray⟩


-- @@ L93-94 verbatim
def derivative (p : QPoly) : QPoly :=
  ⟨(trimCoeffs (derivativeCoeffs p.coeffs.toList)).toArray⟩


-- @@ L96-98 verbatim
/-- The exact rational antiderivative with constant coefficient zero. -/
def antiderivative (p : QPoly) : QPoly :=
  ⟨(0 :: antiderivativeCoeffs 1 p.coeffs.toList).toArray⟩


-- @@ L100-102 verbatim
/-- Exact Horner evaluation over the rationals. -/
def evalRat (p : QPoly) (x : ℚ) : ℚ :=
  evalCoeffs x p.coeffs.toList


-- @@ L104-106 verbatim
/-- Exact definite integral between rational endpoints. -/
def integralRat (p : QPoly) (a b : ℚ) : ℚ :=
  p.antiderivative.evalRat b - p.antiderivative.evalRat a


-- @@ L108-109 verbatim
def trim (p : QPoly) : QPoly :=
  ⟨(trimCoeffs p.coeffs.toList).toArray⟩


-- @@ L111-120 verbatim
private theorem listToPoly_addCoeffs (xs ys : List ℚ) :
    listToPoly (addCoeffs xs ys) = listToPoly xs + listToPoly ys := by
  induction xs generalizing ys with
  | nil => simp [addCoeffs, listToPoly]
  | cons x xs ih =>
      cases ys with
      | nil => simp [addCoeffs, listToPoly]
      | cons y ys =>
          simp only [addCoeffs, listToPoly, ih, map_add]
          ring


-- @@ L122-128 verbatim
private theorem listToPoly_scaleCoeffs (c : ℚ) (xs : List ℚ) :
    listToPoly (scaleCoeffs c xs) = Polynomial.C c * listToPoly xs := by
  induction xs with
  | nil => simp [scaleCoeffs, listToPoly]
  | cons x xs ih =>
      simp only [scaleCoeffs, listToPoly, ih, map_mul]
      ring


-- @@ L130-137 verbatim
private theorem listToPoly_mulCoeffs (xs ys : List ℚ) :
    listToPoly (mulCoeffs xs ys) = listToPoly xs * listToPoly ys := by
  induction xs with
  | nil => simp [mulCoeffs, listToPoly]
  | cons x xs ih =>
      rw [mulCoeffs, listToPoly_addCoeffs, listToPoly_scaleCoeffs]
      simp only [listToPoly, ih, map_zero]
      ring


-- @@ L139-151 verbatim
private theorem listToPoly_trimCoeffs (xs : List ℚ) :
    listToPoly (trimCoeffs xs) = listToPoly xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [trimCoeffs]
      split
      next htrim =>
        by_cases hx : x = 0
        · simp [hx, listToPoly, ← ih, htrim]
        · simp [hx, listToPoly, ← ih, htrim]
      next y ys htrim =>
        simp [listToPoly, ← ih, htrim]


-- @@ L153-165 verbatim
private theorem listToPoly_weightedDerivativeCoeffs (n : Nat) (xs : List ℚ) :
    listToPoly (weightedDerivativeCoeffs n xs) =
      Polynomial.C (n : ℚ) * listToPoly xs +
        Polynomial.X * (listToPoly xs).derivative := by
  induction xs generalizing n with
  | nil => simp [weightedDerivativeCoeffs, listToPoly]
  | cons x xs ih =>
      simp only [weightedDerivativeCoeffs, listToPoly, ih,
        Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, map_mul]
      push_cast
      simp only [map_add, map_one]
      ring


-- @@ L167-175 verbatim
private theorem listToPoly_derivativeCoeffs (xs : List ℚ) :
    listToPoly (derivativeCoeffs xs) = (listToPoly xs).derivative := by
  cases xs with
  | nil => simp [derivativeCoeffs, listToPoly]
  | cons x xs =>
      rw [derivativeCoeffs, listToPoly_weightedDerivativeCoeffs]
      simp only [listToPoly, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X]
      norm_num [Polynomial.C_1]


-- @@ L177-186 verbatim
private theorem weightedDerivativeCoeffs_antiderivativeCoeffs
    (xs : List ℚ) (n : Nat) (hn : 0 < n) :
    weightedDerivativeCoeffs n (antiderivativeCoeffs n xs) = xs := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih =>
      simp only [antiderivativeCoeffs, weightedDerivativeCoeffs, List.cons.injEq]
      constructor
      · field_simp
      · exact ih (n + 1) (by omega)


-- @@ L188-189 verbatim
@[simp] theorem toPoly_zero : zero.toPoly = 0 := by
  rfl


-- @@ L191-192 verbatim
@[simp] theorem toPoly_constant (c : ℚ) : (constant c).toPoly = Polynomial.C c := by
  simp [constant, toPoly, listToPoly]


-- @@ L194-195 verbatim
@[simp] theorem toPoly_X : X.toPoly = Polynomial.X := by
  simp [X, toPoly, listToPoly]


-- @@ L197-198 verbatim
theorem toPoly_add (p q : QPoly) : (p.add q).toPoly = p.toPoly + q.toPoly := by
  simpa [add, toPoly] using listToPoly_addCoeffs p.coeffs.toList q.coeffs.toList


-- @@ L200-201 verbatim
theorem toPoly_mul (p q : QPoly) : (p.mul q).toPoly = p.toPoly * q.toPoly := by
  simpa [mul, toPoly] using listToPoly_mulCoeffs p.coeffs.toList q.coeffs.toList


-- @@ L203-205 verbatim
theorem toPoly_derivative (p : QPoly) : p.derivative.toPoly = p.toPoly.derivative := by
  simpa [derivative, toPoly, listToPoly_trimCoeffs] using
    listToPoly_derivativeCoeffs p.coeffs.toList


-- @@ L207-212 verbatim
theorem toPoly_antiderivative_derivative (p : QPoly) :
    p.antiderivative.toPoly.derivative = p.toPoly := by
  rw [← toPoly_derivative]
  simp only [derivative, antiderivative, derivativeCoeffs,
    weightedDerivativeCoeffs_antiderivativeCoeffs _ 1 (by omega), toPoly,
    listToPoly_trimCoeffs]


-- @@ L214-215 verbatim
theorem toPoly_trim (p : QPoly) : p.trim.toPoly = p.toPoly := by
  simpa [trim, toPoly] using listToPoly_trimCoeffs p.coeffs.toList


-- @@ L217-221 verbatim
/-! ### Sparse products with `1 - X^n` and monomial shifts

`mul` is dense (`O(deg p · deg q)`), which is far too slow for products of a
few hundred factors `1 - X^n` of total degree in the hundreds of thousands.
`mulOneSubPow` computes `p · (1 - X^n)` as `p - X^n · p` in linear time. -/


-- @@ L223-225 verbatim
private def negCoeffs : List ℚ → List ℚ
  | [] => []
  | x :: xs => (-x) :: negCoeffs xs


-- @@ L227-233 verbatim
private theorem listToPoly_negCoeffs (xs : List ℚ) :
    listToPoly (negCoeffs xs) = -listToPoly xs := by
  induction xs with
  | nil => simp [negCoeffs, listToPoly]
  | cons x xs ih =>
      simp only [negCoeffs, listToPoly, ih, map_neg]
      ring


-- @@ L235-242 verbatim
private theorem listToPoly_replicate_append (n : Nat) (xs : List ℚ) :
    listToPoly (List.replicate n 0 ++ xs) = Polynomial.X ^ n * listToPoly xs := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [listToPoly, ih, map_zero]
      ring


-- @@ L244-246 verbatim
/-- `X^k · p`, in linear time. -/
def shiftPow (p : QPoly) (k : Nat) : QPoly :=
  ⟨(List.replicate k 0 ++ p.coeffs.toList).toArray⟩


-- @@ L248-250 verbatim
theorem toPoly_shiftPow (p : QPoly) (k : Nat) :
    (p.shiftPow k).toPoly = Polynomial.X ^ k * p.toPoly := by
  simpa [shiftPow, toPoly] using listToPoly_replicate_append k p.coeffs.toList


-- @@ L252-254 verbatim
/-- `p · (1 - X^n)`, in linear time. -/
def mulOneSubPow (p : QPoly) (n : Nat) : QPoly :=
  ⟨(addCoeffs p.coeffs.toList (List.replicate n 0 ++ negCoeffs p.coeffs.toList)).toArray⟩


-- @@ L256-264 verbatim
theorem toPoly_mulOneSubPow (p : QPoly) (n : Nat) :
    (p.mulOneSubPow n).toPoly = p.toPoly * (1 - Polynomial.X ^ n) := by
  have h := listToPoly_addCoeffs p.coeffs.toList
    (List.replicate n 0 ++ negCoeffs p.coeffs.toList)
  rw [listToPoly_replicate_append, listToPoly_negCoeffs] at h
  show listToPoly (addCoeffs p.coeffs.toList
    (List.replicate n 0 ++ negCoeffs p.coeffs.toList)) = _
  rw [h, toPoly]
  ring


-- @@ L266-266 verbatim
/-! ### Composition and coefficient sums -/


-- @@ L268-270 verbatim
private def composeCoeffs (q : QPoly) : List ℚ → QPoly
  | [] => zero
  | c :: cs => (constant c).add (q.mul (composeCoeffs q cs))


-- @@ L272-274 verbatim
/-- Horner composition `p ∘ q`, exact over the rationals. -/
def compose (p q : QPoly) : QPoly :=
  composeCoeffs q p.coeffs.toList


-- @@ L276-282 verbatim
private theorem toPoly_composeCoeffs (q : QPoly) (cs : List ℚ) :
    (composeCoeffs q cs).toPoly = (listToPoly cs).comp q.toPoly := by
  induction cs with
  | nil => simp [composeCoeffs, listToPoly]
  | cons c cs ih =>
      simp only [composeCoeffs, toPoly_add, toPoly_constant, toPoly_mul, ih, listToPoly,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]


-- @@ L284-285 verbatim
theorem toPoly_compose (p q : QPoly) : (p.compose q).toPoly = p.toPoly.comp q.toPoly :=
  toPoly_composeCoeffs q p.coeffs.toList


-- @@ L287-291 verbatim
/-- Evaluating a composition evaluates the inner polynomial first. -/
theorem aeval_compose (p q : QPoly) (x : ℝ) :
    Polynomial.aeval x (p.compose q).toPoly =
      Polynomial.aeval (Polynomial.aeval x q.toPoly) p.toPoly := by
  rw [toPoly_compose, Polynomial.aeval_comp]


-- @@ L293-305 verbatim
private theorem aeval_listToPoly_eq_sum (xs : List ℚ) (x : ℝ) :
    Polynomial.aeval x (listToPoly xs) =
      ∑ j ∈ Finset.range xs.length, (xs.getD j 0 : ℝ) * x ^ j := by
  induction xs with
  | nil => simp [listToPoly]
  | cons c cs ih =>
      simp only [listToPoly, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, ih,
        List.length_cons]
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring


-- @@ L307-311 verbatim
/-- The represented polynomial is the finite sum of its coefficient list. -/
theorem aeval_toPoly_eq_sum (p : QPoly) (x : ℝ) :
    Polynomial.aeval x p.toPoly =
      ∑ j ∈ Finset.range p.coeffs.toList.length, (p.coeffs.toList.getD j 0 : ℝ) * x ^ j :=
  aeval_listToPoly_eq_sum p.coeffs.toList x


-- @@ L313-315 verbatim
private def listToExpr : List ℚ → Expr
  | [] => .const 0
  | x :: xs => .add (.const x) (.mul (.var 0) (listToExpr xs))


-- @@ L317-319 verbatim
/-- Convert to a single-variable Horner expression in variable `0`. -/
def toExpr (p : QPoly) : Expr :=
  listToExpr p.coeffs.toList


-- @@ L321-328 verbatim
private theorem eval_listToExpr (xs : List ℚ) (x : ℝ) :
    Expr.eval (fun _ => x) (listToExpr xs) = Polynomial.aeval x (listToPoly xs) := by
  induction xs with
  | nil => simp [listToExpr, listToPoly]
  | cons q qs ih =>
      simp only [listToExpr, listToPoly, Expr.eval, ih, map_add, map_mul,
        Polynomial.aeval_C, Polynomial.aeval_X]
      rfl


-- @@ L330-333 verbatim
/-- The Horner `Expr` and Mathlib polynomial have identical real semantics. -/
theorem eval_toExpr (p : QPoly) (x : ℝ) :
    Expr.eval (fun _ => x) p.toExpr = Polynomial.aeval x p.toPoly := by
  exact eval_listToExpr p.coeffs.toList x


-- @@ L335-339 verbatim
private theorem cast_evalCoeffs (xs : List ℚ) (x : ℚ) :
    ((evalCoeffs x xs : ℚ) : ℝ) = Expr.eval (fun _ => (x : ℝ)) (listToExpr xs) := by
  induction xs with
  | nil => simp [evalCoeffs, listToExpr]
  | cons c cs ih => simp [evalCoeffs, listToExpr, Expr.eval, ih]


-- @@ L341-343 verbatim
theorem cast_evalRat (p : QPoly) (x : ℚ) :
    ((p.evalRat x : ℚ) : ℝ) = Expr.eval (fun _ => (x : ℝ)) p.toExpr := by
  exact cast_evalCoeffs p.coeffs.toList x


-- @@ L345-372 verbatim
/-- The executable exact integral agrees with the interval integral of the
represented polynomial. -/
theorem integral_eval_toExpr (p : QPoly) (a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), Expr.eval (fun _ => x) p.toExpr) =
      (p.integralRat a b : ℝ) := by
  let q := p.antiderivative
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t => Expr.eval (fun _ => t) q.toExpr)
        (Expr.eval (fun _ => x) p.toExpr) x := by
    intro x
    have hq : q.toPoly.derivative = p.toPoly :=
      toPoly_antiderivative_derivative p
    have h := q.toPoly.hasDerivAt_aeval x
    rw [hq] at h
    simpa only [eval_toExpr] using h
  have hInt : IntervalIntegrable
      (fun x => Expr.eval (fun _ => x) p.toExpr) MeasureTheory.volume (a : ℝ) (b : ℝ) := by
    rw [show (fun x : ℝ => Expr.eval (fun _ => x) p.toExpr) =
        (fun x : ℝ => Polynomial.aeval x p.toPoly) by
      funext x
      exact eval_toExpr p x]
    exact p.toPoly.differentiable_aeval.continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    hInt]
  simp only [q, integralRat]
  rw [← cast_evalRat p.antiderivative b, ← cast_evalRat p.antiderivative a]
  norm_num


-- @@ L374-383 verbatim
/-- The analytic derivative of the Horner expression agrees with the formal
polynomial derivative. -/
theorem deriv_eval_toExpr (p : QPoly) (x : ℝ) :
    deriv (fun t : ℝ => Expr.eval (fun _ => t) p.toExpr) x =
      Polynomial.aeval x p.toPoly.derivative := by
  rw [show (fun t : ℝ => Expr.eval (fun _ => t) p.toExpr) =
      (fun t : ℝ => Polynomial.aeval t p.toPoly) by
    funext t
    exact eval_toExpr p t]
  exact (p.toPoly.hasDerivAt_aeval x).deriv


-- @@ L385-385 verbatim
end QPoly

-- @@ L386-386 verbatim
end LeanCert.Engine
