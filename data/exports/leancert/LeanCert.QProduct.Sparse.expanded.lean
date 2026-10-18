/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct.LimitCert
import LeanCert.Engine.Algebra.QPoly


-- @@ L9-25 verbatim
/-!
# Sparse exact q-product integrals

`finiteIntegralRat` expands the product over the powerset of the exponent set,
which is exact but exponential in `|S|`. This file evaluates the same integrals
by multiplying out `∏_{n ∈ S} (1 - X^n)` as an executable `QPoly` (linear time
per factor) and integrating the coefficient vector termwise, so prime
truncations with hundreds of primes become feasible certificate payloads.

* `qpolyOf S` — the product polynomial, with `aeval_qpolyOf : aeval u = qProd S u`;
* `finiteIntegralRatSparse S`, `momentRatSparse S k` — exact values of `F S`
  and `moment S k`;
* `truncatedIntegralRat S c` — the exact value of `∫₀ᶜ qProd S`;
* `primeFRatSparse`, `primeSandwichErrorRatSparse` and the sparse
  `DirectedLimitCert` for `primeLambda`, so `Validity.verify_limit_interval`
  can certify many digits of the prime constant.
-/


-- @@ L27-27 verbatim
namespace LeanCert.QProduct


-- @@ L29-29 verbatim
open LeanCert.Core LeanCert.Engine


-- @@ L31-31 verbatim
/-! ### The product polynomial -/


-- @@ L33-36 verbatim
/-- `∏ (1 - X^n)` over a list of exponents. -/
def qpolyOfList : List Nat → QPoly
  | [] => QPoly.constant 1
  | n :: ns => (qpolyOfList ns).mulOneSubPow n


-- @@ L38-44 verbatim
theorem toPoly_qpolyOfList (l : List Nat) :
    (qpolyOfList l).toPoly = (l.map fun n => 1 - Polynomial.X ^ n).prod := by
  induction l with
  | nil => simp [qpolyOfList, QPoly.toPoly_constant]
  | cons n ns ih =>
      simp only [qpolyOfList, QPoly.toPoly_mulOneSubPow, ih, List.map_cons, List.prod_cons]
      ring


-- @@ L46-48 verbatim
/-- `∏_{n ∈ S} (1 - X^n)` as an executable polynomial. -/
def qpolyOf (S : Finset Nat) : QPoly :=
  qpolyOfList (S.sort (· ≤ ·))


-- @@ L50-54 verbatim
theorem toPoly_qpolyOf (S : Finset Nat) :
    (qpolyOf S).toPoly = ∏ n ∈ S, (1 - Polynomial.X ^ n) := by
  unfold qpolyOf
  rw [toPoly_qpolyOfList, Finset.prod_eq_multiset_prod, ← Finset.sort_eq S (· ≤ ·),
    Multiset.map_coe, Multiset.prod_coe]


-- @@ L56-60 verbatim
/-- The product polynomial evaluates to the q-product profile. -/
theorem aeval_qpolyOf (S : Finset Nat) (u : ℝ) :
    Polynomial.aeval u (qpolyOf S).toPoly = qProd S u := by
  rw [toPoly_qpolyOf, qProd]
  simp


-- @@ L62-64 verbatim
theorem eval_toExpr_qpolyOf (S : Finset Nat) (u : ℝ) :
    Expr.eval (fun _ => u) (qpolyOf S).toExpr = qProd S u := by
  rw [QPoly.eval_toExpr, aeval_qpolyOf]


-- @@ L66-66 verbatim
/-! ### Exact integrals -/


-- @@ L68-70 verbatim
/-- Exact `F S`, sparse evaluation. -/
def finiteIntegralRatSparse (S : Finset Nat) : ℚ :=
  (qpolyOf S).integralRat 0 1


-- @@ L72-74 verbatim
/-- Exact `moment S k`, sparse evaluation. -/
def momentRatSparse (S : Finset Nat) (k : Nat) : ℚ :=
  ((qpolyOf S).shiftPow k).integralRat 0 1


-- @@ L76-78 verbatim
/-- Exact `∫₀ᶜ qProd S` for a rational cutoff `c`. -/
def truncatedIntegralRat (S : Finset Nat) (c : ℚ) : ℚ :=
  (qpolyOf S).integralRat 0 c


-- @@ L80-85 verbatim
theorem truncatedIntegralRat_correct (S : Finset Nat) (c : ℚ) :
    (truncatedIntegralRat S c : ℝ) = ∫ u in (0 : ℝ)..(c : ℝ), qProd S u := by
  unfold truncatedIntegralRat
  rw [← QPoly.integral_eval_toExpr]
  simp only [Rat.cast_zero]
  exact intervalIntegral.integral_congr fun u _ => eval_toExpr_qpolyOf S u


-- @@ L87-90 verbatim
theorem finiteIntegralRatSparse_correct (S : Finset Nat) :
    (finiteIntegralRatSparse S : ℝ) = F S := by
  have h := truncatedIntegralRat_correct S 1
  simpa [truncatedIntegralRat, finiteIntegralRatSparse, F] using h


-- @@ L92-99 verbatim
theorem momentRatSparse_correct (S : Finset Nat) (k : Nat) :
    (momentRatSparse S k : ℝ) = moment S k := by
  unfold momentRatSparse moment
  rw [← QPoly.integral_eval_toExpr]
  simp only [Rat.cast_zero, Rat.cast_one]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [QPoly.eval_toExpr, QPoly.toPoly_shiftPow, map_mul, map_pow, Polynomial.aeval_X,
    aeval_qpolyOf, mul_comm]


-- @@ L101-106 verbatim
/-- The sparse and powerset evaluations agree as rationals. -/
theorem finiteIntegralRatSparse_eq (S : Finset Nat) :
    finiteIntegralRatSparse S = finiteIntegralRat S := by
  have h : (finiteIntegralRatSparse S : ℝ) = (finiteIntegralRat S : ℝ) := by
    rw [finiteIntegralRatSparse_correct, finiteIntegralRat_correct]
  exact_mod_cast h


-- @@ L108-112 verbatim
theorem momentRatSparse_eq (S : Finset Nat) (k : Nat) :
    momentRatSparse S k = momentRat S k := by
  have h : (momentRatSparse S k : ℝ) = (momentRat S k : ℝ) := by
    rw [momentRatSparse_correct, momentRat_correct]
  exact_mod_cast h


-- @@ L114-114 verbatim
/-! ### Prime truncations -/


-- @@ L116-118 verbatim
/-- Sparse exact value of the prime truncation integral. -/
def primeFRatSparse (N : Nat) : ℚ :=
  finiteIntegralRatSparse (primesLE N)


-- @@ L120-122 verbatim
/-- Sparse exact error integral for the prime sandwich. -/
def primeSandwichErrorRatSparse (N m : Nat) : ℚ :=
  momentRatSparse ((primesLE N).filter (fun p => p ≠ 2)) m


-- @@ L124-125 verbatim
theorem primeFRatSparse_eq (N : Nat) : primeFRatSparse N = primeFRat N :=
  finiteIntegralRatSparse_eq _


-- @@ L127-129 verbatim
theorem primeSandwichErrorRatSparse_eq (N m : Nat) :
    primeSandwichErrorRatSparse N m = primeSandwichErrorRat N m :=
  momentRatSparse_eq _ _


-- @@ L131-133 verbatim
theorem primeLambda_le_shiftedTruncSparse (N : ℕ) :
    primeLambda ≤ (primeFRatSparse (N + 2) : ℝ) := by
  rw [primeFRatSparse_eq]; exact primeLambda_le_shiftedTrunc N


-- @@ L135-140 verbatim
theorem shiftedTruncSparse_sub_tail_le_primeLambda (N : ℕ) :
    (primeFRatSparse (N + 2) : ℝ) -
        (primeSandwichErrorRatSparse (N + 2) (oddAbove (N + 2)) : ℝ) ≤
      primeLambda := by
  rw [primeFRatSparse_eq, primeSandwichErrorRatSparse_eq]
  exact shiftedTrunc_sub_tail_le_primeLambda N


-- @@ L142-150 verbatim
/-- The prime q-product limit as a `DirectedLimitCert` with sparse exact
truncations; `Validity.verify_limit_interval` turns a `native_decide` on
`checkLimitInterval` into a real enclosure of `primeLambda`. -/
noncomputable def primeLambdaLimitCertSparse : Validity.DirectedLimitCert where
  approx N := primeFRatSparse (N + 2)
  tail N := primeSandwichErrorRatSparse (N + 2) (oddAbove (N + 2))
  limit := primeLambda
  limit_le_approx := primeLambda_le_shiftedTruncSparse
  approx_sub_tail_le_limit := shiftedTruncSparse_sub_tail_le_primeLambda


-- @@ L152-152 verbatim
end LeanCert.QProduct
