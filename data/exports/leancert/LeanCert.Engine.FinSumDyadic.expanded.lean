/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalDyadic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat


-- @@ L10-55 verbatim
/-!
# General Finite Sum Evaluator with O(1) Proof Size

This module provides a general accumulator-based evaluator for finite sums
over `Core.Expr`, achieving O(1) proof term size via `native_decide`.

## Motivation

`finsum_expand` expands `∑ k ∈ Icc a b, f k` into `f a + f(a+1) + ... + f b`,
creating an O(N) expression tree that blows up for N > ~100.

`ReflectiveSum` solves this with an accumulator + `native_decide`, but is
hardcoded for one specific function (BKLNW's `x^(1/k - 1/3)`).

This module generalizes the pattern: any function expressible as a `Core.Expr`
(with `var 0` as the summation index) can be bounded via the same accumulator
loop, using `LeanCert.Internal.Dyadic.evalUnchecked` per term.

## Main definitions

* `finSumDyadic` - Interval bound for `∑ k ∈ Icc a b, Expr.eval [k] body`
* `checkFinSumUpperBound` - Certificate checker for upper bounds
* `checkFinSumLowerBound` - Certificate checker for lower bounds
* `verify_finsum_upper` - Bridge theorem: checker = true → sum ≤ target
* `verify_finsum_lower` - Bridge theorem: checker = true → target ≤ sum

## Usage

```lean
-- Verify ∑ k ∈ Icc 1 100, 1/k² ≤ 2 with O(1) proof:
example : checkFinSumUpperBound (Expr.inv (Expr.mul (Expr.var 0) (Expr.var 0)))
    1 100 2 { precision := -53 } = true := by native_decide
```

## Architecture

```
LeanCert.Internal.Dyadic.evalUnchecked (per-term, from IntervalEvalDyadic.lean)
  ↓
finSumAux (accumulator loop)
  ↓
checkFinSumUpperBound : Bool
  ↓  native_decide
verify_finsum_upper (bridge theorem)
```
-/


-- @@ L57-57 verbatim
namespace LeanCert.Engine


-- @@ L59-59 verbatim
open LeanCert.Core


-- @@ L61-64 verbatim
/-! ### Sum Lemmas

These are general lemmas for peeling elements from Finset sums.
Reusable by any accumulator-based sum evaluator. -/


-- @@ L66-75 verbatim
/-- Sum over Icc starting at first element -/
theorem Finset.sum_Icc_eq_add_sum_Ioc' {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ)
    (h : a ≤ b) : ∑ k ∈ Finset.Icc a b, f k = f a + ∑ k ∈ Finset.Ioc a b, f k := by
  rw [← Finset.sum_insert (s := Finset.Ioc a b) (a := a)]
  · congr 1
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · simp only [Finset.mem_Ioc]
    omega


-- @@ L77-81 verbatim
/-- Ioc a b equals Icc (a+1) b -/
theorem Finset.Ioc_eq_Icc_succ' (a b : ℕ) : Finset.Ioc a b = Finset.Icc (a + 1) b := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega


-- @@ L83-83 verbatim
/-! ### Environment Helpers -/


-- @@ L85-91 verbatim
/-- Environment for evaluating the sum body at index k.
    Maps all variables to the singleton interval [k, k].

    For single-variable bodies (var 0 = summation index), this is sufficient.
    For multi-variable bodies, a shifted version would be needed (future work). -/
def sumBodyEnvSimple (k : Nat) (prec : Int) : IntervalDyadicEnv :=
  fun _ => IntervalDyadic.ofIntervalRat (IntervalRat.singleton (k : ℚ)) prec


-- @@ L93-94 verbatim
/-- Real environment: all variables equal (k : ℝ). -/
noncomputable def sumBodyRealEnv (k : Nat) : Nat → ℝ := fun _ => (k : ℝ)


-- @@ L96-104 verbatim
/-- The real environment is contained in the dyadic environment. -/
theorem sumBodyEnvSimple_correct (k : Nat) (prec : Int) (hprec : prec ≤ 0) :
    envMemDyadic (sumBodyRealEnv k) (sumBodyEnvSimple k prec) := by
  intro i
  simp only [sumBodyRealEnv, sumBodyEnvSimple]
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  have : ((k : ℚ) : ℝ) = (k : ℝ) := by push_cast; ring
  rw [← this]
  exact IntervalRat.mem_singleton (k : ℚ)


-- @@ L106-106 verbatim
/-! ### Per-term Evaluation -/


-- @@ L108-110 verbatim
/-- Evaluate a single term of the sum: body evaluated at index k. -/
def evalSumTermDyadic (body : Expr) (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  LeanCert.Internal.Dyadic.evalUnchecked body (sumBodyEnvSimple k cfg.precision) cfg


-- @@ L112-112 verbatim
/-! ### Accumulator Loop -/


-- @@ L114-115 verbatim
/-- Zero interval for accumulator initialization. -/
def finSumZero : IntervalDyadic := IntervalDyadic.singleton Core.Dyadic.zero


-- @@ L117-121 verbatim
/-- Zero is in the zero interval. -/
theorem mem_finSumZero : (0 : ℝ) ∈ finSumZero := by
  simp only [finSumZero, IntervalDyadic.singleton, IntervalDyadic.mem_def]
  have hz : Core.Dyadic.zero.toRat = 0 := Core.Dyadic.toRat_zero
  simp only [hz, Rat.cast_zero, le_refl, and_self]


-- @@ L123-133 verbatim
/-- Accumulator loop for general finite sums.
    Computes an interval containing `∑ k ∈ Icc current limit, Expr.eval [k] body`. -/
def finSumAux (body : Expr) (current limit : Nat)
    (acc : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  if h : current > limit then
    acc
  else
    let term := evalSumTermDyadic body current cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    finSumAux body (current + 1) limit newAcc cfg
  termination_by limit + 1 - current


-- @@ L135-137 verbatim
/-- Main entry point: interval for `∑ k ∈ Icc a b, Expr.eval [k] body`. -/
def finSumDyadic (body : Expr) (a b : Nat) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  finSumAux body a b finSumZero cfg


-- @@ L139-139 verbatim
/-! ### Certificate Checkers -/


-- @@ L141-144 verbatim
/-- Check if `∑ k ∈ Icc a b, Expr.eval [k] body ≤ target`. -/
def checkFinSumUpperBound (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadic body a b cfg).upperBoundedBy target


-- @@ L146-149 verbatim
/-- Check if `target ≤ ∑ k ∈ Icc a b, Expr.eval [k] body`. -/
def checkFinSumLowerBound (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadic body a b cfg).lowerBoundedBy target


-- @@ L151-151 verbatim
/-! ### Correctness Theorems -/


-- @@ L153-160 verbatim
/-- Per-term correctness: the true value is in the computed interval. -/
theorem mem_evalSumTermDyadic (body : Expr) (hsupp : ExprSupportedCore body)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    Expr.eval (sumBodyRealEnv k) body ∈ evalSumTermDyadic body k cfg :=
  evalIntervalDyadic_correct body hsupp (sumBodyRealEnv k)
    (sumBodyEnvSimple k cfg.precision) (sumBodyEnvSimple_correct k cfg.precision hprec)
    cfg hprec hdom


-- @@ L162-202 verbatim
/-- Accumulator correctness: if we've accumulated correctly so far,
    adding terms preserves correctness.

    Proof structure mirrors `mem_bklnwSumAux` from ReflectiveSum.lean. -/
theorem mem_finSumAux (body : Expr) (hsupp : ExprSupportedCore body)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, current ≤ k → k ≤ limit →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumAux body current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold finSumAux
    split_ifs with h
    · -- Base case: current > limit, sum is empty
      simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · -- Inductive case: peel first element and recurse
      have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      -- Split the sum
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      -- Reassociate
      rw [← add_assoc]
      -- Term membership
      have hterm := mem_evalSumTermDyadic body hsupp current cfg hprec
        (hdom current (Nat.le_refl current) hcur_le)
      -- (partialSum + term) ∈ newAcc
      have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv current) body ∈
          (IntervalDyadic.add acc (evalSumTermDyadic body current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      -- Apply induction hypothesis
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hdom' : ∀ k, current + 1 ≤ k → k ≤ limit →
          evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
        fun k hk1 hk2 => hdom k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hdom' rfl


-- @@ L204-216 verbatim
/-- Main correctness theorem: the computed interval contains the true sum.

    This is the "golden theorem" connecting the computable evaluator to the
    mathematical definition of the finite sum. -/
theorem mem_finSumDyadic (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body) ∈ finSumDyadic body a b cfg := by
  unfold finSumDyadic
  have h := mem_finSumAux body hsupp a b finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h


-- @@ L218-218 verbatim
/-! ### Bridge Theorems -/


-- @@ L220-234 verbatim
/-- If checkFinSumUpperBound returns true, the sum is bounded above.

    This connects `native_decide` verification to mathematical truth. -/
theorem verify_finsum_upper (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumUpperBound body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  have hmem := mem_finSumDyadic body hsupp a b cfg hprec hdom
  have hhi : ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤
      ((finSumDyadic body a b cfg).hi.toRat : ℝ) := hmem.2
  simp only [checkFinSumUpperBound, IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)


-- @@ L236-248 verbatim
/-- If checkFinSumLowerBound returns true, the sum is bounded below. -/
theorem verify_finsum_lower (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumLowerBound body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  have hmem := mem_finSumDyadic body hsupp a b cfg hprec hdom
  have hlo : ((finSumDyadic body a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := hmem.1
  simp only [checkFinSumLowerBound, IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo


-- @@ L250-250 verbatim
/-! ### Domain Validity Checking Over Range -/


-- @@ L252-259 verbatim
/-- Check domain validity for all indices in [current, limit]. -/
def checkDomainValidAllAux (body : Expr) (current limit : Nat)
    (cfg : DyadicConfig) : Bool :=
  if current > limit then true
  else
    checkDomainValidDyadic body (sumBodyEnvSimple current cfg.precision) cfg &&
    checkDomainValidAllAux body (current + 1) limit cfg
  termination_by limit + 1 - current


-- @@ L261-263 verbatim
/-- Check domain validity for all indices in [a, b]. -/
def checkDomainValidAll (body : Expr) (a b : Nat) (cfg : DyadicConfig) : Bool :=
  checkDomainValidAllAux body a b cfg


-- @@ L265-272 verbatim
/-- Structured candidate evaluation used by the tactic to distinguish a
mathematical domain obstruction from an enclosure that is merely too wide.
This result is untrusted; successful candidates are still certified by the
existing combined Boolean checker and Golden Theorem. -/
inductive FinSumEvaluation where
  | success (enclosure : IntervalDyadic)
  | domainObstruction (index : Nat)
  deriving Repr, Inhabited


-- @@ L274-280 verbatim
def firstInvalidFinSumIndex (body : Expr) (current limit : Nat)
    (cfg : DyadicConfig) : Option Nat :=
  if current > limit then none
  else if checkDomainValidDyadic body (sumBodyEnvSimple current cfg.precision) cfg then
    firstInvalidFinSumIndex body (current + 1) limit cfg
  else some current
  termination_by limit + 1 - current


-- @@ L282-288 verbatim
/-- Evaluate one range candidate exactly once for classification and
telemetry. -/
def evaluateFinSumCandidate (body : Expr) (a b : Nat)
    (cfg : DyadicConfig) : FinSumEvaluation :=
  match firstInvalidFinSumIndex body a b cfg with
  | some index => .domainObstruction index
  | none => .success (finSumDyadic body a b cfg)


-- @@ L290-314 verbatim
/-- Bridge theorem: if checkDomainValidAllAux returns true,
    domain validity holds for all indices in [current, limit]. -/
theorem checkDomainValidAllAux_correct (body : Expr) (current limit : Nat)
    (cfg : DyadicConfig)
    (h : checkDomainValidAllAux body current limit cfg = true) :
    ∀ k, current ≤ k → k ≤ limit →
      evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current with
  | ind m ih =>
    unfold checkDomainValidAllAux at h
    split_ifs at h with hgt
    · -- current > limit: vacuously true
      intro k hk1 hk2; omega
    · -- current ≤ limit: split the && check
      have hcur_le : current ≤ limit := Nat.le_of_not_gt hgt
      rw [Bool.and_eq_true] at h
      intro k hk1 hk2
      by_cases heq : k = current
      · subst heq
        exact checkDomainValidDyadic_correct body
          (sumBodyEnvSimple k cfg.precision) cfg h.1
      · have hk1' : current + 1 ≤ k := by omega
        have hm' : limit + 1 - (current + 1) < m := by omega
        exact ih (limit + 1 - (current + 1)) hm' (current + 1) h.2 rfl k hk1' hk2


-- @@ L316-321 verbatim
/-- Bridge theorem for checkDomainValidAll. -/
theorem checkDomainValidAll_correct (body : Expr) (a b : Nat) (cfg : DyadicConfig)
    (h : checkDomainValidAll body a b cfg = true) :
    ∀ k, a ≤ k → k ≤ b →
      evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
  checkDomainValidAllAux_correct body a b cfg h


-- @@ L323-323 verbatim
/-! ### Combined Certificate Checkers (Domain + Bound) -/


-- @@ L325-328 verbatim
/-- Check upper bound with integrated domain validity. -/
def checkFinSumUpperBoundFull (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  checkDomainValidAll body a b cfg && checkFinSumUpperBound body a b target cfg


-- @@ L330-333 verbatim
/-- Check lower bound with integrated domain validity. -/
def checkFinSumLowerBoundFull (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  checkDomainValidAll body a b cfg && checkFinSumLowerBound body a b target cfg


-- @@ L335-335 verbatim
/-! ### Combined Bridge Theorems (ExprSupportedCore) -/


-- @@ L337-346 verbatim
/-- If checkFinSumUpperBoundFull returns true, the sum is bounded above.
    Domain validity is verified as part of the check. -/
theorem verify_finsum_upper_full (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundFull body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_upper body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2


-- @@ L348-357 verbatim
/-- If checkFinSumLowerBoundFull returns true, the sum is bounded below.
    Domain validity is verified as part of the check. -/
theorem verify_finsum_lower_full (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundFull body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_lower body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2


-- @@ L359-359 verbatim
/-! ### Checked Correctness Chain -/


-- @@ L361-368 verbatim
/-- Per-term correctness for arbitrary expression bodies. -/
theorem mem_evalSumTermDyadic_checked (body : Expr)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    Expr.eval (sumBodyRealEnv k) body ∈ evalSumTermDyadic body k cfg :=
  evalIntervalDyadic_correct_of_domain body (sumBodyRealEnv k)
    (sumBodyEnvSimple k cfg.precision) (sumBodyEnvSimple_correct k cfg.precision hprec)
    cfg hprec hdom


-- @@ L370-400 verbatim
/-- Accumulator correctness for arbitrary expression bodies. -/
theorem mem_finSumAux_checked (body : Expr)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, current ≤ k → k ≤ limit →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumAux body current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold finSumAux
    split_ifs with h
    · simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      rw [← add_assoc]
      have hterm := mem_evalSumTermDyadic_checked body current cfg hprec
        (hdom current (Nat.le_refl current) hcur_le)
      have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv current) body ∈
          (IntervalDyadic.add acc (evalSumTermDyadic body current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hdom' : ∀ k, current + 1 ≤ k → k ≤ limit →
          evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
        fun k hk1 hk2 => hdom k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hdom' rfl


-- @@ L402-411 verbatim
/-- Golden theorem for arbitrary expression bodies. -/
theorem mem_finSumDyadic_checked (body : Expr)
    (a b : Nat) (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body) ∈ finSumDyadic body a b cfg := by
  unfold finSumDyadic
  have h := mem_finSumAux_checked body a b finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h


-- @@ L413-425 verbatim
/-- Bridge theorem: upper bound for arbitrary expressions. -/
theorem verify_finsum_upper_checked (body : Expr)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumUpperBound body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  have hmem := mem_finSumDyadic_checked body a b cfg hprec hdom
  have hhi : ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤
      ((finSumDyadic body a b cfg).hi.toRat : ℝ) := hmem.2
  simp only [checkFinSumUpperBound, IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)


-- @@ L427-439 verbatim
/-- Bridge theorem: lower bound for arbitrary expressions. -/
theorem verify_finsum_lower_checked (body : Expr)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumLowerBound body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  have hmem := mem_finSumDyadic_checked body a b cfg hprec hdom
  have hlo : ((finSumDyadic body a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := hmem.1
  simp only [checkFinSumLowerBound, IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo


-- @@ L441-441 verbatim
/-! ### Combined Bridge Theorems (arbitrary expressions) -/


-- @@ L443-451 verbatim
/-- Combined upper bound check for arbitrary expression bodies. -/
theorem verify_finsum_upper_full_checked (body : Expr)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundFull body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_upper_checked body a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2


-- @@ L453-461 verbatim
/-- Combined lower bound check for arbitrary expression bodies. -/
theorem verify_finsum_lower_full_checked (body : Expr)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundFull body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_lower_checked body a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2


-- @@ L463-471 verbatim
/-! ## List-Based Accumulator for Arbitrary Finite Sets

Instead of iterating over a contiguous range `[a, b]`, this section iterates over
an explicit `List Nat` of indices. This enables `finsum_bound` to handle arbitrary
Finsets like `{1, 3, 5, 7}`, `Finset.range n`, `Finset.Ico a b`, etc.

The key Mathlib lemma connecting `List` and `Finset` sums:
  `List.sum_toFinset (f : ι → M) (hl : l.Nodup) : l.toFinset.sum f = (l.map f).sum`
-/


-- @@ L473-473 verbatim
/-! ### List Accumulator Loop -/


-- @@ L475-483 verbatim
/-- Accumulator loop iterating over a list of indices. -/
def finSumAuxList (body : Expr) (indices : List Nat)
    (acc : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  match indices with
  | [] => acc
  | k :: rest =>
    let term := evalSumTermDyadic body k cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    finSumAuxList body rest newAcc cfg


-- @@ L485-488 verbatim
/-- Interval for `∑ k ∈ indices.toFinset, Expr.eval [k] body`. -/
def finSumDyadicList (body : Expr) (indices : List Nat)
    (cfg : DyadicConfig := {}) : IntervalDyadic :=
  finSumAuxList body indices finSumZero cfg


-- @@ L490-490 verbatim
/-! ### List Certificate Checkers -/


-- @@ L492-495 verbatim
/-- Check if `∑ k ∈ indices.toFinset, Expr.eval [k] body ≤ target`. -/
def checkFinSumUpperBoundList (body : Expr) (indices : List Nat)
    (target : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadicList body indices cfg).upperBoundedBy target


-- @@ L497-500 verbatim
/-- Check if `target ≤ ∑ k ∈ indices.toFinset, Expr.eval [k] body`. -/
def checkFinSumLowerBoundList (body : Expr) (indices : List Nat)
    (target : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadicList body indices cfg).lowerBoundedBy target


-- @@ L502-505 verbatim
/-- Check domain validity for all indices in a list. -/
def checkDomainValidAllList (body : Expr) (indices : List Nat)
    (cfg : DyadicConfig) : Bool :=
  indices.all fun k => checkDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg


-- @@ L507-510 verbatim
def firstInvalidFinSumListIndex (body : Expr) (indices : List Nat)
    (cfg : DyadicConfig) : Option Nat :=
  indices.find? fun k =>
    !(checkDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)


-- @@ L512-518 verbatim
/-- Evaluate one explicit-index candidate exactly once for classification and
telemetry. -/
def evaluateFinSumListCandidate (body : Expr) (indices : List Nat)
    (cfg : DyadicConfig) : FinSumEvaluation :=
  match firstInvalidFinSumListIndex body indices cfg with
  | some index => .domainObstruction index
  | none => .success (finSumDyadicList body indices cfg)


-- @@ L520-528 verbatim
/-- Domain validity correctness for list-based checker. -/
theorem checkDomainValidAllList_correct (body : Expr) (indices : List Nat)
    (cfg : DyadicConfig)
    (h : checkDomainValidAllList body indices cfg = true) :
    ∀ k, k ∈ indices →
      evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg := by
  intro k hk
  simp only [checkDomainValidAllList] at h
  exact checkDomainValidDyadic_correct body _ cfg (List.all_eq_true.mp h k hk)


-- @@ L530-530 verbatim
/-! ### List Combined Checkers -/


-- @@ L532-538 verbatim
/-- Combined check: S = indices.toFinset ∧ Nodup ∧ domain ∧ upper bound. -/
def checkFinSumUpperBoundListFull (body : Expr) (S : Finset Nat)
    (indices : List Nat) (target : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  decide (S = indices.toFinset) &&
  indices.Nodup &&
  checkDomainValidAllList body indices cfg &&
  checkFinSumUpperBoundList body indices target cfg


-- @@ L540-546 verbatim
/-- Combined check: S = indices.toFinset ∧ Nodup ∧ domain ∧ lower bound. -/
def checkFinSumLowerBoundListFull (body : Expr) (S : Finset Nat)
    (indices : List Nat) (target : ℚ) (cfg : DyadicConfig := {}) : Bool :=
  decide (S = indices.toFinset) &&
  indices.Nodup &&
  checkDomainValidAllList body indices cfg &&
  checkFinSumLowerBoundList body indices target cfg


-- @@ L548-548 verbatim
/-! ### List Correctness Theorems (ExprSupportedCore) -/


-- @@ L550-572 verbatim
/-- Accumulator correctness for list iteration. -/
theorem mem_finSumAuxList (body : Expr) (hsupp : ExprSupportedCore body)
    (indices : List Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, k ∈ indices →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + (indices.map (fun k => Expr.eval (sumBodyRealEnv k) body)).sum)
      ∈ finSumAuxList body indices acc cfg := by
  induction indices generalizing acc partialSum with
  | nil =>
    simp only [List.map_nil, List.sum_nil, add_zero, finSumAuxList]
    exact hacc
  | cons k rest ih =>
    simp only [finSumAuxList, List.map_cons, List.sum_cons]
    rw [← add_assoc]
    have hterm := mem_evalSumTermDyadic body hsupp k cfg hprec
      (hdom k (.head rest))
    have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv k) body ∈
        (IntervalDyadic.add acc (evalSumTermDyadic body k cfg)).roundOut cfg.precision := by
      apply IntervalDyadic.roundOut_contains
      exact IntervalDyadic.mem_add hacc hterm
    exact ih _ _ hnewAcc (fun j hj => hdom j (.tail k hj))


-- @@ L574-586 verbatim
/-- Golden theorem for list-based sum: the interval contains the true sum. -/
theorem mem_finSumDyadicList (body : Expr) (hsupp : ExprSupportedCore body)
    (indices : List Nat) (hnodup : indices.Nodup)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, k ∈ indices →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ indices.toFinset, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumDyadicList body indices cfg := by
  unfold finSumDyadicList
  rw [List.sum_toFinset _ hnodup]
  have h := mem_finSumAuxList body hsupp indices finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h


-- @@ L588-588 verbatim
/-! ### List Bridge Theorems (ExprSupportedCore) -/


-- @@ L590-605 verbatim
/-- If checkFinSumUpperBoundListFull returns true, the sum is bounded above.
    This is the main theorem used by the tactic. -/
theorem verify_finsum_upper_list_full (body : Expr) (hsupp : ExprSupportedCore body)
    (S : Finset Nat) (indices : List Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundListFull body S indices target cfg = true) :
    ∑ k ∈ S, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨⟨heq, hnodup⟩, hdomAll⟩, hbound⟩ := h_check
  rw [heq]
  have hdom := checkDomainValidAllList_correct body indices cfg hdomAll
  have hmem := mem_finSumDyadicList body hsupp indices hnodup cfg hprec hdom
  exact le_trans hmem.2 (by
    simp only [checkFinSumUpperBoundList, IntervalDyadic.upperBoundedBy,
      decide_eq_true_eq] at hbound
    exact_mod_cast hbound)


-- @@ L607-621 verbatim
/-- If checkFinSumLowerBoundListFull returns true, the sum is bounded below. -/
theorem verify_finsum_lower_list_full (body : Expr) (hsupp : ExprSupportedCore body)
    (S : Finset Nat) (indices : List Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundListFull body S indices target cfg = true) :
    target ≤ ∑ k ∈ S, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨⟨heq, hnodup⟩, hdomAll⟩, hbound⟩ := h_check
  rw [heq]
  have hdom := checkDomainValidAllList_correct body indices cfg hdomAll
  have hmem := mem_finSumDyadicList body hsupp indices hnodup cfg hprec hdom
  exact le_trans (by
    simp only [checkFinSumLowerBoundList, IntervalDyadic.lowerBoundedBy,
      decide_eq_true_eq] at hbound
    exact_mod_cast hbound) hmem.1


-- @@ L623-623 verbatim
/-! ### List Correctness Theorems (arbitrary expressions) -/


-- @@ L625-647 verbatim
/-- Accumulator correctness for arbitrary expression bodies over a list. -/
theorem mem_finSumAuxList_checked (body : Expr)
    (indices : List Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, k ∈ indices →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + (indices.map (fun k => Expr.eval (sumBodyRealEnv k) body)).sum)
      ∈ finSumAuxList body indices acc cfg := by
  induction indices generalizing acc partialSum with
  | nil =>
    simp only [List.map_nil, List.sum_nil, add_zero, finSumAuxList]
    exact hacc
  | cons k rest ih =>
    simp only [finSumAuxList, List.map_cons, List.sum_cons]
    rw [← add_assoc]
    have hterm := mem_evalSumTermDyadic_checked body k cfg hprec
      (hdom k (.head rest))
    have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv k) body ∈
        (IntervalDyadic.add acc (evalSumTermDyadic body k cfg)).roundOut cfg.precision := by
      apply IntervalDyadic.roundOut_contains
      exact IntervalDyadic.mem_add hacc hterm
    exact ih _ _ hnewAcc (fun j hj => hdom j (.tail k hj))


-- @@ L649-661 verbatim
/-- Golden theorem for arbitrary expressions over a list. -/
theorem mem_finSumDyadicList_checked (body : Expr)
    (indices : List Nat) (hnodup : indices.Nodup)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, k ∈ indices →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ indices.toFinset, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumDyadicList body indices cfg := by
  unfold finSumDyadicList
  rw [List.sum_toFinset _ hnodup]
  have h := mem_finSumAuxList_checked body indices finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h


-- @@ L663-663 verbatim
/-! ### List Bridge Theorems (arbitrary expressions) -/


-- @@ L665-679 verbatim
/-- Combined upper bound for arbitrary expressions over a list. -/
theorem verify_finsum_upper_list_full_checked (body : Expr)
    (S : Finset Nat) (indices : List Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundListFull body S indices target cfg = true) :
    ∑ k ∈ S, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨⟨heq, hnodup⟩, hdomAll⟩, hbound⟩ := h_check
  rw [heq]
  have hdom := checkDomainValidAllList_correct body indices cfg hdomAll
  have hmem := mem_finSumDyadicList_checked body indices hnodup cfg hprec hdom
  exact le_trans hmem.2 (by
    simp only [checkFinSumUpperBoundList, IntervalDyadic.upperBoundedBy,
      decide_eq_true_eq] at hbound
    exact_mod_cast hbound)


-- @@ L681-695 verbatim
/-- Combined lower bound for arbitrary expressions over a list. -/
theorem verify_finsum_lower_list_full_checked (body : Expr)
    (S : Finset Nat) (indices : List Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundListFull body S indices target cfg = true) :
    target ≤ ∑ k ∈ S, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨⟨heq, hnodup⟩, hdomAll⟩, hbound⟩ := h_check
  rw [heq]
  have hdom := checkDomainValidAllList_correct body indices cfg hdomAll
  have hmem := mem_finSumDyadicList_checked body indices hnodup cfg hprec hdom
  exact le_trans (by
    simp only [checkFinSumLowerBoundList, IntervalDyadic.lowerBoundedBy,
      decide_eq_true_eq] at hbound
    exact_mod_cast hbound) hmem.1


-- @@ L697-697 verbatim
end LeanCert.Engine
