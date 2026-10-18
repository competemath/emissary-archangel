/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumBound


-- @@ L8-14 verbatim
/-!
# Tests for `finsum_bound`

Verifies that the `finsum_bound` tactic can prove bounds on finite sums
with O(1) proof size via `native_decide`. Covers auto-reify mode, witness mode
(`using`), auto-hmem witness mode (`auto`), Fin n sums, and various Finset types.
-/


-- @@ L16-16 verbatim
namespace LeanCert.Test.FinSumBound


-- @@ L18-18 verbatim
open Lean Meta Elab Tactic

-- @@ L19-19 verbatim
open LeanCert.Tactic


-- @@ L21-21 verbatim
set_option linter.unusedTactic false


-- @@ L23-25 verbatim
/-! ### Basic Icc sums -/

-- Sum of constants (upper)

-- @@ L26-29 verbatim
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound

-- Sum of constants (lower)

-- @@ L30-33 verbatim
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_bound

-- Singleton sum

-- @@ L34-37 verbatim
example : ∑ _k ∈ Finset.Icc 5 5, (1 : ℝ) ≤ 2 := by
  finsum_bound

-- Empty sum

-- @@ L38-41 verbatim
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_bound

-- Sum using the index: ∑ ↑k (Nat → ℝ cast)

-- @@ L42-45 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_bound

-- Shifted index cast: Nat.cast (k + 1)

-- @@ L46-49 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑(k + 1) : ℝ) ≤ 66 := by
  finsum_bound

-- Scaled index cast: Nat.cast (2 * k)

-- @@ L50-53 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑(2 * k) : ℝ) ≤ 111 := by
  finsum_bound

-- Transcendental: ∑ exp(constant)

-- @@ L54-57 verbatim
example : ∑ _k ∈ Finset.Icc 1 5, Real.exp (1 : ℝ) ≤ 15 := by
  finsum_bound

-- Larger sum: 100 terms (would blow up with finsum_expand)

-- @@ L58-59 verbatim
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_bound


-- @@ L61-63 verbatim
/-! ### Bodies with inv/log (domain validity checked per-k) -/

-- inv: ∑ 1/(k*k) upper bound (uses checked evaluation)

-- @@ L64-67 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound

-- inv: harmonic partial sum lower bound

-- @@ L68-71 verbatim
example : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k := by
  finsum_bound

-- inv with shifted denominator

-- @@ L72-75 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / (↑(k + 1) : ℝ) ≤ 3 := by
  finsum_bound

-- log: ∑ log(k) for k ≥ 1 (positive domain)

-- @@ L76-79 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.log ↑k ≤ 16 := by
  finsum_bound

-- Combined: exp(1/k) with inv inside exp

-- @@ L80-83 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp ((1 : ℝ) / ↑k) ≤ 20 := by
  finsum_bound

-- Larger N with inv (stress test O(1) proof size)

-- @@ L84-85 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 500, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound


-- @@ L87-89 verbatim
/-! ### Nested evaluations -/

-- Nested exp: exp(exp(1/k))

-- @@ L90-93 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 35 := by
  finsum_bound

-- Nested inv: 1/(1 + 1/k) = k/(k+1)

-- @@ L94-97 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ((1 : ℝ) + (1 : ℝ) / ↑k) ≤ 9 := by
  finsum_bound

-- Log with inv: log(k)/k

-- @@ L98-101 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.log ↑k / ↑k ≤ 6 := by
  finsum_bound

-- exp of log: exp(log(k)) = k for k ≥ 1

-- @@ L102-105 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp (Real.log ↑k) ≤ 56 := by
  finsum_bound

-- Triple nesting: exp(1/(1 + exp(-k)))

-- @@ L106-109 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp ((1 : ℝ) / ((1 : ℝ) + Real.exp (-(↑k : ℝ)))) ≤ 14 := by
  finsum_bound

-- Absolute value: |sin(k)| ≤ 1 per term, so ∑ |sin(k)| ≤ 10

-- @@ L110-111 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, |Real.sin ↑k| ≤ 10 := by
  finsum_bound


-- @@ L113-115 verbatim
/-! ### Rational and integer casts -/

-- Rat.cast: body contains ↑(q : ℚ) cast to ℝ

-- @@ L116-119 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 5, ((1/3 : ℚ) : ℝ) ≤ 2 := by
  finsum_bound

-- Rat.cast in arithmetic: ↑(q : ℚ) * sin(k)

-- @@ L120-123 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, ((1/2 : ℚ) : ℝ) * Real.sin ↑k ≤ 3 := by
  finsum_bound

-- Rat.cast in target: centralized extraction handles coerced rational bounds.

-- @@ L124-127 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 3, (1 : ℝ) / 1000 ≤ ↑(9/500 : ℚ) := by
  finsum_bound

-- Int.cast: body contains ↑(z : ℤ) multiplied with k

-- @@ L128-131 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 3, ((-1 : ℤ) : ℝ) * Real.sin ↑k ≤ 1 := by
  finsum_bound

-- Int.cast + constant: ↑(-2 : ℤ) + 3 reified structurally (not constant-folded)

-- @@ L132-133 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 3, (((-2 : ℤ) : ℝ) + 3) ≤ 4 := by
  finsum_bound


-- @@ L135-140 verbatim
/-! ### Witness mode (`finsum_bound using`)

Unlike the automatic mode, witness mode lets the user supply
a custom per-term interval evaluator.  The evaluators below use the
engine's `evalSumTermDyadic` which calls `LeanCert.Internal.Dyadic.evalUnchecked`—producing
*real* intervals with dyadic rounding error, not point singletons. -/


-- @@ L142-142 verbatim
open LeanCert.Core

-- @@ L143-143 verbatim
open LeanCert.Engine


-- @@ L145-147 verbatim
/-- Interval evaluator for exp(k) via Taylor series + dyadic rounding. -/
def expEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.exp (.var 0)) k cfg


-- @@ L149-152 verbatim
theorem expEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    Real.exp (↑k : ℝ) ∈ expEval k cfg :=
  mem_evalSumTermDyadic (.exp (.var 0)) (.exp (.var 0)) k cfg hprec trivial


-- @@ L154-156 verbatim
/-- Interval evaluator for 1/k via dyadic interval arithmetic. -/
def invEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.inv (.var 0)) k cfg


-- @@ L158-163 verbatim
theorem invEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.inv (.var 0)) (sumBodyEnvSimple k cfg.precision) cfg) :
    (1 : ℝ) / ↑k ∈ invEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_checked (.inv (.var 0)) k cfg hprec hdom


-- @@ L165-167 verbatim
/-- Interval evaluator for exp(1/k): nested inv inside exp. -/
def expInvEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.exp (.inv (.var 0))) k cfg


-- @@ L169-174 verbatim
theorem expInvEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.exp (.inv (.var 0))) (sumBodyEnvSimple k cfg.precision) cfg) :
    Real.exp ((1 : ℝ) / ↑k) ∈ expInvEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_checked (.exp (.inv (.var 0))) k cfg hprec hdom


-- @@ L176-178 verbatim
/-- Interval evaluator for 1/(k*k). -/
def invSqEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.inv (.mul (.var 0) (.var 0))) k cfg


-- @@ L180-189 verbatim
theorem invSqEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.inv (.mul (.var 0) (.var 0)))
        (sumBodyEnvSimple k cfg.precision) cfg) :
    (1 : ℝ) / (↑k * ↑k) ∈ invSqEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_checked (.inv (.mul (.var 0) (.var 0)))
    k cfg hprec hdom

-- exp(k) upper bound (trivial domain, no inv/log)

-- @@ L190-193 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (↑k : ℝ) ≤ 234 := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)

-- exp(k) lower bound

-- @@ L194-197 verbatim
example : (233 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (↑k : ℝ) := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)

-- 1/k upper bound (domain check via native_decide)

-- @@ L198-202 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k ≤ 4 := by
  finsum_bound using invEval (fun k ha hb => invEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.var 0)) 1 10 {} (by native_decide) k ha hb))

-- 1/k lower bound

-- @@ L203-207 verbatim
example : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k := by
  finsum_bound using invEval (fun k ha hb => invEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.var 0)) 1 10 {} (by native_decide) k ha hb))

-- exp(1/k) upper bound (nested inv inside exp, domain check)

-- @@ L208-212 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp ((1 : ℝ) / ↑k) ≤ 20 := by
  finsum_bound using expInvEval (fun k ha hb => expInvEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.exp (.inv (.var 0))) 1 10 {} (by native_decide) k ha hb))

-- 1/(k*k) on 100 terms (stress test)

-- @@ L213-217 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound using invSqEval (fun k ha hb => invSqEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.mul (.var 0) (.var 0))) 1 100 {} (by native_decide) k ha hb))

-- Empty range

-- @@ L218-219 verbatim
example : ∑ k ∈ Finset.Icc (5 : ℕ) 3, Real.exp (↑k : ℝ) ≤ 1 := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)


-- @@ L221-223 verbatim
/-! ### Arbitrary finite sets (list path) -/

-- Finset.range

-- @@ L224-226 verbatim
example : ∑ _k ∈ Finset.range 10, (1 : ℝ) ≤ 11 := by finsum_bound

-- Finset.Ico

-- @@ L227-229 verbatim
example : ∑ k ∈ Finset.Ico (1 : ℕ) 11, (1 : ℝ) / ↑k ≤ 4 := by finsum_bound

-- Finset.Ioc

-- @@ L230-232 verbatim
example : ∑ k ∈ Finset.Ioc (0 : ℕ) 5, (↑k : ℝ) ≤ 16 := by finsum_bound

-- Finset.Ioo

-- @@ L233-235 verbatim
example : ∑ k ∈ Finset.Ioo (0 : ℕ) 5, (↑k : ℝ) ≤ 11 := by finsum_bound

-- Explicit finset

-- @@ L236-238 verbatim
example : ∑ k ∈ ({1, 3, 5, 7} : Finset ℕ), (↑k : ℝ) ≤ 17 := by finsum_bound

-- Explicit finset duplicate semantics: Finset removes duplicates.

-- @@ L239-242 verbatim
example : ∑ _k ∈ ({1, 1, 2} : Finset ℕ), ((1 : ℚ) : ℝ) ≤ 2 := by
  finsum_bound

-- Duplicate semantics for lower bounds with negative terms.

-- @@ L243-246 verbatim
example : (-20 : ℝ) ≤ ∑ _k ∈ ({1, 1, 2} : Finset ℕ), ((-10 : ℚ) : ℝ) := by
  finsum_bound

-- Explicit finset order stability / non-Icc path.

-- @@ L247-250 verbatim
example : ∑ _k ∈ ({3, 1, 2} : Finset ℕ), ((1 : ℚ) : ℝ) ≤ 3 := by
  finsum_bound

-- Explicit finset with inv

-- @@ L251-253 verbatim
example : ∑ k ∈ ({1, 2, 4, 8} : Finset ℕ), (1 : ℝ) / ↑k ≤ 2 := by finsum_bound

-- Lower bound with Finset.range

-- @@ L254-256 verbatim
example : (10 : ℝ) ≤ ∑ k ∈ Finset.range 6, (↑k : ℝ) := by finsum_bound

-- Sparse set with exp

-- @@ L257-259 verbatim
example : ∑ k ∈ ({1, 10, 100} : Finset ℕ), Real.exp (-(↑k : ℝ)) ≤ 1 := by finsum_bound

-- Deep nesting on explicit finset: 1/(k * log(k))

-- @@ L260-262 verbatim
example : ∑ k ∈ ({2, 3, 5, 7} : Finset ℕ), (1 : ℝ) / (↑k * Real.log ↑k) ≤ 2 := by finsum_bound

-- Nested exp on explicit finset: exp(exp(1/k))

-- @@ L263-263 verbatim
example : ∑ k ∈ ({1, 2, 3} : Finset ℕ), Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 26 := by finsum_bound


-- @@ L265-273 verbatim
/-! ### Fin n sums (auto-rewrite via `tryRewriteFinSum`)

`finsum_bound` detects `∑ i : Fin n, f i` goals, extracts the body lambda,
replaces `Fin.val i` with a fresh ℕ variable to build `g : ℕ → β`, and
rewrites via `Fin.sum_univ_eq_sum_range g`. This handles arbitrary bodies
(not just simple `↑i`), unlike `simp only [Fin.sum_univ_eq_sum_range]` which
requires first-order matching. -/

-- Simple coercion body

-- @@ L274-276 verbatim
example : ∑ i : Fin 10, (↑i : ℝ) ≤ 46 := by finsum_bound

-- Lower bound

-- @@ L277-279 verbatim
example : (44 : ℝ) ≤ ∑ i : Fin 10, (↑i : ℝ) := by finsum_bound

-- Transcendental body (exp ↑i — needs meta-level Fin.val extraction)

-- @@ L280-282 verbatim
example : ∑ i : Fin 5, Real.exp (↑i : ℝ) ≤ 234 := by finsum_bound

-- Witness mode (Fin → range rewrite, then list path)

-- @@ L283-284 verbatim
example : ∑ i : Fin 5, Real.exp (↑i : ℝ) ≤ 234 := by
  finsum_bound using expEval (fun k _ => expEval_correct k _)


-- @@ L286-291 verbatim
/-! ### Auto-hmem witness mode (`finsum_bound auto`)

The `auto` keyword provides a witness evaluator without a manual hmem proof.
The tactic auto-proves `f k ∈ evalTerm k cfg` via `simp [mem_def] + push_cast + norm_num`.
This works when the evaluator returns singletons where membership reduces to
`d.toRat ≤ x ∧ x ≤ d.toRat` with `x = ↑(d.toRat)`. -/


-- @@ L293-295 verbatim
/-- Singleton evaluator: returns the exact value 1 for every k. -/
def constOneEval (_k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton ⟨1, 0⟩


-- @@ L297-300 verbatim
/-- Deliberately excludes the constant body value, so auto-membership reaches
the typed verifier and receives a conclusive rejection. -/
def rejectingOneEval (_k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton ⟨0, 0⟩


-- @@ L302-307 verbatim
/-- Deliberately noncomputable evaluator used to exercise membership
verification infrastructure failure rather than ordinary synthesis failure. -/
noncomputable def unavailableOneEval (_k : Nat) (_cfg : DyadicConfig) :
    IntervalDyadic :=
  Classical.choice (show Nonempty IntervalDyadic from
    ⟨IntervalDyadic.singleton ⟨1, 0⟩⟩)


-- @@ L309-320 verbatim
elab "expect_auto_membership_rejected" : tactic => do
  let original ← getMainGoal
  let originalType ← original.getType
  match ← finSumWitnessAutoCoreTyped (← `(term| rejectingOneEval)) (-53) with
  | .error (.rejected _ _) =>
      let restored ← getMainGoal
      unless restored == original && (← isDefEq (← restored.getType) originalType) do
        throwError "auto-membership rejection did not restore the original goal"
  | .error failure =>
      throwError "auto-membership rejection was misclassified: {repr failure}"
  | .ok _ =>
      throwError "invalid auto-membership certificate was accepted"


-- @@ L322-330 verbatim
elab "expect_auto_membership_verification_failure" : tactic => do
  match ← finSumWitnessAutoCoreTyped (← `(term| unavailableOneEval)) (-53) with
  | .error (.verificationFailure _) => pure ()
  | .error failure =>
      throwError "auto-membership infrastructure failure was misclassified: {repr failure}"
  | .ok _ =>
      throwError "noncomputable auto-membership certificate unexpectedly succeeded"

-- Constant body, singleton evaluator

-- @@ L331-332 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 5, (1 : ℝ) ≤ 6 := by
  finsum_bound auto constOneEval


-- @@ L334-336 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 5, (1 : ℝ) ≤ 6 := by
  expect_auto_membership_rejected
  finsum_bound auto constOneEval


-- @@ L338-340 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 5, (1 : ℝ) ≤ 6 := by
  expect_auto_membership_verification_failure
  finsum_bound auto constOneEval


-- @@ L342-344 verbatim
/-! ### Rational bound targets (`extractRatFromReal` with `toRat?` fallback) -/

-- ↑(q : ℚ) as bound target (was failing before toRat? fix)

-- @@ L345-348 verbatim
example : ∑ _k ∈ Finset.Icc (1 : ℕ) 3, (1 : ℝ) / 1000 ≤ ↑(9/500 : ℚ) := by
  finsum_bound

-- ↑(q : ℚ) in body (already worked via Rat.cast pattern in toRat?)

-- @@ L349-350 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, ↑(9/500 : ℚ) * Real.sin (↑k : ℝ) ≤ 1 := by
  finsum_bound


-- @@ L352-352 verbatim
end LeanCert.Test.FinSumBound
