/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumBound


-- @@ L8-15 verbatim
/-!
# Tests for the Witness Sum API

Verifies:
- `finsum_witness` tactic (standalone)
- `finsum_bound using` (integrated witness mode)
- Bridge theorems (`verify_witness_sum_upper`/`lower`)
-/


-- @@ L17-17 verbatim
namespace LeanCert.Test.WitnessSum


-- @@ L19-19 verbatim
open LeanCert.Core

-- @@ L20-20 verbatim
open LeanCert.Engine


-- @@ L22-22 verbatim
/-! ## Witness evaluators for testing -/


-- @@ L24-26 verbatim
/-- Constant evaluator: always returns [1, 1]. -/
def constEval (_k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt 1)


-- @@ L28-34 verbatim
/-- Correctness: `(1 : ℝ) ∈ constEval k cfg`. -/
theorem constEval_correct (k : Nat) (cfg : DyadicConfig) :
    (1 : ℝ) ∈ constEval k cfg := by
  show (1 : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt 1)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 1)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h


-- @@ L36-38 verbatim
/-- Identity evaluator: returns [k, k] for each k. -/
def identityEval (k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)


-- @@ L40-46 verbatim
/-- Correctness: `(↑k : ℝ) ∈ identityEval k cfg`. -/
theorem identityEval_correct (k : Nat) (cfg : DyadicConfig) :
    (↑k : ℝ) ∈ identityEval k cfg := by
  show (↑k : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt ↑k)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h


-- @@ L48-48 verbatim
/-! ## Cached witness evaluator tests -/


-- @@ L50-51 verbatim
def constCache (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt 1)


-- @@ L53-55 verbatim
def cachedConstEval (cache : IntervalDyadic) (_k : Nat) (_cfg : DyadicConfig) :
    IntervalDyadic :=
  cache


-- @@ L57-59 verbatim
theorem cachedConstEval_correct (k : Nat) (cfg : DyadicConfig) :
    (1 : ℝ) ∈ cachedConstEval (constCache cfg) k cfg := by
  exact constEval_correct k cfg


-- @@ L61-64 verbatim
example :
    checkWitnessSumUpperBoundCached constCache cachedConstEval 1 10 11
      { precision := -53, taylorDepth := 10 } = true := by
  native_decide


-- @@ L66-70 verbatim
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 :=
  verify_witness_sum_upper_cached (fun _ => 1) constCache cachedConstEval 1 10 11
    { precision := -53, taylorDepth := 10 }
    (fun k _ _ => cachedConstEval_correct k _)
    (by native_decide)


-- @@ L72-74 verbatim
/-! ## Tests via `finsum_witness` tactic (standalone) -/

-- Basic: ∑ 1 ≤ 11 via constant witness

-- @@ L75-78 verbatim
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Lower bound: 1 ≤ ∑ 1 via constant witness

-- @@ L79-82 verbatim
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Empty sum: ∑ over Icc 5 3 (empty range)

-- @@ L83-86 verbatim
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Larger sum: 100 terms via constant witness

-- @@ L87-90 verbatim
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Identity: ∑ k for k ∈ Icc 1 10 ≤ 56 (actual = 55)

-- @@ L91-94 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_witness identityEval using (fun k _ _ => identityEval_correct k _)

-- Identity lower bound: 50 ≤ ∑ k for k ∈ Icc 1 10

-- @@ L95-96 verbatim
example : (50 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) := by
  finsum_witness identityEval using (fun k _ _ => identityEval_correct k _)


-- @@ L98-100 verbatim
/-! ## Tests via `finsum_bound using` (integrated witness mode) -/

-- finsum_bound using: constant witness upper bound

-- @@ L101-104 verbatim
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: constant witness lower bound

-- @@ L105-108 verbatim
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: identity witness upper bound

-- @@ L109-112 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- finsum_bound using: identity witness lower bound

-- @@ L113-116 verbatim
example : (50 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- finsum_bound using: empty range

-- @@ L117-120 verbatim
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: larger sum

-- @@ L121-124 verbatim
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: identity witness, larger range

-- @@ L125-126 verbatim
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (↑k : ℝ) ≤ 5051 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)


-- @@ L128-130 verbatim
/-! ## Tests via direct bridge theorem application -/

-- Direct use of verify_witness_sum_upper (no tactic)

-- @@ L131-137 verbatim
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 :=
  verify_witness_sum_upper (fun _ => 1) constEval 1 10 11
    { precision := -53, taylorDepth := 10 }
    (fun _ _ _ => constEval_correct _ _)
    (by native_decide)

-- Direct use of verify_witness_sum_lower (no tactic)

-- @@ L138-143 verbatim
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  have h := verify_witness_sum_lower (fun _ => (1 : ℝ)) constEval 1 10 1
    { precision := -53, taylorDepth := 10 }
    (fun _ _ _ => constEval_correct _ _)
    (by native_decide)
  exact_mod_cast h


-- @@ L145-145 verbatim
end LeanCert.Test.WitnessSum
