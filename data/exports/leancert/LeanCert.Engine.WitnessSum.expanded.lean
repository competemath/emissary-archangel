/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.FinSumDyadic


-- @@ L8-34 verbatim
/-!
# Witness-Based Finite Sum Evaluator

Generic accumulator loop for finite sums parameterized by a user-provided
per-term evaluator. Unlike `FinSumDyadic` (which uses `Core.Expr` + `LeanCert.Internal.Dyadic.evalUnchecked`),
this module accepts any computable evaluator `Nat → DyadicConfig → IntervalDyadic`
paired with a correctness proof.

## Motivation

`finsum_bound` auto-reifies to `Core.Expr`, which covers +, *, inv, exp, sin, log, etc.
Functions outside `Core.Expr` (like `rpow` in BKLNW's `x^(1/k - 1/3)`) need a custom
evaluator. The witness API provides the accumulator + bridge theorems; the user provides
the per-term evaluator + its correctness proof.

## Usage

```lean
-- User defines:
def myEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic := ...
theorem myEval_correct (k : Nat) ... : myF k ∈ myEval k cfg := ...

-- Prove bound:
example : ∑ k ∈ Finset.Icc 1 100, myF k ≤ target :=
  verify_witness_sum_upper myF myEval 1 100 target cfg myEval_correct (by native_decide)
```
-/


-- @@ L36-36 verbatim
namespace LeanCert.Engine


-- @@ L38-38 verbatim
open LeanCert.Core


-- @@ L40-40 verbatim
/-! ### Accumulator Loop -/


-- @@ L42-52 verbatim
/-- Accumulator loop parameterized by a user-provided evaluator.
    Computes an interval containing `∑ k ∈ Icc current limit, f k`. -/
def witnessSumAux (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (current limit : Nat) (acc : IntervalDyadic)
    (cfg : DyadicConfig) : IntervalDyadic :=
  if current > limit then acc
  else
    let term := evalTerm current cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    witnessSumAux evalTerm (current + 1) limit newAcc cfg
  termination_by limit + 1 - current


-- @@ L54-57 verbatim
/-- Main entry point: interval for `∑ k ∈ Icc a b, f k` using a witness evaluator. -/
def witnessSumDyadic (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  witnessSumAux evalTerm a b finSumZero cfg


-- @@ L59-59 verbatim
/-! ### Cached Evaluators -/


-- @@ L61-69 verbatim
/-- Main entry point for witness sums whose term evaluator uses data cached once
    per configuration.  This is computationally equivalent to closing over the
    cache manually, but gives table/generator code a stable reusable API. -/
def witnessSumDyadicCached {Cache : Type}
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  let cache := init cfg
  witnessSumDyadic (fun k cfg => evalTerm cache k cfg) a b cfg


-- @@ L71-71 verbatim
/-! ### Certificate Checkers -/


-- @@ L73-76 verbatim
/-- Check if `∑ k ∈ Icc a b, f k ≤ target` using the witness evaluator. -/
def checkWitnessSumUpperBound (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadic evalTerm a b cfg).upperBoundedBy target


-- @@ L78-81 verbatim
/-- Check if `target ≤ ∑ k ∈ Icc a b, f k` using the witness evaluator. -/
def checkWitnessSumLowerBound (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadic evalTerm a b cfg).lowerBoundedBy target


-- @@ L83-88 verbatim
/-- Check an upper bound for a cached witness sum. -/
def checkWitnessSumUpperBoundCached {Cache : Type}
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadicCached init evalTerm a b cfg).upperBoundedBy target


-- @@ L90-95 verbatim
/-- Check a lower bound for a cached witness sum. -/
def checkWitnessSumLowerBoundCached {Cache : Type}
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadicCached init evalTerm a b cfg).lowerBoundedBy target


-- @@ L97-97 verbatim
/-! ### Correctness Theorems -/


-- @@ L99-126 verbatim
/-- Accumulator correctness: if the evaluator is sound for each term,
    the accumulator produces a sound interval for the partial sum. -/
theorem mem_witnessSumAux (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc) (cfg : DyadicConfig)
    (hmem : ∀ k, current ≤ k → k ≤ limit → f k ∈ evalTerm k cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, f k)
      ∈ witnessSumAux evalTerm current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold witnessSumAux
    split_ifs with h
    · simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      rw [← add_assoc]
      have hterm := hmem current (Nat.le_refl current) hcur_le
      have hnewAcc : partialSum + f current ∈
          (IntervalDyadic.add acc (evalTerm current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hmem' : ∀ k, current + 1 ≤ k → k ≤ limit → f k ∈ evalTerm k cfg :=
        fun k hk1 hk2 => hmem k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hmem' rfl


-- @@ L128-136 verbatim
/-- Golden theorem: the computed interval contains the true sum. -/
theorem mem_witnessSumDyadic (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg) :
    (∑ k ∈ Finset.Icc a b, f k) ∈ witnessSumDyadic evalTerm a b cfg := by
  unfold witnessSumDyadic
  have h := mem_witnessSumAux f evalTerm a b finSumZero 0 mem_finSumZero cfg hmem
  simp only [zero_add] at h
  exact h


-- @@ L138-147 verbatim
/-- Golden theorem for cached witness sums. -/
theorem mem_witnessSumDyadicCached {Cache : Type} (f : Nat → ℝ)
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm (init cfg) k cfg) :
    (∑ k ∈ Finset.Icc a b, f k) ∈
      witnessSumDyadicCached init evalTerm a b cfg := by
  unfold witnessSumDyadicCached
  exact mem_witnessSumDyadic f (fun k cfg' => evalTerm (init cfg) k cfg') a b cfg hmem


-- @@ L149-149 verbatim
/-! ### Bridge Theorems -/


-- @@ L151-163 verbatim
/-- If checkWitnessSumUpperBound returns true, the sum is bounded above. -/
theorem verify_witness_sum_upper (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumUpperBound evalTerm a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, f k ≤ target := by
  have hsum := mem_witnessSumDyadic f evalTerm a b cfg hmem
  have hhi : ∑ k ∈ Finset.Icc a b, f k ≤
      ((witnessSumDyadic evalTerm a b cfg).hi.toRat : ℝ) := hsum.2
  simp only [checkWitnessSumUpperBound, IntervalDyadic.upperBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)


-- @@ L165-177 verbatim
/-- If checkWitnessSumLowerBound returns true, the sum is bounded below. -/
theorem verify_witness_sum_lower (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumLowerBound evalTerm a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, f k := by
  have hsum := mem_witnessSumDyadic f evalTerm a b cfg hmem
  have hlo : ((witnessSumDyadic evalTerm a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, f k := hsum.1
  simp only [checkWitnessSumLowerBound, IntervalDyadic.lowerBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo


-- @@ L179-192 verbatim
/-- If `checkWitnessSumUpperBoundCached` returns true, the cached sum is bounded above. -/
theorem verify_witness_sum_upper_cached {Cache : Type} (f : Nat → ℝ)
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm (init cfg) k cfg)
    (h_check : checkWitnessSumUpperBoundCached init evalTerm a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, f k ≤ target := by
  have hsum := mem_witnessSumDyadicCached f init evalTerm a b cfg hmem
  have hhi : ∑ k ∈ Finset.Icc a b, f k ≤
      ((witnessSumDyadicCached init evalTerm a b cfg).hi.toRat : ℝ) := hsum.2
  simp only [checkWitnessSumUpperBoundCached, IntervalDyadic.upperBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)


-- @@ L194-207 verbatim
/-- If `checkWitnessSumLowerBoundCached` returns true, the cached sum is bounded below. -/
theorem verify_witness_sum_lower_cached {Cache : Type} (f : Nat → ℝ)
    (init : DyadicConfig → Cache)
    (evalTerm : Cache → Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm (init cfg) k cfg)
    (h_check : checkWitnessSumLowerBoundCached init evalTerm a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, f k := by
  have hsum := mem_witnessSumDyadicCached f init evalTerm a b cfg hmem
  have hlo : ((witnessSumDyadicCached init evalTerm a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, f k := hsum.1
  simp only [checkWitnessSumLowerBoundCached, IntervalDyadic.lowerBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo


-- @@ L209-211 verbatim
/-! ## List-Based Witness Sum

Witness sum over an explicit `List Nat` of indices, enabling arbitrary Finsets. -/


-- @@ L213-213 verbatim
/-! ### List Accumulator -/


-- @@ L215-224 verbatim
/-- Accumulator loop over a list of indices. -/
def witnessSumAuxList (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (acc : IntervalDyadic)
    (cfg : DyadicConfig) : IntervalDyadic :=
  match indices with
  | [] => acc
  | k :: rest =>
    let term := evalTerm k cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    witnessSumAuxList evalTerm rest newAcc cfg


-- @@ L226-229 verbatim
/-- Interval for `∑ k ∈ indices.toFinset, f k` using a witness evaluator. -/
def witnessSumDyadicList (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  witnessSumAuxList evalTerm indices finSumZero cfg


-- @@ L231-231 verbatim
/-! ### List Certificate Checkers -/


-- @@ L233-235 verbatim
def checkWitnessSumUpperBoundList (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadicList evalTerm indices cfg).upperBoundedBy target


-- @@ L237-239 verbatim
def checkWitnessSumLowerBoundList (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadicList evalTerm indices cfg).lowerBoundedBy target


-- @@ L241-241 verbatim
/-! ### List Correctness Theorems -/


-- @@ L243-262 verbatim
/-- Accumulator correctness for list-based witness sum. -/
theorem mem_witnessSumAuxList (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg) :
    (partialSum + (indices.map f).sum)
      ∈ witnessSumAuxList evalTerm indices acc cfg := by
  induction indices generalizing acc partialSum with
  | nil =>
    simp only [List.map_nil, List.sum_nil, add_zero, witnessSumAuxList]
    exact hacc
  | cons k rest ih =>
    simp only [witnessSumAuxList, List.map_cons, List.sum_cons]
    rw [← add_assoc]
    have hterm := hmem k (.head rest)
    have hnewAcc : partialSum + f k ∈
        (IntervalDyadic.add acc (evalTerm k cfg)).roundOut cfg.precision := by
      apply IntervalDyadic.roundOut_contains
      exact IntervalDyadic.mem_add hacc hterm
    exact ih _ _ hnewAcc (fun j hj => hmem j (.tail k hj))


-- @@ L264-273 verbatim
/-- Golden theorem for list-based witness sum. -/
theorem mem_witnessSumDyadicList (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (hnodup : indices.Nodup) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg) :
    (∑ k ∈ indices.toFinset, f k) ∈ witnessSumDyadicList evalTerm indices cfg := by
  unfold witnessSumDyadicList
  rw [List.sum_toFinset _ hnodup]
  have h := mem_witnessSumAuxList f evalTerm indices finSumZero 0 mem_finSumZero cfg hmem
  simp only [zero_add] at h
  exact h


-- @@ L275-275 verbatim
/-! ### List Bridge Theorems -/


-- @@ L277-289 verbatim
/-- Upper bound for witness sum over a list. -/
theorem verify_witness_sum_upper_list (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (hnodup : indices.Nodup)
    (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumUpperBoundList evalTerm indices target cfg = true) :
    ∑ k ∈ indices.toFinset, f k ≤ target := by
  have hsum := mem_witnessSumDyadicList f evalTerm indices hnodup cfg hmem
  exact le_trans hsum.2 (by
    simp only [checkWitnessSumUpperBoundList, IntervalDyadic.upperBoundedBy,
      decide_eq_true_eq] at h_check
    exact_mod_cast h_check)


-- @@ L291-303 verbatim
/-- Lower bound for witness sum over a list. -/
theorem verify_witness_sum_lower_list (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (indices : List Nat) (hnodup : indices.Nodup)
    (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumLowerBoundList evalTerm indices target cfg = true) :
    target ≤ ∑ k ∈ indices.toFinset, f k := by
  have hsum := mem_witnessSumDyadicList f evalTerm indices hnodup cfg hmem
  exact le_trans (by
    simp only [checkWitnessSumLowerBoundList, IntervalDyadic.lowerBoundedBy,
      decide_eq_true_eq] at h_check
    exact_mod_cast h_check) hsum.1


-- @@ L305-305 verbatim
/-! ### List Combined Checkers -/


-- @@ L307-312 verbatim
/-- Combined check: S = indices.toFinset ∧ Nodup ∧ upper bound. -/
def checkWitnessSumUpperBoundListFull (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (S : Finset Nat) (indices : List Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  decide (S = indices.toFinset) &&
  indices.Nodup &&
  checkWitnessSumUpperBoundList evalTerm indices target cfg


-- @@ L314-319 verbatim
/-- Combined check: S = indices.toFinset ∧ Nodup ∧ lower bound. -/
def checkWitnessSumLowerBoundListFull (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (S : Finset Nat) (indices : List Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  decide (S = indices.toFinset) &&
  indices.Nodup &&
  checkWitnessSumLowerBoundList evalTerm indices target cfg


-- @@ L321-321 verbatim
/-! ### List Combined Bridge Theorems -/


-- @@ L323-335 verbatim
/-- If checkWitnessSumUpperBoundListFull returns true, the sum is bounded above. -/
theorem verify_witness_sum_upper_list_full (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (S : Finset Nat) (indices : List Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ S → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumUpperBoundListFull evalTerm S indices target cfg = true) :
    ∑ k ∈ S, f k ≤ target := by
  simp only [checkWitnessSumUpperBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨heq, hnodup⟩, hbound⟩ := h_check
  rw [heq]
  have hmem' : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg :=
    fun k hk => hmem k (heq ▸ List.mem_toFinset.mpr hk)
  exact verify_witness_sum_upper_list f evalTerm indices hnodup target cfg hmem' hbound


-- @@ L337-349 verbatim
/-- If checkWitnessSumLowerBoundListFull returns true, the sum is bounded below. -/
theorem verify_witness_sum_lower_list_full (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (S : Finset Nat) (indices : List Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, k ∈ S → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumLowerBoundListFull evalTerm S indices target cfg = true) :
    target ≤ ∑ k ∈ S, f k := by
  simp only [checkWitnessSumLowerBoundListFull, Bool.and_eq_true, decide_eq_true_eq] at h_check
  obtain ⟨⟨heq, hnodup⟩, hbound⟩ := h_check
  rw [heq]
  have hmem' : ∀ k, k ∈ indices → f k ∈ evalTerm k cfg :=
    fun k hk => hmem k (heq ▸ List.mem_toFinset.mpr hk)
  exact verify_witness_sum_lower_list f evalTerm indices hnodup target cfg hmem' hbound


-- @@ L351-351 verbatim
end LeanCert.Engine
