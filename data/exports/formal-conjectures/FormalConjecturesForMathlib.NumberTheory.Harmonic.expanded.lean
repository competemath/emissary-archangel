/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module


public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-41 verbatim
/-!
# Block harmonic sums

Mathlib's `harmonic n` is the initial harmonic sum `∑_{1 ≤ k ≤ n} 1 / k`. Several problems
instead need the *block* sum `∑_{n ≤ k ≤ m} 1 / k`, which is what `harmonicBlock` gives.
Like `harmonic` it is valued in `ℚ`; cast at the use site when a real value is wanted.

## Main definitions

* `harmonicBlock`: the block harmonic sum `∑_{n ≤ k ≤ m} 1 / k`.

## Main results

* `harmonicBlock_eq_zero_of_lt`: the block sum is empty when `m < n`.
* `harmonicBlock_one`: `harmonicBlock 1 n` is Mathlib's `harmonic n`.
-/


-- @@ L43-45 verbatim
/-- The block harmonic sum $\sum_{n\leq k\leq m}\frac{1}{k}$.
For `n = 1` this is Mathlib's `harmonic`, see `harmonicBlock_one`. -/
def harmonicBlock (n m : ℕ) : ℚ := ∑ k ∈ Finset.Icc n m, (k : ℚ)⁻¹


-- @@ L47-47 verbatim
variable (n m : ℕ)


-- @@ L49-51 verbatim
theorem harmonicBlock_eq_sum_one_div :
    harmonicBlock n m = ∑ k ∈ Finset.Icc n m, 1 / (k : ℚ) := by
  simp [harmonicBlock, one_div]


-- @@ L53-55 verbatim
@[simp]
theorem harmonicBlock_eq_zero_of_lt (h : m < n) : harmonicBlock n m = 0 := by
  simp [harmonicBlock, Finset.Icc_eq_empty_of_lt h]


-- @@ L57-59 verbatim
theorem harmonicBlock_succ_top (h : n ≤ m + 1) :
    harmonicBlock n (m + 1) = harmonicBlock n m + ((m : ℚ) + 1)⁻¹ := by
  simp [harmonicBlock, Finset.sum_Icc_succ_top h]


-- @@ L61-65 verbatim
/-- The block sum starting at `1` is Mathlib's harmonic number. -/
theorem harmonicBlock_one (n : ℕ) : harmonicBlock 1 n = harmonic n := by
  induction n with
  | zero => simp [harmonicBlock]
  | succ n ih => rw [harmonicBlock_succ_top _ _ (by omega), ih, harmonic_succ]; push_cast; ring
