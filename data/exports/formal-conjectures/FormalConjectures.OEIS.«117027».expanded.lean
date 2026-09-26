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

import FormalConjecturesUtil


-- @@ L19-26 verbatim
/-!
# Determinants of 2 X 2 matrices of non-overlapping blocks of 4 consecutive primes

$a(n) = p_{4n-3}p_{4n} - p_{4n-2}p_{4n-1}$ where $p_k$ is the k-th prime number (1-indexed).

*References:*
- [A117027](https://oeis.org/A117027)
-/


-- @@ L28-28 verbatim
namespace OeisA117027


-- @@ L30-30 verbatim
open Nat Int Filter


-- @@ L32-45 verbatim
/-- a n is the determinant of a 2x2 matrix of non-overlapping blocks of 4 consecutive primes. -/
noncomputable def a (n : ℕ) : ℤ :=
  if 0 < n then
    let k := 4 * n
    let pPrime (i : ℕ) : ℤ := (Nat.nth Nat.Prime i : ℤ)

    let p₁ := pPrime (k - 4) -- p_{4n-4} in 0-indexed Mathlib
    let p₂ := pPrime (k - 1) -- p_{4n-1} in 0-indexed Mathlib
    let p₃ := pPrime (k - 3) -- p_{4n-3} in 0-indexed Mathlib
    let p₄ := pPrime (k - 2) -- p_{4n-2} in 0-indexed Mathlib

    p₁ * p₂ - p₃ * p₄
  else
    0


-- @@ L47-50 verbatim
@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1


-- @@ L52-55 verbatim
@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1


-- @@ L57-60 verbatim
@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1


-- @@ L62-65 verbatim
@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1


-- @@ L67-70 verbatim
@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1


-- @@ L72-75 verbatim
@[category API, AMS 11]
lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : (31).Prime := by decide
  exact Nat.nth_count h1


-- @@ L77-80 verbatim
@[category API, AMS 11]
lemma nth_prime_eleven : Nat.nth Nat.Prime 11 = 37 := by
  have h1 : (37).Prime := by decide
  exact Nat.nth_count h1


-- @@ L82-84 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl


-- @@ L86-91 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = -1 := by
  dsimp [a]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven]
  norm_num


-- @@ L93-97 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = -12 := by
  dsimp [a]
  rw [Nat.nth_prime_four_eq_eleven, nth_prime_seven, nth_prime_five, nth_prime_six]
  norm_num


-- @@ L99-103 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = -48 := by
  dsimp [a]
  rw [nth_prime_eight, nth_prime_eleven, nth_prime_nine, nth_prime_ten]
  norm_num


-- @@ L105-107 verbatim
/-- The count of positive terms among $a(1)$, ..., $a(N)$. -/
noncomputable def positiveCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => 0 < a (n + 1))


-- @@ L109-111 verbatim
/-- The count of negative terms among $a(1)$, ..., $a(N)$. -/
noncomputable def negativeCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => a (n + 1) < 0)


-- @@ L113-118 verbatim
/-- The sequence of ratios $P(N)/Neg(N)$ as a sequence of real numbers. -/
noncomputable def ratioSeq (N : ℕ) : ℝ :=
  if negativeCount N = 0 then
    0
  else
    (positiveCount N : ℝ) / (negativeCount N : ℝ)


-- @@ L120-129 verbatim
/--
This suggests the ratio is approaching a limit close to 0.87.

Formalized as: The sequence of ratios $P(N)/Neg(N)$ converges to a limit L,
and L is in the interval (0.8, 0.9).
-/
@[category research open, AMS 11]
theorem conjecture :
  ∃ L : ℝ, Tendsto ratioSeq atTop (nhds L) ∧ 0.8 < L ∧ L < 0.9 :=
by sorry


-- @@ L131-131 verbatim
end OeisA117027
