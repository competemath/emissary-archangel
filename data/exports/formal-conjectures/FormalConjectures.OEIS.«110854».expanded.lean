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


-- @@ L19-27 verbatim
/-!
# Conjectures associated with A110854

$a(n) = \mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$,
where $\mathrm{prime}(k)$ is the $k$-th prime number.

*References:*
- [A110854](https://oeis.org/A110854)
-/


-- @@ L29-29 verbatim
namespace OeisA110854


-- @@ L31-31 verbatim
open Nat


-- @@ L33-40 verbatim
/--
The primary defining sequence `a`.
$a(n)$ is $\mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let p (k : ℕ) : ℤ := (Nat.nth Nat.Prime (k - 1)).cast
  if n = 0 then 0
  else p (2 * n + 2) - p (2 * n + 1) - p (2 * n) + p (2 * n - 1)


-- @@ L42-45 verbatim
@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1


-- @@ L47-50 verbatim
@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1


-- @@ L52-55 verbatim
@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1


-- @@ L57-60 verbatim
@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1


-- @@ L62-65 verbatim
@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1


-- @@ L67-70 verbatim
/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl


-- @@ L72-75 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  norm_num


-- @@ L77-82 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  rw [nth_prime_five, Nat.nth_prime_four_eq_eleven, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_two_eq_five]
  norm_num


-- @@ L84-88 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  rw [nth_prime_seven, nth_prime_six, nth_prime_five, Nat.nth_prime_four_eq_eleven]
  norm_num


-- @@ L90-94 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  dsimp [a]
  rw [nth_prime_nine, nth_prime_eight, nth_prime_seven, nth_prime_six]
  norm_num


-- @@ L96-105 verbatim
/--
Do the absolute values cover A004275?
A004275 is $1$ together with the nonnegative even numbers.
The conjecture asks whether every member of A004275 occurs as $|a(n)|$ for some
term of the sequence.
-/
@[category research open, AMS 11]
theorem conjecture :
  ∀ d : ℕ, (d = 1 ∨ Even d) → ∃ n > 0, d = (a n).natAbs := by
  sorry


-- @@ L107-107 verbatim
end OeisA110854
