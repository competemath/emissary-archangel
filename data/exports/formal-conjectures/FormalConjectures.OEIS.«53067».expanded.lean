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
# Concatenation of the next $n$ numbers

$a(n)$ is the concatenation of the next $n$ numbers: the integers from
$\frac{(n-1)n}{2} + 1$ up to $\frac{n(n+1)}{2}$.

*References:*
- [A053067](https://oeis.org/A053067)-/


-- @@ L28-28 verbatim
namespace OeisA53067


-- @@ L30-31 verbatim
/-- The $n$-th triangular number, $T_n = \frac{n(n+1)}{2}$. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2


-- @@ L33-35 verbatim
/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenateNats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b


-- @@ L37-44 verbatim
/-- $a(n)$ is the concatenation of the next $n$ numbers. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let start_num : ℕ := triangular (n - 1) + 1
    let end_num : ℕ := triangular n
    let numbers_to_concat : List ℕ := List.Ico start_num (end_num + 1)
    numbers_to_concat.foldl concatenateNats 0


-- @@ L46-48 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide +native


-- @@ L50-52 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 23 := by
  decide +native


-- @@ L54-56 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 456 := by
  decide +native


-- @@ L58-60 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 78910 := by
  decide +native


-- @@ L62-64 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 1112131415 := by
  decide +native


-- @@ L66-78 verbatim
open scoped Classical in
/--
"The second term is a prime. When is the next prime, if there is another?
- _N. J. A. Sloane_, Dec 16 2016"
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) =
      if h : ∃ n, 2 < n ∧ (a n).Prime then
        some (sInf {n | 2 < n ∧ (a n).Prime})
      else
        none := by
  sorry



-- @@ L81-81 verbatim
end OeisA53067
