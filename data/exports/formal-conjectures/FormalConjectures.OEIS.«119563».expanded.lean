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
# Sum of Fermat number and Mersenne number minus 1: $2^{2^n} + 2^n - 1$

Define $F(n) = 2^{2^n} + 1$ (the $n$-th Fermat number) and $M(n) = 2^n - 1$ (the $n$-th Mersenne
number). Then $a(n) = F(n) + M(n) - 1 = 2^{2^n} + 2^n - 1$.

*References:*
- [A119563](https://oeis.org/A119563)-/


-- @@ L28-28 verbatim
namespace OeisA119563


-- @@ L30-31 verbatim
/-- $a(n) = 2^{2^n} + 2^n - 1$. -/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 2 ^ n - 1


-- @@ L33-35 verbatim
/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by rfl


-- @@ L37-39 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by rfl


-- @@ L41-43 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 19 := by rfl


-- @@ L45-47 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 263 := by rfl


-- @@ L49-51 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 65551 := by rfl


-- @@ L53-57 verbatim
/--
The first 5 entries are primes. Are there infinitely many primes in this sequence?-/
@[category research open, AMS 11]
theorem conjecture : Set.Infinite {n : ℕ | (a n).Prime} := by
  sorry


-- @@ L59-59 verbatim
end OeisA119563
