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
# Difference of digit sums in base 3 and base 2

Difference of sums of digits of $n$ in ternary and in binary:
$$a(n) = \sum \mathrm{digits}_3(n) - \sum \mathrm{digits}_2(n).$$

*References:*
- [A180017](https://oeis.org/A180017)-/


-- @@ L28-28 verbatim
namespace OeisA180017


-- @@ L30-32 verbatim
/-- Difference of sums of digits of $n$ in ternary and in binary. -/
def a (n : ℕ) : ℤ :=
  (Nat.digits 3 n).sum - (Nat.digits 2 n).sum


-- @@ L34-35 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by norm_num [a]


-- @@ L37-38 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by norm_num [a]


-- @@ L40-41 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by norm_num [a]


-- @@ L43-44 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by norm_num [a]


-- @@ L46-47 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by norm_num [a]


-- @@ L49-54 verbatim
/--
"This sequence is positive on average, since 1/log(3) > 1/log(4). Do all integers appear
infinitely often?" - Charles R Greathouse IV, Feb 07 2013-/
@[category research open, AMS 11]
theorem conjecture (z : ℤ) : Set.Infinite {n : ℕ | a n = z} := by
  sorry


-- @@ L56-56 verbatim
end OeisA180017
