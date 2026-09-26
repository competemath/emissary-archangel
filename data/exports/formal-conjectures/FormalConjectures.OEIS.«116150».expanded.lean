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


-- @@ L19-24 verbatim
/-!
# $a(n) = \sum_{j=1}^{n} (3^j + (-2)^j)$

*References:*
- [A116150](https://oeis.org/A116150)
-/


-- @@ L26-26 verbatim
namespace OeisA116150


-- @@ L28-28 verbatim
open BigOperators


-- @@ L30-32 verbatim
/-- a n is the sum of $3^j + (-2)^j$ for j from 1 to n. -/
def a (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.Icc 1 n, ((3 : ℤ) ^ j + ((-2) : ℤ) ^ j)).toNat


-- @@ L34-35 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide


-- @@ L37-38 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 14 := by decide


-- @@ L40-41 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 33 := by decide


-- @@ L43-44 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 130 := by decide


-- @@ L46-47 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 341 := by decide


-- @@ L49-56 verbatim
/--
First primes are $a(11) = 264353$ and $a(17) = 193622861$.
Additional primes: $a(71)$, $a(91)$, $a(431)$.
What is the next prime?
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) = a (sInf {n : ℕ | 431 < n ∧ (a n).Prime}) := by
  sorry


-- @@ L58-58 verbatim
end OeisA116150
