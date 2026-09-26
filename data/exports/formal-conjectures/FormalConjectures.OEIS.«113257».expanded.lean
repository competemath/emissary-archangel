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
# Ascending descending base exponent transform of squares

a n is $\sum_{i=1}^n (i^2)^((n-i+1)^2)$.

*References:*
- [A113257](https://oeis.org/A113257)
-/


-- @@ L28-28 verbatim
namespace OeisA113257


-- @@ L30-32 verbatim
/-- a n is the ascending descending base exponent transform of squares -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, (i ^ 2) ^ ((n - i + 1) ^ 2)


-- @@ L34-35 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide


-- @@ L37-38 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by decide


-- @@ L40-41 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 266 := by decide


-- @@ L43-44 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 268722 := by decide


-- @@ L46-47 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 4682453347 := by decide


-- @@ L49-55 verbatim
/--
The smallest prime in this sequence is $a(2) = 5$. What is the next prime?
-/
@[category research open, AMS 11]
theorem conjecture1 :
    answer(sorry) = a (sInf {n : ℕ | 2 < n ∧ (a n).Prime}) := by
  sorry


-- @@ L57-63 verbatim
/--
What is the first square value after 1?
-/
@[category research open, AMS 11]
theorem conjecture2 :
    answer(sorry) = a (sInf {n : ℕ | 1 < n ∧ IsSquare (a n)}) := by
  sorry


-- @@ L65-65 verbatim
end OeisA113257
