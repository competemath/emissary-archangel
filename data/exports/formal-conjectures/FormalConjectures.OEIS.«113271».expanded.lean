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
# Ascending descending base exponent transform of $2^n$

*References:*
- [A113271](https://oeis.org/A113271)
-/


-- @@ L26-26 verbatim
namespace OeisA113271


-- @@ L28-34 verbatim
/--
The primary defining sequence `a`.
$a(n)$ is the ascending descending base exponent transform of $2^n$.
$$a(n) = \sum_{i=0}^n 2^{i \cdot 2^{n-i}}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), 2 ^ (i * 2 ^ (n - i))


-- @@ L36-37 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl


-- @@ L39-40 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl


-- @@ L42-43 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by rfl


-- @@ L45-46 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 41 := by rfl


-- @@ L48-49 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 593 := by rfl


-- @@ L51-58 verbatim
/--
The smallest primes in this (always odd) sequence are $a(1) = 3$, $a(3) = 41$ and $a(5) = 543$.
What is the next prime?
-/
@[category research open, AMS 11]
theorem conjecture1 :
  answer(sorry) = a (sInf {n : ℕ | 5 < n ∧ (a n).Prime}) := by
  sorry


-- @@ L60-60 verbatim
end OeisA113271
