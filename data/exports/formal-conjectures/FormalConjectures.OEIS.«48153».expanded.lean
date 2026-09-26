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


-- @@ L19-23 verbatim
/-!
# $a(n) = \sum_{k=1}^n (k^2 \bmod n)$

*References:*
- [A048153](https://oeis.org/A048153)-/


-- @@ L25-25 verbatim
namespace OeisA48153


-- @@ L27-29 verbatim
/-- $a(n) = \sum_{k=1}^n (k^2 \bmod n)$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (k ^ 2 % n)


-- @@ L31-34 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide


-- @@ L36-39 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide


-- @@ L41-44 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  decide


-- @@ L46-49 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  decide


-- @@ L51-54 verbatim
/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 10 := by
  decide


-- @@ L56-60 verbatim
/--
"Conjecture: $a(n) <= \frac{n^2-1}{2}$. - _Aspen A.M. Meissner_, Mar 06 2025"-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : a n ≤ (n ^ 2 - 1) / 2 := by
  sorry


-- @@ L62-62 verbatim
end OeisA48153
