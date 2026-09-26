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
# Apéry numbers

Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$

*References:*
- [A005258](https://oeis.org/A005258)
-/


-- @@ L29-29 verbatim
namespace OeisA5258


-- @@ L31-33 verbatim
/-- Apéry numbers: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k


-- @@ L35-36 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl


-- @@ L38-39 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl


-- @@ L41-42 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 19 := by rfl


-- @@ L44-45 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 147 := by rfl


-- @@ L47-48 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 1251 := by rfl


-- @@ L50-55 verbatim
open Polynomial in
/-- The polynomial associated with the $n$-th Apéry number:
$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$. -/
noncomputable def aperyPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k


-- @@ L57-65 verbatim
/--
For each $n = 1, 2, 3, \dots$ the polynomial
$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$
is irreducible over the field of rational numbers.
- Zhi-Wei Sun, Mar 21 2013
-/
@[category research open, AMS 11 12]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : Irreducible (aperyPoly n) := by
  sorry


-- @@ L67-67 verbatim
end OeisA5258
