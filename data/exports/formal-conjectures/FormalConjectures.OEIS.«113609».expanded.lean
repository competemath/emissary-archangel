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
# Number of prime powers $q<=n$ such that also $q+2$ is a prime power

*References:*
- [A113609](https://oeis.org/A113609)
-/


-- @@ L26-26 verbatim
namespace OeisA113609


-- @@ L28-32 verbatim
/--
A number $n$ is an "OEIS prime power" (for the context of A113609's definition)
if $n=1$ or $n$ is a standard prime power.
-/
def IsOeisPrimePower (n : ℕ) : Prop := n = 1 ∨ IsPrimePow n


-- @@ L34-36 verbatim
instance DecidableIsOeisPrimePower (n : ℕ) : Decidable (IsOeisPrimePower n) := by
  simp only [IsOeisPrimePower]
  exact instDecidableOr


-- @@ L38-45 verbatim
/--
The primary defining sequence `a`.
$a(n)$ is the number of prime powers $q<=n$ such that also $q+2$ is a prime power.
$$a(n) = \operatorname{card} \{q \in \mathbb{N} \mid 1 \le q \le n \land P(q) \land P(q+2) \}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.range (n + 1)).filter fun q =>
    IsOeisPrimePower q ∧ IsOeisPrimePower (q + 2) ∧ q ≥ 1


-- @@ L47-48 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide


-- @@ L50-51 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by native_decide


-- @@ L53-54 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by native_decide


-- @@ L56-57 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by native_decide


-- @@ L59-60 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by native_decide


-- @@ L62-71 verbatim
/--
(25,27) is the smallest pair of prime powers (q,q+2) such that both q and q+2 are not primes,
conjecture: there are more (but not < 10^6).
-/
@[category research open, AMS 11]
theorem conjecture :
  answer(sorry) ↔ ∃ q ≥ 1000000,
    IsOeisPrimePower q ∧ IsOeisPrimePower (q + 2) ∧
    ¬ q.Prime ∧ ¬ (q + 2).Prime := by
  sorry


-- @@ L73-73 verbatim
end OeisA113609
