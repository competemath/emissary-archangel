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


-- @@ L19-28 verbatim
/-!
# Sum of $a(k)/k!$ over divisors equals harmonic number

The sequence $a(n)$ satisfies $\sum_{k \mid n} \frac{a(k)}{k!} = \sum_{j=1}^n \frac{1}{j} = H_n$,
where the sum on the left is over positive divisors $k$ of $n$. By Möbius inversion,
$$a(n) = n! \sum_{d \mid n} \mu(n/d) H_d$$
where $H_d = \sum_{j=1}^d \frac{1}{j}$ is the $d$-th harmonic number.

*References:*
- [A067857](https://oeis.org/A067857)-/


-- @@ L30-30 verbatim
namespace OeisA67857


-- @@ L32-32 verbatim
open ArithmeticFunction Finset


-- @@ L34-39 verbatim
/-- The sequence $a(n) = n! \sum_{d \mid n} \mu(n/d) H_d$ for $n \ge 1$, and $a(0) = 0$. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    (n.factorial : ℚ) *
      ∑ d ∈ n.divisors, ((moebius (n / d) : ℤ) : ℚ) * harmonic d


-- @@ L41-44 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide +native


-- @@ L46-49 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide +native


-- @@ L51-54 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  decide +native


-- @@ L56-59 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 14 := by
  decide +native


-- @@ L61-64 verbatim
/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 154 := by
  decide +native


-- @@ L66-73 verbatim
/--
The terms are not all positive. The first negative one is
$a(30) = -22690644647302814715858124800000$.
Conjecture: $a(n) < 0$ if and only if A001221(n) is an odd number $\ge 3$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    a n < 0 ↔ Odd (cardDistinctFactors n) ∧ 3 ≤ cardDistinctFactors n := by
  sorry


-- @@ L75-75 verbatim
end OeisA67857
