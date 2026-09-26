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
# Number of pairs of twin primes between $n^2$ and $(n+1)^2$

$a(n)$ is the number of pairs of twin primes between $n^2$ and $(n+1)^2$.
This counts the number of primes $p$ such that $p$ and $p+2$ are both prime,
and the entire twin prime pair $(p, p+2)$ lies strictly between $n^2$ and $(n+1)^2$.
That is, $n^2 < p$ and $p + 2 < (n+1)^2$.

*References:*
- [A091591](https://oeis.org/A091591)-/


-- @@ L30-30 verbatim
namespace OeisA91591


-- @@ L32-35 verbatim
/-- Number of pairs of twin primes $(p, p+2)$ strictly between $n^2$ and $(n+1)^2$. -/
def a (n : ℕ) : ℕ :=
  (((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter
    fun p => p.Prime ∧ (p + 2).Prime ∧ p + 2 < (n + 1) ^ 2)).card


-- @@ L37-39 verbatim
/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide +native


-- @@ L41-43 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +native


-- @@ L45-47 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide +native


-- @@ L49-51 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide +native


-- @@ L53-55 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide +native


-- @@ L57-64 verbatim
/--
It is conjectured that $a(n)>0$ for all $n>122$.
Proving this would also prove Legendre's conjecture that there is a prime
between $n^2$ and $(n+1)^2$. - _T. D. Noe_, Feb 28 2007-/
@[category research open, AMS 11]
theorem conjecture :
    ∀ n : ℕ, n > 122 → a n > 0 := by
  sorry


-- @@ L66-66 verbatim
end OeisA91591
