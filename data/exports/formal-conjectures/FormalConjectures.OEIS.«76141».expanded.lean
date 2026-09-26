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
# Number of times $n$ occurs as a binary sub-pattern of $n^2$

The sequence $a(n)$ is the number of times the binary expansion of $n$ appears as a contiguous
sublist (infix) in the binary expansion of $n^2$.

*References:*
- [A076141](https://oeis.org/A076141)-/


-- @@ L28-28 verbatim
namespace OeisA76141


-- @@ L30-33 verbatim
/-- The binary representation of a natural number $n$, most significant bit first.
For $n = 0$, this is $[0]$. -/
def binaryPattern (n : ℕ) : List ℕ :=
  if n = 0 then [0] else (Nat.digits 2 n).reverse


-- @@ L35-39 verbatim
/-- Number of times the binary pattern of $n$ occurs as an infix of the binary pattern of $n^2$. -/
def a (n : ℕ) : ℕ :=
  let pat := binaryPattern n
  let tgt := binaryPattern (n ^ 2)
  tgt.tails.countP (pat.isPrefixOf ·)


-- @@ L41-44 verbatim
/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  decide +native


-- @@ L46-49 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide +native


-- @@ L51-54 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide +native


-- @@ L56-59 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  decide +native


-- @@ L61-64 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  decide +native


-- @@ L66-69 verbatim
/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  decide +native


-- @@ L71-75 verbatim
/--
Is $a(n) \le 1$ for all $n$?-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : a n ≤ 1 := by
  sorry


-- @@ L77-77 verbatim
end OeisA76141
