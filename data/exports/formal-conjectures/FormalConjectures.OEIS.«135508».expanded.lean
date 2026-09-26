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
# Recurrence involving LCM: $a(n) = x(n+1)/x(n) - 2$

$a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2 x(n-1) + \operatorname{lcm}(x(n-1),n)$
for $n > 1$.

*References:*
- [A135508](https://oeis.org/A135508)-/


-- @@ L28-28 verbatim
namespace OeisA135508


-- @@ L30-34 verbatim
/-- Auxiliary sequence $x(n)$ with $x(1)=1$ and $x(n) = 2 x(n-1) + \operatorname{lcm}(x(n-1),n)$. -/
def x : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => 2 * x n + Nat.lcm (x n) (n + 1)


-- @@ L36-38 verbatim
/-- $a(n) = x(n+1)/x(n) - 2$ for $n \ge 1$, and $a(0) = 0$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (x (n + 1) / x n) - 2


-- @@ L40-42 verbatim
/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl


-- @@ L44-46 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rfl


-- @@ L48-50 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl


-- @@ L52-54 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl


-- @@ L56-58 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl


-- @@ L60-66 verbatim
/--
Conjecture: For prime $p$ such that $p-2$ is not a prime, $a(p-1) = p$.
- _Bill McEachen_, Sep 26 2025
-/
@[category research open, AMS 11]
theorem conjecture (p : ℕ) (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p := by
  sorry


-- @@ L68-68 verbatim
end OeisA135508
