/-
Copyright 2025 The Formal Conjectures Authors.

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


-- @@ L19-30 verbatim
/-!
# Sum of a triangular number, a generalized pentagonal number, and a generalized heptagonal number

Any nonnegative integer can be written as $x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2$ with $x, y, z$
nonnegative integers.

Zhi-Wei Sun has offered a USD 135 prize for the first proof of this conjecture.

*References:*
- [A287616](https://oeis.org/A287616)
- Zhi-Wei Sun, "Universal sums of three quadratic polynomials", arXiv:1502.03056 [math.NT]
-/


-- @@ L32-32 verbatim
namespace OeisA287616


-- @@ L34-37 verbatim
/-- The predicate that `n` can be written as $x(x+1)/2 + y(3y+1)/2 + z(5z+1)/2$ for
nonnegative integers $x, y, z$. -/
def A (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (3 * y + 1) / 2 + z * (5 * z + 1) / 2


-- @@ L39-41 verbatim
@[category test, AMS 11]
theorem a_0 : A 0 :=
  ⟨0, 0, 0, by norm_num⟩


-- @@ L43-45 verbatim
@[category test, AMS 11]
theorem a_1 : A 1 :=
  ⟨1, 0, 0, by norm_num⟩


-- @@ L47-49 verbatim
@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 1, 0, by norm_num⟩


-- @@ L51-53 verbatim
@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨2, 0, 0, by norm_num⟩


-- @@ L55-57 verbatim
@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 0, 1, by norm_num⟩


-- @@ L59-66 verbatim
/--
**Zhi-Wei Sun's Conjecture (A287616)**: Any nonnegative integer can be written as the sum of
a triangular number $x(x+1)/2$, a generalized pentagonal number $y(3y+1)/2$, and a generalized
heptagonal number $z(5z+1)/2$, where $x, y, z$ are nonnegative integers.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : A n := by
  sorry


-- @@ L68-68 verbatim
end OeisA287616
