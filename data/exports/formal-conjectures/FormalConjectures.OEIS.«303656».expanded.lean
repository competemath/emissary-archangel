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


-- @@ L19-37 verbatim
/-!
# Sum of two squares, a power of 3, and a power of 5

Any integer $n > 1$ can be written as $a^2 + b^2 + 3^c + 5^d$ where $a, b, c, d$ are
nonnegative integers.

Zhi-Wei Sun has offered a \$3,500 prize for the first proof.

*References:*
- [A303656](https://oeis.org/A303656)
- Z.-W. Sun, "Restricted sums of four squares," arXiv preprint:
  https://arxiv.org/abs/1701.05868v10
- Z.-W. Sun, "Refining Lagrange's four-square theorem," Journal of Number Theory:
  http://maths.nju.edu.cn/~zwsun/RefineFourSquareTh.pdf
- Z.-W. Sun, "Restricted sums of three or four squares":
  http://maths.nju.edu.cn/~zwsun/Square-sum.pdf
- Zhi-Wei Sun's 1-3-5 conjecture and variations:
  https://www.aimspress.com/aimspress-data/era/2020/2/PDF/1935-9179_2020_2_589.pdf
-/


-- @@ L39-39 verbatim
namespace OeisA303656


-- @@ L41-43 verbatim
/-- The predicate that `n` can be written as $a^2 + b^2 + 3^c + 5^d$ for nonnegative integers. -/
def A (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + 3 ^ c + 5 ^ d


-- @@ L45-47 verbatim
@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 0, 0, 0, by norm_num⟩


-- @@ L49-51 verbatim
@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by norm_num⟩


-- @@ L53-55 verbatim
@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 1, 0, 0, by norm_num⟩


-- @@ L57-59 verbatim
@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨0, 1, 1, 0, by norm_num⟩


-- @@ L61-63 verbatim
@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨0, 0, 0, 1, by norm_num⟩


-- @@ L65-67 verbatim
@[category test, AMS 11]
theorem a_25 : A 25 :=
  ⟨1, 4, 1, 1, by norm_num⟩


-- @@ L69-75 verbatim
/--
**Zhi-Wei Sun's Conjecture (A303656)**: Any integer $n > 1$ can be written as the sum of two
squares, a power of 3, and a power of 5.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : A n := by
  sorry


-- @@ L77-77 verbatim
end OeisA303656
