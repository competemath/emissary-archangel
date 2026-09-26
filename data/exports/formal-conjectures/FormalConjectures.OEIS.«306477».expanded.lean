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


-- @@ L19-32 verbatim
/-!
# The 2-4-6-8 Conjecture

Any integer $n > 0$ can be written as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w, x, y, z$ nonnegative integers.

Zhi-Wei Sun has offered a $2,468 prize for the first proof (or $2,468 RMB for a counterexample).

The conjecture has been verified for all $n$ up to $1.2 \times 10^{12}$ by Yaakov Baruch (March 2019).

*References:*
- [A306477](https://oeis.org/A306477)
- [mathoverflow/323541](https://mathoverflow.net/questions/323541): Z.-W. Sun, "Positive integers written as C(w,2) + C(x,4) + C(y,6) + C(z,8) with w,x,y,z in {2,3,...},", Feb. 19, 2019.
-/


-- @@ L34-34 verbatim
namespace OeisA306477


-- @@ L36-39 verbatim
/-- The predicate that `n` can be written as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
for nonnegative integers $w, x, y, z$. -/
def A (n : ℕ) : Prop :=
  ∃ w x y z : ℕ, n = (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8


-- @@ L41-43 verbatim
@[category test, AMS 11]
theorem a_1 : A 1 :=
  ⟨0, 0, 0, 0, by decide⟩


-- @@ L45-47 verbatim
@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 1, 0, 0, by decide⟩


-- @@ L49-51 verbatim
@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by decide⟩


-- @@ L53-55 verbatim
@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨1, 1, 0, 0, by decide⟩


-- @@ L57-59 verbatim
@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨1, 1, 1, 0, by decide⟩


-- @@ L61-63 verbatim
@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨2, 0, 0, 0, by decide⟩


-- @@ L65-71 verbatim
/--
**Zhi-Wei Sun's 2-4-6-8 Conjecture (A306477)**: Any integer $n > 0$ can be written as
$\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$ for nonnegative integers $w, x, y, z$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : A n := by
  sorry


-- @@ L73-73 verbatim
end OeisA306477
