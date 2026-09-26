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
# Ascending descending base exponent transform of factorials

*References:*
- [A113258](https://oeis.org/A113258)
-/


-- @@ L26-26 verbatim
namespace OeisA113258


-- @@ L28-28 verbatim
open Nat


-- @@ L30-36 verbatim
/--
The primary defining sequence `a`.
$a(n)$ is the ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (i + 1)! ^ (n - i)!


-- @@ L38-39 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl


-- @@ L41-42 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl


-- @@ L44-45 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 11 := by rfl


-- @@ L47-48 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 125 := by rfl


-- @@ L50-56 verbatim
/--
Is there a nontrivial power after $a(4) = 5^3$?
-/
@[category research open, AMS 11]
theorem conjecture :
  answer(sorry) ↔ ∃ n > 4, ∃ b > 1, ∃ e > 1, a n = b ^ e := by
  sorry


-- @@ L58-58 verbatim
end OeisA113258
