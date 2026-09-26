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
# Number of digits of n raised to the power of the sum of the digits of n

*References:*
- [A113010](https://oeis.org/A113010)
-/


-- @@ L26-26 verbatim
namespace OeisA113010


-- @@ L28-28 verbatim
open Nat


-- @@ L30-34 verbatim
/--
a n is the {Number of digits of n} raised to the power of {the sum of the digits of n}.
-/
def a (n : ℕ) : ℕ :=
  ((10).digits n).length ^ (List.sum ((10).digits n))


-- @@ L36-37 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide


-- @@ L39-40 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide


-- @@ L42-43 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide


-- @@ L45-46 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by native_decide


-- @@ L48-49 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide


-- @@ L51-56 verbatim
/--
$n=1$ and $32$ are two fixed points. Are there any others?
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) ↔ ∀ n : ℕ, a n = n ∧ n > 0 → n = 1 ∨ n = 32 := by
  sorry


-- @@ L58-58 verbatim
end OeisA113010
