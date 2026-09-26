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
# Number of zeros in ternary representation of $2^n$

*References:*
- [A104320](https://oeis.org/A104320)
-/


-- @@ L26-26 verbatim
namespace OeisA104320


-- @@ L28-33 verbatim
/--
The primary defining sequence `a`.
`a n` is the number of zeros in the ternary representation of $2^n$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 3 (2 ^ n)).count 0


-- @@ L35-37 verbatim
/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by native_decide


-- @@ L39-40 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by native_decide


-- @@ L42-43 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by native_decide


-- @@ L45-46 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by native_decide


-- @@ L48-49 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by native_decide


-- @@ L51-56 verbatim
/--
Conjecture from N. J. A. Sloane: $a(n) > 0$ for $n > 15$.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ n : ℕ, 15 < n → a n > 0 := by
  sorry


-- @@ L58-58 verbatim
end OeisA104320
