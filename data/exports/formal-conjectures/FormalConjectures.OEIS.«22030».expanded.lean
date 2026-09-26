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
# A nonlinear recurrence sequence

For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.

*References:*
- [A022030](https://oeis.org/A022030)
-/


-- @@ L30-30 verbatim
namespace OeisA22030


-- @@ L32-45 verbatim
/--
For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1


-- @@ L47-48 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 4 := by rfl


-- @@ L50-51 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 16 := by rfl


-- @@ L53-54 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 63 := by rfl


-- @@ L56-57 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 249 := by rfl


-- @@ L59-60 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 984 := by rfl


-- @@ L62-63 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 3889 := by rfl


-- @@ L65-72 verbatim
/--
Conjecture: $a(n) = 4 a(n-1) - a(n-3) + a(n-4)$.
- Colin Barker, Feb 16 2012
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 4 ≤ n) :
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) := by
  sorry


-- @@ L74-74 verbatim
end OeisA22030
