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


-- @@ L19-27 verbatim
/-!
# A generalized Stern sequence

A112970: A generalized Stern sequence, defined by the recurrence relations:
$a(2n+1) = a(n)$ and $a(2n) = a(n) + a(n-2)$ with $a(0)=1$, $a(1)=1$ and $a(n)=0$ for $n \le -1$.

*References:*
- [A112970](https://oeis.org/A112970)
-/


-- @@ L29-29 verbatim
namespace OeisA112970


-- @@ L31-49 verbatim
/--
a n is the generalized Stern sequence, defined by the recurrence relations:
$a(2n+1) = a(n)$ and $a(2n) = a(n)$ + $a(n-2)$ with $a(0) = 1$, $a(1) = 1$
and $a(n) = 0$ for $n \le -1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let k := n / 2
    if n % 2 = 1 then -- Odd case: a(2k + 1) = a(k)
      a k
    else -- Even case: a(2k) = a(k) + a(k - 2)
      let aPrev : ℕ :=
        -- a(m) is 0 if m < 0. Equivalent to checking k < 2 for the argument k-2.
        if k < 2 then 0
        else a (k - 2)
      a k + aPrev
termination_by n


-- @@ L51-52 verbatim
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by unfold a; rfl


-- @@ L54-55 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by unfold a; rfl


-- @@ L57-58 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by unfold a; unfold a; unfold a; rfl


-- @@ L60-61 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by unfold a; unfold a; rfl


-- @@ L63-64 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by unfold a; unfold a; unfold a; unfold a; rfl


-- @@ L66-74 verbatim
/--
Conjectures: a(2^n)=a(2^(n+1)+1)=A033638(n).
This formalizes the equality a(2^n) = a(2^(n+1)+1).
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L43-L46"]
theorem conjecture1 (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  sorry


-- @@ L76-81 verbatim
/-- Conjectures: a(2^n-1)=a(3*2^n-1)=1. This formalizes the equality part a(2^n-1) = a(3*2^n-1). -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L56-L64"]
theorem conjecture2 (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  sorry


-- @@ L83-88 verbatim
/-- Conjectures: a(2^n-1)=a(3*2^n-1)=1. This formalizes the value part a(2^n-1)=1. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L48-L54"]
theorem conjecture3 (n : ℕ) : a (2^n - 1) = 1 := by
  sorry


-- @@ L90-90 verbatim
end OeisA112970
