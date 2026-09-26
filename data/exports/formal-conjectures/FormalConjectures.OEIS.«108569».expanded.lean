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
# Numbers $n$ such that $\phi(n) = \phi(n + \phi(n))$

*References:*
- [A108569](https://oeis.org/A108569)
-/


-- @@ L26-26 verbatim
namespace OeisA108569


-- @@ L28-28 verbatim
open scoped Nat


-- @@ L30-31 verbatim
/-- The predicate defining whether $k$ belongs to the sequence. -/
def A (k : ℕ) : Prop := 0 < k ∧ φ k = φ (k + φ k)


-- @@ L33-35 verbatim
instance : DecidablePred A := by
  unfold A
  infer_instance


-- @@ L37-42 verbatim
/--
The primary defining sequence `a`.
`a n` is the $(n+1)$-th positive integer $k$ such that $\phi(k) = \phi(k + \phi(k))$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A


-- @@ L44-50 verbatim
/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this


-- @@ L52-57 verbatim
@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 1 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this


-- @@ L59-64 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by
  have h8 : A 8 := by decide
  have hcnt : Nat.count A 8 = 2 := by decide
  have := Nat.nth_count (p := A) h8
  rwa [hcnt] at this


-- @@ L66-71 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 16 := by
  have h16 : A 16 := by decide
  have hcnt : Nat.count A 16 = 3 := by decide
  have := Nat.nth_count (p := A) h16
  rwa [hcnt] at this


-- @@ L73-78 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 32 := by
  have h32 : A 32 := by decide
  have hcnt : Nat.count A 32 = 4 := by decide
  have := Nat.nth_count (p := A) h32
  rwa [hcnt] at this


-- @@ L80-83 verbatim
/-- Conjecture: Except for the first term all terms are even. -/
@[category research open, AMS 11]
theorem conjecture : ∀ n, 0 < n → Even (a n) := by
  sorry


-- @@ L85-85 verbatim
end OeisA108569
