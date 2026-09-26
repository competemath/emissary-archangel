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
# Smallest factorial containing exactly $n$ 6's

The sequence $a(n)$ gives the smallest $k$ such that the decimal expansion of $k!$
contains exactly $n$ occurrences of the digit '6', or $0$ if no such $k$ exists.

*References:*
- [A072200](https://oeis.org/A072200)-/


-- @@ L28-28 verbatim
namespace OeisA72200


-- @@ L30-36 verbatim
open Classical in
/-- Smallest $k$ such that $k!$ contains exactly $n$ 6's in base 10, or 0 if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, (Nat.digits 10 k.factorial).count 6 = n then
    Nat.find h
  else
    0


-- @@ L38-46 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨3, by decide +native⟩).elim


-- @@ L48-56 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 15 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨15, by decide +native⟩).elim


-- @@ L58-66 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 23 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨23, by decide +native⟩).elim


-- @@ L68-76 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 26 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨26, by decide +native⟩).elim


-- @@ L78-86 verbatim
/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 32 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨32, by decide +native⟩).elim


-- @@ L88-92 verbatim
/--
It is conjectured that $a(24) = 0$ since no factorial less than $10000$ contained just 24 sixes.-/
@[category research open, AMS 11]
theorem conjecture : a 24 = 0 := by
  sorry


-- @@ L94-94 verbatim
end OeisA72200
