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
# Lesser of twin primes

Primes $p$ such that $p+2$ is also prime.

*References:*
- [A001359](https://oeis.org/A001359)
-/


-- @@ L28-28 verbatim
namespace OeisA1359


-- @@ L30-35 verbatim
/-- The $n$-th lesser twin prime, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) (n - 1)
  else
    0


-- @@ L37-39 verbatim
/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl


-- @@ L41-45 verbatim
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  norm_num[a]
  exact(((congr_arg _) (by constructor) )).trans.comp (3).nth_count (by decide)


-- @@ L47-51 verbatim
/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  delta a
  apply((congr_arg _) (by constructor) ).trans (Nat.nth_count (by decide ) )


-- @@ L53-58 verbatim
/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 11 := by
  (inhabit ℝ)
  norm_num[a]
  exact (congr_arg _ (by decide)).trans (Nat.nth_count (by decide))


-- @@ L60-64 verbatim
/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 17 := by
  simp_all[a]
  exact (congr_arg _ (by constructor) ).trans (Nat.nth_count (by decide))


-- @@ L66-80 verbatim
/--
Primes $p_k$ such that $p_k! \equiv 1 \pmod{p_{k+1}}$ with the exception of $p_{991} = 7841$ and
other unknown primes $p_k$ for which $(p_k+1)(p_k+2)\cdots(p_{k+1}-2) \equiv 1 \pmod{p_{k+1}}$
where $p_{k+1} - p_k > 2$.
-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) (hk : k > 1) :
    let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])) :=
        by
  sorry


-- @@ L82-82 verbatim
end OeisA1359
