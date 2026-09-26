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


-- @@ L19-29 verbatim
/-!
# Fractional parts of sums of reciprocals of Catalan numbers $C(n)$

Catalan numbers $C(n) = \frac{1}{n+1}\binom{2n}{n}$.

The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers.

*References:*
- [A000108](https://oeis.org/A000108)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/


-- @@ L31-31 verbatim
namespace OeisA108



-- @@ L34-34 verbatim
open Nat Real Finset


-- @@ L36-39 verbatim
/--
Catalan numbers $C(n) = \frac{1}{n+1}\binom{2n}{n}$.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)


-- @@ L41-41 verbatim
def aRat (n : ℕ) : ℚ := (a n : ℚ)⁻¹


-- @@ L43-45 verbatim
/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalanReciprocalSum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum aRat


-- @@ L47-50 verbatim
/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def IndexCond (j k : ℕ) : Prop :=
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k


-- @@ L52-52 verbatim
open Int (fract)


-- @@ L54-55 verbatim
/-- The fractional part of a rational number. -/
def fracPart (q : ℚ) : ℚ := fract q



-- @@ L58-59 verbatim
@[category test, AMS 11]
lemma a_0 : a 0 = 1 := by rfl


-- @@ L61-62 verbatim
@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl


-- @@ L64-65 verbatim
@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by rfl


-- @@ L67-68 verbatim
@[category test, AMS 11]
lemma a_3 : a 3 = 5 := by rfl


-- @@ L70-71 verbatim
@[category test, AMS 11]
lemma a_4 : a 4 = 14 := by rfl



-- @@ L74-87 verbatim
/--
Conjecture: All the rational numbers $\sum_{i=j}^k \frac{1}{a(i)}$ with
$0 < \min\{2,k\} \le j \le k$ have pairwise distinct fractional parts.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/108.wip.lean#L255"]
theorem catalanReciprocalSum_fracPart_inj : ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
    IndexCond j₁ k₁ → IndexCond j₂ k₂ →
    (j₁, k₁) ≠ (j₂, k₂) →
    fracPart (catalanReciprocalSum j₁ k₁) ≠ fracPart (catalanReciprocalSum j₂ k₂) := by
    sorry


-- @@ L89-89 verbatim
end OeisA108
