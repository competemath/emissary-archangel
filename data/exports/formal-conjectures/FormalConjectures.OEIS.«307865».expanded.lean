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
# Vanishing of bases with $b^n \equiv -1 \pmod{2n+1}$ for absolute Euler pseudoprimes

$a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.

If $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.

*References:*
- [A307865](https://oeis.org/A307865)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/


-- @@ L31-31 verbatim
namespace OeisA307865



-- @@ L34-34 verbatim
open Nat Finset ZMod


-- @@ L36-44 verbatim
/--
$a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$.
We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card


-- @@ L46-46 verbatim
variable {n : ℕ}


-- @@ L48-54 verbatim
/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)



-- @@ L57-58 verbatim
@[category test, AMS 11]
lemma a_0 : a 0 = 0 := by rfl


-- @@ L60-61 verbatim
@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl


-- @@ L63-64 verbatim
@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by rfl


-- @@ L66-67 verbatim
@[category test, AMS 11]
lemma a_3 : a 3 = 3 := by rfl


-- @@ L69-70 verbatim
@[category test, AMS 11]
lemma a_4 : a 4 = 0 := by rfl



-- @@ L73-82 verbatim
/--
Conjecture: if $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/307865.wip.lean#L190"]
theorem a_eq_zero_of_pseudoprime (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
    sorry


-- @@ L84-84 verbatim
end OeisA307865
