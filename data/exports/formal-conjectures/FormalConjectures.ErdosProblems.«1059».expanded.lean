/-
Copyright 2025 The Formal Conjectures Authors.

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


-- @@ L19-23 verbatim
/-!
# Erdős Problem 1059

*Reference:* [erdosproblems.com/1059](https://www.erdosproblems.com/1059)
-/


-- @@ L25-25 verbatim
namespace Erdos1059


-- @@ L27-28 verbatim
def IsFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial


-- @@ L30-31 verbatim
def factorialsLessThanN (n : ℕ) : Set ℕ :=
  { d | d < n ∧ IsFactorial d }


-- @@ L33-34 verbatim
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀d ∈ factorialsLessThanN n, (n - d).Composite


-- @@ L36-40 verbatim
/-- Are there infinitely many primes $p$ such that $p - k!$ is composite for each $k$ such that $1 ≤ k! < p$? -/
@[category research open, AMS 11]
theorem erdos_1059 :
    answer(sorry) ↔ Set.Infinite {p | p.Prime ∧ AllFactorialSubtractionsComposite p} := by
  sorry


-- @@ L42-43 verbatim
abbrev DecidableIsFactorial (d : ℕ) : Prop :=
  ((Finset.Icc 0 d).filter (λ k => Nat.factorial k = d)).Nonempty


-- @@ L45-46 verbatim
def decidableFactorialsLessThanN (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter DecidableIsFactorial


-- @@ L48-49 verbatim
def DecidableAllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ decidableFactorialsLessThanN n, (n - d).Composite


-- @@ L51-70 verbatim
@[category test, AMS 11]
lemma isFactorial_equivalent (d : ℕ) :
  IsFactorial d ↔ DecidableIsFactorial d := by
  unfold IsFactorial DecidableIsFactorial
  simp
  constructor
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter]
    constructor
    · have hk : k <= d := by
        rw [← hk]
        apply Nat.self_le_factorial
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le k, hk⟩
    · exact hk
  · rintro ⟨k, hk⟩
    use k
    rw [Finset.mem_filter] at hk
    exact hk.2


-- @@ L72-78 verbatim
@[category test, AMS 11]
lemma factorialsLessThanN_equivalent (n : ℕ) :
  factorialsLessThanN n = ↑(decidableFactorialsLessThanN n) := by
  ext d
  unfold factorialsLessThanN decidableFactorialsLessThanN
  simp
  exact λ _ => isFactorial_equivalent d


-- @@ L80-85 verbatim
@[category test, AMS 11]
lemma allFactorialSubtractionsComposite_equivalent (d : ℕ) :
    DecidableAllFactorialSubtractionsComposite d ↔ AllFactorialSubtractionsComposite d := by
  unfold AllFactorialSubtractionsComposite DecidableAllFactorialSubtractionsComposite
  rw [factorialsLessThanN_equivalent d]
  simp


-- @@ L87-92 verbatim
@[category test, AMS 11]
theorem allFactorialSubtractionsComposite_101 : AllFactorialSubtractionsComposite 101 := by
  have h : DecidableAllFactorialSubtractionsComposite 101 := by
    norm_num [DecidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 101).mp h


-- @@ L94-99 verbatim
@[category test, AMS 11]
theorem allFactorialSubtractionsComposite_211 : AllFactorialSubtractionsComposite 211 := by
  have h : DecidableAllFactorialSubtractionsComposite 211 := by
    norm_num [DecidableAllFactorialSubtractionsComposite, decidableFactorialsLessThanN]
    decide +kernel
  exact (allFactorialSubtractionsComposite_equivalent 211).mp h


-- @@ L101-110 verbatim
@[category test, AMS 11]
theorem notAllFactorialSubtractionsComposite_89 : ¬(AllFactorialSubtractionsComposite 89) := by
  have h : ¬(DecidableAllFactorialSubtractionsComposite 89) := by
    unfold DecidableAllFactorialSubtractionsComposite decidableFactorialsLessThanN
    intro h
    specialize h 6
    have : Nat.Prime (89 - 6) := by norm_num
    contradiction
  simp [allFactorialSubtractionsComposite_equivalent] at h
  exact h


-- @@ L112-118 verbatim
@[category test, AMS 11]
theorem testFactorialsLessThanN : factorialsLessThanN 100 = {1, 2, 6, 24} := by
  have h : decidableFactorialsLessThanN 100 = {1, 2, 6, 24} := by
    norm_num [decidableFactorialsLessThanN]
    decide +kernel
  rw [factorialsLessThanN_equivalent]
  simp [h]


-- @@ L120-120 verbatim
end Erdos1059
