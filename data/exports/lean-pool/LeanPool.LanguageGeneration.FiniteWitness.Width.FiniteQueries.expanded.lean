/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Characterization
public import Mathlib.Data.Finset.Prod


-- @@ L11-13 verbatim
/-!
# Finite history domains and query bounds for normalization
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace GenLimit.FiniteWitness


-- @@ L19-19 verbatim
variable {α : Type*} [DecidableEq α]


-- @@ L21-24 verbatim
/-- A constructive enumeration, including repetitions, of every word of bounded length. -/
def boundedWords (S : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] ((S ×ˢ boundedWords S n).image (fun p => p.1 :: p.2))


-- @@ L26-34 verbatim
theorem mem_boundedWords {S : Finset α} {n : ℕ} {q : List α} :
    q ∈ boundedWords S n ↔ q.toFinset ⊆ S ∧ q.length ≤ n := by
  induction n generalizing q with
  | zero => cases q <;> simp [boundedWords]
  | succ n ih =>
    cases q with
    | nil => simp [boundedWords]
    | cons a q =>
      simp [boundedWords, ih, Finset.insert_subset_iff, and_assoc]


-- @@ L36-36 verbatim
variable [Encodable α]


-- @@ L38-47 verbatim
theorem Candidate.congr_oracle {F G : List α → α} {S : Finset α} {n k : ℕ}
    (h : ∀ q ∈ boundedWords S (2 * n), F q = G q) (p q : List α) :
    Candidate F S n p k q ↔ Candidate G S n p k q := by
  constructor
  · intro hc
    have he := h q (mem_boundedWords.mpr ⟨hc.2.2.1, hc.2.2.2.1⟩)
    simpa only [Candidate, he] using hc
  · intro hc
    have he := h q (mem_boundedWords.mpr ⟨hc.2.2.1, hc.2.2.2.1⟩)
    simpa only [Candidate, he] using hc


-- @@ L49-59 verbatim
theorem sampleRun_congr_oracle {F G : List α → α} {S : Finset α} {n : ℕ}
    (h : ∀ q ∈ boundedWords S (2 * n), F q = G q) (k : ℕ) :
    sampleRun F S n k = sampleRun G S n k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : Candidate F S n (sampleRun G S n k) k =
        Candidate G S n (sampleRun G S n k) k :=
      funext (fun q => propext (Candidate.congr_oracle h _ q))
    simp only [sampleRun, ih, hp]


-- @@ L61-66 verbatim
/-- One finite set of oracle inputs, fixed by S alone, determines the normalized output. -/
theorem normalized_finite_query_bound {F G : List α → α} (S : Finset α)
    (h : ∀ q ∈ boundedWords S (2 * S.card), F q = G q) : normalized F S = normalized G S := by
  unfold normalized
  rw [sampleRun_congr_oracle h]
  exact h _ (mem_boundedWords.mpr ⟨sampleRun_content _ _ _ _, sampleRun_length _ _ _ _⟩)


-- @@ L68-68 verbatim
end GenLimit.FiniteWitness
