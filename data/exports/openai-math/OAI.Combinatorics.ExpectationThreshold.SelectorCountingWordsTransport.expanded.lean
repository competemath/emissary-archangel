import OAI.Combinatorics.ExpectationThreshold.SelectorCountingWords
import Mathlib.Data.Fintype.EquivFin


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# Transport of words with a prescribed profile

Reindexing the domain of a word preserves every letter count. Consequently,
the number of words with a prescribed profile depends only on the size of
the domain, including when that domain is the subtype of a finite set.
-/


-- @@ L14-14 verbatim
namespace TalagrandThreshold


-- @@ L16-16 verbatim
section Profile


-- @@ L18-18 verbatim
variable {D E H : Type*} [Fintype D] [Fintype E] [DecidableEq H]


-- @@ L20-28 verbatim
/-- A domain equivalence preserves the profile of a word. -/
theorem wordProfile_comp_equiv (e : D ≃ E) (f : E → H) :
    wordProfile (f ∘ e) = wordProfile f := by
  funext h
  change (Finset.univ.filter (fun i : D => f (e i) = h)).card =
    (Finset.univ.filter (fun j : E => f j = h)).card
  apply Finset.card_equiv e
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


-- @@ L30-30 verbatim
end Profile


-- @@ L32-32 verbatim
section Fiber


-- @@ L34-34 verbatim
variable {D E H : Type*} [Fintype D] [Fintype E]

-- @@ L35-35 verbatim
variable [DecidableEq D] [DecidableEq E] [Fintype H] [DecidableEq H]


-- @@ L37-49 verbatim
/-- Reindexing gives an equivalence between words of the same profile. -/
def wordFiberEquiv (e : D ≃ E) (n : H → ℕ) :
    ↥(wordFiber D n) ≃ ↥(wordFiber E n) := by
  refine Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl H)) ?_
  intro f
  change f ∈ Finset.univ.filter (fun g : D → H => wordProfile g = n) ↔
    (f ∘ e.symm) ∈ Finset.univ.filter (fun g : E → H => wordProfile g = n)
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro hf
    exact ⟨Finset.mem_univ _, (wordProfile_comp_equiv e.symm f).trans hf.2⟩
  · intro hf
    exact ⟨Finset.mem_univ _, (wordProfile_comp_equiv e.symm f).symm.trans hf.2⟩


-- @@ L51-54 verbatim
/-- Equivalent finite domains have equally many words of each profile. -/
theorem wordFiber_card_eq_of_equiv (e : D ≃ E) (n : H → ℕ) :
    (wordFiber D n).card = (wordFiber E n).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (wordFiberEquiv e n)


-- @@ L56-56 verbatim
end Fiber


-- @@ L58-63 verbatim
/-- The word count on any finite domain agrees with the count on `Fin`. -/
theorem wordFiber_card_eq_wordCount (D : Type*) {H : Type*}
    [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H] (n : H → ℕ) :
    (wordFiber D n).card = wordCount (Fintype.card D) n := by
  change (wordFiber D n).card = (wordFiber (Fin (Fintype.card D)) n).card
  exact wordFiber_card_eq_of_equiv (Fintype.equivFin D) n


-- @@ L65-70 verbatim
/-- Labels on a finite set are counted by the word count for its cardinality. -/
theorem wordFiber_finset_card {α H : Type*} [DecidableEq α]
    [Fintype H] [DecidableEq H] (U : Finset α) (n : H → ℕ) :
    (wordFiber ↥U n).card = wordCount U.card n := by
  change (wordFiber ↥U n).card = (wordFiber (Fin U.card) n).card
  exact wordFiber_card_eq_of_equiv U.equivFin n


-- @@ L72-72 verbatim
end TalagrandThreshold


-- @@ L74-74 verbatim
end OAI
