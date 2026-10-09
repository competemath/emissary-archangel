import OAI.Combinatorics.ExpectationThreshold.SelectorCountingWordsTransport
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-14 verbatim
/-!
# Counting row encodings

A row encoding chooses a subset of the available positions and labels those
positions with a word of a prescribed profile. The word count depends only on
the number of chosen positions, so the total count factors into a binomial
coefficient and the corresponding word count.
-/


-- @@ L16-16 verbatim
namespace TalagrandThreshold


-- @@ L18-18 verbatim
open scoped BigOperators


-- @@ L20-20 verbatim
variable {α H : Type*} [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]


-- @@ L22-31 verbatim
/-- The number of subsets of `R` with exactly `t` elements. -/
theorem card_fixedSize_subsets (R : Finset α) (t : ℕ) :
    Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} =
      Nat.choose R.card t := by
  calc
    Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} =
        (R.powersetCard t).card :=
      Fintype.card_of_subtype (R.powersetCard t)
        (fun _ => Finset.mem_powersetCard)
    _ = Nat.choose R.card t := Finset.card_powersetCard t R


-- @@ L33-35 verbatim
/-- A chosen set of positions together with labels of the prescribed profile. -/
def RowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) : Type _ :=
  Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)


-- @@ L37-40 verbatim
noncomputable instance instFintypeRowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) :
    Fintype (RowEncoding R t n) :=
  inferInstanceAs (Fintype
    (Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)))


-- @@ L42-62 verbatim
/-- Each chosen set admits the same number of words, so the count factors. -/
theorem card_rowEncoding (R : Finset α) (t : ℕ) (n : H → ℕ) :
    Fintype.card (RowEncoding R t n) = Nat.choose R.card t * wordCount t n := by
  classical
  change Fintype.card
    (Σ U : {U : Finset α // U ⊆ R ∧ U.card = t}, ↥(wordFiber ↥U.val n)) = _
  rw [Fintype.card_sigma]
  have hFiber (U : {U : Finset α // U ⊆ R ∧ U.card = t}) :
      Fintype.card ↥(wordFiber ↥U.val n) = wordCount t n := by
    rw [Fintype.card_coe, wordFiber_finset_card, U.property.2]
  calc
    (∑ U : {U : Finset α // U ⊆ R ∧ U.card = t},
        Fintype.card ↥(wordFiber ↥U.val n)) =
        Fintype.card {U : Finset α // U ⊆ R ∧ U.card = t} * wordCount t n := by
      simpa only [Finset.card_univ] using
        (Finset.sum_const_nat (s := Finset.univ)
          (f := fun U : {U : Finset α // U ⊆ R ∧ U.card = t} =>
            Fintype.card ↥(wordFiber ↥U.val n))
          (m := wordCount t n) (fun U _ => hFiber U))
    _ = Nat.choose R.card t * wordCount t n := by
      rw [card_fixedSize_subsets]


-- @@ L64-64 verbatim
end TalagrandThreshold


-- @@ L66-66 verbatim
end OAI
