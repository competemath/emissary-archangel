import OAI.Combinatorics.ExpectationThreshold.SelectorTruncationCompact
import OAI.Combinatorics.ExpectationThreshold.SelectorTruncationSlope


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-13 verbatim
/-!
# Maximal weighted truncation

This is the maximal truncation lemma used by the multiscale selector. The
cutoff is obtained from the actual compact admissible set. Its heavy-set
bound follows from the exact affine increase on the next interval between
weights, rather than an assumed slope or regularity certificate.
-/


-- @@ L15-15 verbatim
namespace TalagrandThreshold.Selector


-- @@ L17-17 verbatim
open scoped BigOperators


-- @@ L19-19 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L21-32 verbatim
/-- A nonempty admissible set has a greatest cutoff, whose heavy set satisfies
the multiplied cardinality bound. -/
theorem exists_maximal_truncation (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hm : 0 ≤ m) (hd0 : 0 < d) (hd1 : d < 1)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧
      (∀ u, Admissible w A m d u → u ≤ ε) ∧
      d * ((heavySet w ε).card : ℝ) ≤ m := by
  obtain ⟨ε, hε, hmax⟩ := exists_greatest_admissible w A m d hne
  exact ⟨ε, hε, hmax,
    maximal_admissible_card_bound w A m d ε hw hsum hm hd0 hd1 hε hmax⟩


-- @@ L34-45 verbatim
/-- The division form of the maximal truncation lemma. -/
theorem exists_maximal_truncation_div (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hm : 0 ≤ m) (hd0 : 0 < d) (hd1 : d < 1)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧
      (∀ u, Admissible w A m d u → u ≤ ε) ∧
      ((heavySet w ε).card : ℝ) ≤ m / d := by
  obtain ⟨ε, hε, hmax, hcard⟩ :=
    exists_maximal_truncation w A m d hw hsum hm hd0 hd1 hne
  refine ⟨ε, hε, hmax, (le_div_iff₀ hd0).2 ?_⟩
  simpa only [mul_comm] using hcard


-- @@ L47-47 verbatim
end TalagrandThreshold.Selector


-- @@ L49-49 verbatim
end OAI
