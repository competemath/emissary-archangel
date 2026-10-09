import OAI.Combinatorics.ExpectationThreshold.SelectorTruncationDefinitions
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-17 verbatim
/-!
# Existence of the maximal admissible truncation

The condition that every heavy point belongs to `A` is a family of closed
lower bounds on the cutoff, one for each point outside `A`. The excess is a
continuous finite sum. Thus the admissible cutoffs form a closed subset of
`[0, 1]`, and a nonempty such set has a greatest element.

This existence argument does not use positivity or normalization of the
weights, or sign assumptions on the parameters `m` and `d`.
-/


-- @@ L19-19 verbatim
namespace TalagrandThreshold.Selector


-- @@ L21-21 verbatim
open scoped BigOperators


-- @@ L23-23 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L25-31 verbatim
/-- Finite truncation gives a continuous excess as the cutoff varies. -/
theorem continuous_truncatedExcess (w : α → ℝ) (A : Finset α) (d : ℝ) :
    Continuous (fun u => truncatedExcess w A d u) := by
  unfold truncatedExcess
  apply continuous_finsetSum
  intro x _
  exact (continuous_const.min continuous_id).mul continuous_const


-- @@ L33-56 verbatim
/-- The heavy-point inclusion and the excess test are closed conditions. -/
theorem isClosed_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ) :
    IsClosed {u : ℝ | Admissible w A m d u} := by
  have hlarge : IsClosed {u : ℝ | ∀ x, x ∉ A → w x ≤ u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_le continuous_const continuous_id
  have hexcess : IsClosed {u : ℝ | m * u ≤ truncatedExcess w A d u} :=
    isClosed_le (continuous_const.mul continuous_id)
      (continuous_truncatedExcess w A d)
  have hrepr : {u : ℝ | Admissible w A m d u} =
      (Set.Icc 0 1 ∩ {u : ℝ | ∀ x, x ∉ A → w x ≤ u}) ∩
        {u : ℝ | m * u ≤ truncatedExcess w A d u} := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨⟨hu.1, hu.2.1⟩, fun _ hx => hu.outside_le hx⟩, hu.2.2.2⟩
    · intro hu
      refine ⟨hu.1.1.1, hu.1.1.2, ?_, hu.2⟩
      intro x hux
      by_contra hx
      exact (not_lt_of_ge (hu.1.2 x hx)) hux
  rw [hrepr]
  exact (isClosed_Icc.inter hlarge).inter hexcess


-- @@ L58-64 verbatim
/-- Admissible cutoffs are compact because they are closed and lie in `[0, 1]`. -/
theorem isCompact_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ) :
    IsCompact {u : ℝ | Admissible w A m d u} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).of_isClosed_subset
    (isClosed_admissible w A m d)
  intro u hu
  exact ⟨hu.1, hu.2.1⟩


-- @@ L66-71 verbatim
/-- Every nonempty admissible set has an actual greatest cutoff. -/
theorem exists_greatest_admissible (w : α → ℝ) (A : Finset α) (m d : ℝ)
    (hne : ∃ u, Admissible w A m d u) :
    ∃ ε, Admissible w A m d ε ∧ ∀ u, Admissible w A m d u → u ≤ ε := by
  obtain ⟨ε, hε⟩ := (isCompact_admissible w A m d).exists_isGreatest hne
  exact ⟨ε, hε.1, fun _ hu => hε.2 hu⟩


-- @@ L73-73 verbatim
end TalagrandThreshold.Selector


-- @@ L75-75 verbatim
end OAI
