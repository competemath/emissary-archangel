import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SeymourSecondNeighborhood.Extremal


-- @@ L9-9 verbatim
open Pruning


-- @@ L11-11 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-16 verbatim
def uncoveredCount (r : V → V → Prop) (P Q : Finset (V × V)) : ℕ :=
  (Finset.univ \ (leftImage r P ∪ rightImage r Q)).card


-- @@ L18-19 verbatim
def objective (r : V → V → Prop) (P Q : Finset (V × V)) : ℕ :=
  P.card + Q.card + uncoveredCount r P Q


-- @@ L21-29 verbatim
theorem uncoveredCount_add_images {r : V → V → Prop} {P Q : Finset (V × V)}
    (h : ConflictFree r P Q) :
    uncoveredCount r P Q + (leftImage r P).card + (rightImage r Q).card =
      (Finset.univ : Finset (V × V)).card := by
  classical
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (leftImage r P ∪ rightImage r Q))
  rw [Finset.card_union_of_disjoint (conflictFree_iff_disjoint.mp h)] at hc
  simpa only [uncoveredCount, Nat.add_assoc] using hc


-- @@ L31-38 verbatim
theorem uncoveredZ_card_le (r : V → V → Prop) (R C P Q : Finset (V × V)) :
    (uncoveredZ r R C P Q).card ≤ uncoveredCount r P Q := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨_, hn⟩ := mem_uncoveredZ.mp hz
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, fun h =>
    hn (Finset.mem_union.mp h)⟩


-- @@ L40-51 verbatim
theorem objective_lt_of_pruning {r : V → V → Prop}
    {P Q R C P' Q' : Finset (V × V)}
    (hpr : PruningResult r R C P' Q')
    (hH : (H r R C).card ≤ uncoveredCount r P Q)
    (hgain : P.card + Q.card + 2 * uncoveredCount r P Q < R.card + C.card) :
    objective r P Q < objective r P' Q' := by
  have hZ := uncoveredZ_card_le r R C P' Q'
  have hR := Finset.card_sdiff_add_card_eq_card hpr.subset_left
  have hC := Finset.card_sdiff_add_card_eq_card hpr.subset_right
  have hdel := hpr.deletion_bound
  unfold objective
  omega


-- @@ L53-68 verbatim
theorem exists_maximizing_pair (r : V → V → Prop)
    (admissible : Finset (V × V) → Finset (V × V) → Prop)
    (hex : ∃ P Q, admissible P Q) :
    ∃ P Q, admissible P Q ∧ ∀ P' Q', admissible P' Q' →
      objective r P' Q' ≤ objective r P Q := by
  classical
  let candidates : Finset (Finset (V × V) × Finset (V × V)) :=
    Finset.univ.filter fun p => admissible p.1 p.2
  have hne : candidates.Nonempty := by
    obtain ⟨P, Q, h⟩ := hex
    exact ⟨(P, Q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  obtain ⟨p, hp, hmax⟩ := candidates.exists_max_image
    (fun p => objective r p.1 p.2) hne
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  intro P Q h
  exact hmax (P, Q) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end SeymourSecondNeighborhood.Extremal


-- @@ L74-74 verbatim
end OAI
