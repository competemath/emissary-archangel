import OAI.Combinatorics.SecondNeighborhood.AugmentedRankBound
import OAI.Combinatorics.SecondNeighborhood.CoverPruning


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SeymourSecondNeighborhood.Pruning


-- @@ L8-8 verbatim
variable {X : Type*} [Fintype X] [DecidableEq X]


-- @@ L10-15 verbatim
theorem pruning (r : X → X → Prop) : PruningStatement r := by
  intro R C
  obtain ⟨M, hM, hα, hβ⟩ := exists_augmented_maximum_matching r R C
  apply exists_pruning_of_augmented_matching_bound r R C M hM
  simpa only [Nat.add_comm] using
    augmented_matching_card_le_corners r R C M hM.1 hα hβ


-- @@ L17-17 verbatim
end SeymourSecondNeighborhood.Pruning


-- @@ L19-19 verbatim
end OAI
