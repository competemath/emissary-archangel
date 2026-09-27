/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.ChannelCapacity.NonDegeneracy
import LeanPool.ChannelCapacity.StrictConcavity


-- @@ L11-15 verbatim
/-!
# ChannelCapacity.Capacity

Capacity and generic existence/uniqueness packaging for maximizing mutual information.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open MeasureTheory

-- @@ L20-20 verbatim
open ProbabilityTheory


-- @@ L22-22 verbatim
namespace ChannelCapacity


-- @@ L24-24 verbatim
open ProbabilityMeasure


-- @@ L26-26 verbatim
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]


-- @@ L28-30 verbatim
/-- Shannon channel capacity as the supremum over all priors. -/
noncomputable def channelCapacity (k : Kernel α β) [IsMarkovKernel k] : ℝ :=
  sSup (Set.range fun p : ProbabilityMeasure α => mutualInformation p k)


-- @@ L32-35 verbatim
/-- A prior achieves capacity if it attains the supremum. -/
def IsCapacityAchievingPrior (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : Prop :=
  mutualInformation p k = channelCapacity k


-- @@ L37-54 verbatim
lemma channelCapacity_eq_of_isMaxOn_univ (k : Kernel α β) [IsMarkovKernel k]
    {p : ProbabilityMeasure α}
    (hp : IsMaxOn (fun q => mutualInformation q k) Set.univ p) :
    channelCapacity k = mutualInformation p k := by
  let s : Set ℝ := Set.range fun q : ProbabilityMeasure α => mutualInformation q k
  have hp' : ∀ q : ProbabilityMeasure α, mutualInformation q k ≤ mutualInformation p k :=
    isMaxOn_univ_iff.mp hp
  have hsNonempty : s.Nonempty := ⟨mutualInformation p k, ⟨p, rfl⟩⟩
  have hsBdd : BddAbove s := by
    refine ⟨mutualInformation p k, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hp' q
  apply le_antisymm
  · refine csSup_le hsNonempty ?_
    rintro _ ⟨q, rfl⟩
    exact hp' q
  · refine le_csSup hsBdd ?_
    exact ⟨p, rfl⟩


-- @@ L56-67 verbatim
lemma exists_isMaxOn_mutualInformation (k : Kernel α β) [IsMarkovKernel k]
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃ p : ProbabilityMeasure α,
      IsMaxOn (fun q => mutualInformation q k) Set.univ p := by
  rcases UpperSemicontinuousOn.exists_isMaxOn
      (f := fun p : ProbabilityMeasure α => mutualInformation p k)
      (s := (Set.univ : Set (ProbabilityMeasure α)))
      hNonempty hCompact (hUsc.upperSemicontinuousOn _) with ⟨p, _hp, hp⟩
  exact ⟨p, hp⟩


-- @@ L69-76 verbatim
theorem exists_capacity_achieving_prior (k : Kernel α β) [IsMarkovKernel k]
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃ p : ProbabilityMeasure α, IsCapacityAchievingPrior k p := by
  rcases exists_isMaxOn_mutualInformation k hNonempty hCompact hUsc with ⟨p, hp⟩
  exact ⟨p, (channelCapacity_eq_of_isMaxOn_univ k hp).symm⟩


-- @@ L78-101 verbatim
theorem exists_unique_capacity_achieving_prior
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k)
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  rcases exists_isMaxOn_mutualInformation k hNonempty hCompact hUsc with ⟨pMax, hpMax⟩
  refine ⟨pMax, (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm, ?_⟩
  intro p hp
  have hpMax' : ∀ q : ProbabilityMeasure α, mutualInformation q k ≤ mutualInformation pMax k :=
    isMaxOn_univ_iff.mp hpMax
  have hp' : IsMaxOn (fun q => mutualInformation q k) Set.univ p := by
    intro q _hq
    calc
      mutualInformation q k ≤ mutualInformation pMax k := hpMax' q
      _ = channelCapacity k := (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm
      _ = mutualInformation p k := hp.symm
  exact ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
    (Kernel.mutualInformation_strictlyConcave_of_injectivePriorPushforward k h hWC) hp' hpMax


-- @@ L103-103 verbatim
end ChannelCapacity
