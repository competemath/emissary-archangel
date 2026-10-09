import OAI.Analysis.LipschitzEquivalence.CompactReduction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators InnerProductSpace Topology ENNReal

-- @@ L7-7 verbatim
open scoped Topology ENNReal NNReal

-- @@ L8-8 verbatim
open scoped Classical ENNReal NNReal InnerProductSpace Topology

-- @@ L9-9 verbatim
open Filter Set

-- @@ L10-10 verbatim
open scoped NNReal Topology

-- @@ L11-11 verbatim
open Filter Set


-- @@ L13-13 verbatim
namespace LipschitzCounterexample.SeparatingStages

-- @@ L14-14 verbatim
open LocalGeometry LocalizedLinearization


-- @@ L16-28 verbatim
theorem D_localOrthogonality : LocalOrthogonality D := by
  intro I _ x hx
  obtain ⟨r,hr,l,S,hS,_,hD⟩ := D_local_orthogonality x hx
  refine ⟨r,hr,l,S,hS,fun i y hy => ?_⟩
  have he : CoordinateSpaces.tail l (D y) = HilbertSlots.tailCLM l (D y) := by
    apply lp.ext
    funext n
    apply PiLp.ext
    intro a
    rw [CoordinateSpaces.tail_coord,HilbertSlots.tailCLM_coord]
    split_ifs <;> rfl
  rw [he]
  exact hD i y hy


-- @@ L30-32 verbatim
theorem q_completelyContinuous : WeakSequences.CompletelyContinuous q :=
  completely_continuous_of_compact_reduction FreeSpace.hasCompactReduction D
    D_lipschitz D_zero D_localOrthogonality


-- @@ L34-37 verbatim
theorem main_of_free_wsc
    (hW : WeakSequences.WeakSequentiallyComplete (FreeSpace.Space M)) : MainClaim :=
  Criterion.assemble q h (fun x => q_point x) h_zero h_lipschitz h_symm_lipschitz q_norm hW
    q_completelyContinuous


-- @@ L39-39 verbatim
end LipschitzCounterexample.SeparatingStages


-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
