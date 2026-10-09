import OAI.Combinatorics.SecondNeighborhood.Reduction
import OAI.Combinatorics.SecondNeighborhood.Pruning
import OAI.Combinatorics.SecondNeighborhood.ExtremalContradiction


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SeymourSecondNeighborhood


-- @@ L9-9 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]


-- @@ L11-18 verbatim
theorem exists_goodVertex (r : V → V → Prop) (hr : IsOriented r) :
    ∃ v, GoodVertex r v := by
  classical
  by_contra h
  have hcounter : Counterexample r := (counterexample_iff_not_conjecture r).mpr h
  obtain ⟨n, hn, g, hg, hpos, hgrowth⟩ := counterexample_reduction hr hcounter
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Extremal.no_strictSubsetGrowth_of_pruning hg hpos (Pruning.pruning g) hgrowth


-- @@ L20-20 verbatim
end SeymourSecondNeighborhood


-- @@ L22-22 verbatim
end OAI
