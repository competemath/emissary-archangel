import OAI.Combinatorics.CliqueFree.WalkEntropy
import OAI.Combinatorics.CliqueFree.TriangleState


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Finset


-- @@ L11-11 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L13-13 verbatim
namespace CliqueFreeIndependence.WeightedGraph


-- @@ L15-15 verbatim
universe u v


-- @@ L17-17 verbatim
variable {V : Type u} [Fintype V]


-- @@ L19-19 verbatim
attribute [local instance 10000] edgeStateDecEq


-- @@ L21-21 verbatim
namespace LocalWalk

-- @@ L22-22 verbatim
open FiniteEntropy FiniteKernel

-- @@ L23-23 verbatim
variable {G : SimpleGraph V} {w : V → ℝ}

-- @@ L24-43 verbatim
lemma triangle_pair_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12 t.edge13) =
      normalizer G w * ∑ e, law G w e * ∑ z, transition G w e z * f e z := by
  rw [TriangleState.corner_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  have he := (hc _ _ e.adj).ne'
  have hZ := (normalizer_pos hw hc).ne'
  by_cases hs : e.src = z.src
  · by_cases ha : G.Adj e.dst z.dst
    · simp only [hs, ha, true_and, ↓reduceIte, transition, law]
      rw [hs] at he
      field_simp
    · simp [hs, ha, transition]
  · simp [hs, transition]


-- @@ L45-50 verbatim
lemma triangle_edge_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) (f : EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12) =
      normalizer G w * ∑ e, law G w e * f e := by
  rw [triangle_pair_sum hw hc (fun e _ ↦ f e)]
  simp only [← sum_mul, (transition_stochastic hw hc _).2, one_mul]

-- @@ L51-51 verbatim
end LocalWalk


-- @@ L53-53 verbatim
end CliqueFreeIndependence.WeightedGraph


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end OAI
