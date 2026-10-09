import OAI.Combinatorics.CliqueFree.OptimizerBounds
import OAI.Combinatorics.CliqueFree.MultiplierLaw


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


-- @@ L19-21 verbatim
noncomputable def closedNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact insert v (neighbors G v)


-- @@ L23-26 verbatim
@[simp] lemma mem_closedNeighbors (G : SimpleGraph V) (u v : V) :
    u ∈ closedNeighbors G v ↔ u = v ∨ G.Adj v u := by
  classical
  simp [closedNeighbors]


-- @@ L28-31 verbatim
lemma mass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    mass w (closedNeighbors G v) = w v + neighborMass G w v := by
  classical
  exact sum_insert (by simp) -- the two expressions are definitionally the sums


-- @@ L33-60 verbatim
lemma edgeMass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    edgeMass G (restrict (closedNeighbors G v) w) =
      w v * neighborMass G w v + triangleAt G w v / 2 := by
  classical
  have hv : v ∉ neighbors G v := by simp
  have hs : (∑ u ∈ neighbors G v, if G.Adj v u then w v * w u else 0) =
      w v * neighborMass G w v := by
    rw [neighborMass, mass, mul_sum]
    apply sum_congr rfl
    intro u hu
    simp [(mem_neighbors G v u).1 hu]
  have hs' : (∑ u ∈ neighbors G v, if G.Adj u v then w u * w v else 0) =
      w v * neighborMass G w v := by
    simp_rw [G.adj_comm, mul_comm]
    exact hs
  have ht : crossMass G w (neighbors G v) (neighbors G v) = triangleAt G w v := by
    simpa [triangleAt, commonMass, inter_comm] using crossMass_neighbors G w (neighbors G v) v
  rw [edgeMass_restrict]
  have he : crossMass G w (closedNeighbors G v) (closedNeighbors G v) =
      2 * (w v * neighborMass G w v) + triangleAt G w v := by
    simp only [closedNeighbors, crossMass, sum_insert hv, G.irrefl, ite_false, zero_add,
      sum_add_distrib]
    rw [hs,hs']
    change _ + (_ + crossMass G w (neighbors G v) (neighbors G v)) = _
    rw [ht]
    ring
  rw [he]
  ring


-- @@ L62-89 verbatim
lemma optimizer_deletion_cost {G : SimpleGraph V} {w : V → ℝ}
    (hw : IsOptimizer G w) (A : Finset V) :
    potential G w - potential G (restrict Aᶜ w) =
      mass w A + edgeMass G (restrict A w) := by
  classical
  have hq : ∀ v, 0 ≤ restrict Aᶜ w v := by
    intro v
    simp only [restrict]
    split_ifs
    · exact hw.1 v
    · rfl
  rw [(optimizer_divergence hw _ hq).2]
  have hsum : (∑ v, (restrict Aᶜ w v * Real.log (restrict Aᶜ w v / w v) -
      restrict Aᶜ w v + w v)) = mass w A := by
    calc
      _ = ∑ v, if v ∈ A then w v else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases hv : v ∈ A
        · simp [restrict,hv]
        · simp [restrict,hv, (optimizer_stationary hw v).1.ne']
      _ = mass w A := by simp [mass]
  have hdiff : restrict Aᶜ w - w = (-1 : ℝ) • restrict A w := by
    ext v
    by_cases hv : v ∈ A <;> simp [restrict,hv]
  rw [hsum, hdiff]
  have he := edgeMass_smul G (restrict A w) (-1)
  simpa only [Pi.smul_def,smul_eq_mul,neg_one_sq,one_mul] using congrArg (mass w A + ·) he


-- @@ L91-112 verbatim
lemma potential_induce (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    potential (G.induce (A : Set V)) (fun v ↦ w v) = potential G (restrict A w) := by
  classical
  have he : edgeMass (G.induce (A : Set V)) (fun v ↦ w v) = edgeMass G (restrict A w) := by
    rw [edgeMass_restrict,edgeMass,crossMass]
    congr 1
    simp only [SimpleGraph.induce_adj]
    rw [← Finset.sum_subtype A (by simp)
      (fun u ↦ ∑ v : (A : Set V), if G.Adj u v then w u * w v else 0)]
    unfold crossMass
    apply sum_congr rfl
    intro u hu
    exact (Finset.sum_subtype A (by simp)
      (fun v ↦ if G.Adj u v then w u * w v else 0)).symm
  rw [potential, potential, he]
  congr 1
  rw [← Finset.sum_subtype A (by simp) (fun v ↦ vertexPotential (w v))]
  have hvertex (v : V) : vertexPotential (restrict A w v) =
      if v ∈ A then vertexPotential (w v) else 0 := by
    by_cases hv : v ∈ A <;> simp [restrict,hv,vertexPotential]
  simp_rw [hvertex]
  simp


-- @@ L114-114 verbatim
end CliqueFreeIndependence.WeightedGraph


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end OAI
