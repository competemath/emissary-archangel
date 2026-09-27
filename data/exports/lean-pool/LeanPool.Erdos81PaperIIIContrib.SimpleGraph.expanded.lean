/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import LeanPool.Erdos81PaperIIIContrib.SumZeroTriangles
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-23 verbatim
/-!
# Simple graph interface for the sum-zero triangle packing

This file translates the finite edge-set formulation of the sum-zero construction into Mathlib's
`SimpleGraph` API. It leaves the constructive implementation in `SumZeroTriangles.lean` while
providing graph-valued triangles, their union, and a complete-graph corollary stated using graph
disjointness and degree.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open Finset


-- @@ L29-29 verbatim
namespace SumZeroTriangles


-- @@ L31-31 verbatim
variable {V : Type*} [DecidableEq V]


-- @@ L33-35 verbatim
/-- The simple graph consisting of the edges spanned by the vertices in `t`. -/
def triangleGraph (t : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet t.innerEdges


-- @@ L37-39 verbatim
/-- The simple graph consisting of all edges covered by the triples in `P`. -/
def packingGraph (P : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (familyEdges P)


-- @@ L41-43 verbatim
instance instDecidableAdjTriangleGraph (t : Finset V) : DecidableRel (triangleGraph t).Adj := by
  unfold triangleGraph
  infer_instance


-- @@ L45-48 verbatim
instance instDecidableAdjPackingGraph (P : Finset (Finset V)) :
    DecidableRel (packingGraph P).Adj := by
  unfold packingGraph
  infer_instance


-- @@ L50-52 verbatim
instance instFintypeEdgeSetTriangleGraph (t : Finset V) : Fintype (triangleGraph t).edgeSet := by
  unfold triangleGraph
  infer_instance


-- @@ L54-57 verbatim
instance instFintypeEdgeSetPackingGraph (P : Finset (Finset V)) :
    Fintype (packingGraph P).edgeSet := by
  unfold packingGraph
  infer_instance


-- @@ L59-63 verbatim
private lemma innerEdges_disjoint_diagSet (t : Finset V) :
    Disjoint (t.innerEdges : Set (Sym2 V)) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e he hdiag
  exact (Finset.mem_innerEdges.1 he).2 hdiag


-- @@ L65-70 verbatim
private lemma familyEdges_disjoint_diagSet (P : Finset (Finset V)) :
    Disjoint (familyEdges P : Set (Sym2 V)) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e he hdiag
  obtain ⟨t, -, het⟩ := Finset.mem_familyEdges.1 he
  exact (Finset.mem_innerEdges.1 het).2 hdiag


-- @@ L72-76 verbatim
@[simp]
lemma edgeSet_triangleGraph (t : Finset V) :
    (triangleGraph t).edgeSet = t.innerEdges := by
  rw [triangleGraph, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
  exact innerEdges_disjoint_diagSet t


-- @@ L78-82 verbatim
@[simp]
lemma edgeSet_packingGraph (P : Finset (Finset V)) :
    (packingGraph P).edgeSet = familyEdges P := by
  rw [packingGraph, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
  exact familyEdges_disjoint_diagSet P


-- @@ L84-88 verbatim
@[simp]
lemma edgeFinset_triangleGraph (t : Finset V) :
    (triangleGraph t).edgeFinset = t.innerEdges := by
  ext e
  simp


-- @@ L90-94 verbatim
@[simp]
lemma edgeFinset_packingGraph (P : Finset (Finset V)) :
    (packingGraph P).edgeFinset = familyEdges P := by
  ext e
  simp


-- @@ L96-119 verbatim
/-- Every finite complete graph has a packing by edge-disjoint triangles whose uncovered graph has
maximum degree at most three. -/
theorem exists_simpleGraph_triangle_packing [Fintype V] :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, (⊤ : SimpleGraph V).IsNClique 3 t) ∧
      (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (triangleGraph t) (triangleGraph t')) ∧
      (∀ v : V, ((⊤ : SimpleGraph V) \ packingGraph P).degree v ≤ 3) := by
  classical
  obtain ⟨P, hcard, -, hdisjoint, hdegree⟩ :=
    exists_triangle_packing_clique (Finset.univ : Finset V)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨by simp, hcard t ht⟩
  · intro t ht t' ht' hne
    rw [← SimpleGraph.disjoint_edgeSet, edgeSet_triangleGraph, edgeSet_triangleGraph]
    exact Finset.disjoint_coe.mpr (hdisjoint t ht t' ht' hne)
  · intro v
    have htop : (⊤ : SimpleGraph V).edgeFinset = (Finset.univ : Finset V).innerEdges := by
      ext e
      simp [Finset.mem_innerEdges]
    rw [← SimpleGraph.card_incidenceFinset_eq_degree,
      SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.edgeFinset_sdiff,
      htop, edgeFinset_packingGraph]
    simpa [Finset.edgeDegree] using hdegree v


-- @@ L121-121 verbatim
end SumZeroTriangles
