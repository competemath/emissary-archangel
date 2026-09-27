/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import LeanPool.Sabidussi.Color
public import LeanPool.Sabidussi.Statement
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-22 verbatim
/-!
# Finite endpoint multigraphs with loops

Edges are labelled objects with two numbered half-edges.  The endpoints may coincide, so loops
are represented without quotienting or special cases.  Degree and parity always count half-edge
incidences; consequently a loop contributes two incidences at its vertex.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Sabidussi


-- @@ L28-28 verbatim
open scoped BigOperators


-- @@ L30-30 verbatim
namespace LoopMultigraph


-- @@ L32-32 verbatim
variable {V E : Type*} [Fintype V] [Fintype E]


-- @@ L34-34 verbatim
namespace EulerTour


-- @@ L36-36 verbatim
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)


-- @@ L38-39 verbatim
/-- The vertex of the transition from the previous edge into edge `i`. -/
def vertexAt (i : T.Pos) : V := G.endAt (T.edge i) (T.depart i)


-- @@ L41-42 verbatim
/-- The vertex at which edge `i` arrives. -/
def arrivalAt (i : T.Pos) : V := G.endAt (T.edge i) (Fin.rev (T.depart i))


-- @@ L44-47 verbatim
omit [DecidableEq V] in
@[simp]
theorem next_prev (i : T.Pos) : T.next (T.prev i) = i := by
  simp [next, prev]


-- @@ L49-52 verbatim
omit [DecidableEq V] in
@[simp]
theorem prev_next (i : T.Pos) : T.prev (T.next i) = i := by
  simp [next, prev]


-- @@ L54-56 verbatim
omit [DecidableEq V] in
theorem arrival_eq_vertexAt_next (i : T.Pos) : T.arrivalAt i = T.vertexAt (T.next i) := by
  exact T.continuous i


-- @@ L58-60 verbatim
omit [DecidableEq V] in
theorem arrival_prev_eq_vertexAt (i : T.Pos) : T.arrivalAt (T.prev i) = T.vertexAt i := by
  simpa [arrivalAt, vertexAt, next, prev] using T.continuous (T.prev i)


-- @@ L62-63 verbatim
/-- Occurrences of `v` in the cyclic transition word. -/
abbrev Occurrence (v : V) := {i : T.Pos // T.vertexAt i = v}


-- @@ L65-66 verbatim
instance (v : V) : Fintype (T.Occurrence v) :=
  Subtype.fintype fun i : T.Pos ↦ T.vertexAt i = v


-- @@ L68-75 verbatim
/-- The two edge ends paired at an occurrence of a transition vertex.

Side `0` is the departing end of the current edge; side `1` is the arriving end of the previous
edge.  The two numbered half-edges remain distinct even when the underlying edge is a loop.
-/
def transitionHalfEdge {v : V} (o : T.Occurrence v) : Fin 2 → HalfEdge E
  | 0 => (T.edge o.1, T.depart o.1)
  | 1 => (T.edge (T.prev o.1), Fin.rev (T.depart (T.prev o.1)))


-- @@ L77-84 verbatim
omit [DecidableEq V] in
@[simp]
theorem vertex_transitionHalfEdge {v : V} (o : T.Occurrence v) (s : Fin 2) :
    G.vertex (T.transitionHalfEdge o s) = v := by
  fin_cases s
  · exact o.2
  · change T.arrivalAt (T.prev o.1) = v
    exact (T.arrival_prev_eq_vertexAt o.1).trans o.2


-- @@ L86-88 verbatim
/-- A transition occurrence with a chosen side, mapped to the corresponding incident half-edge. -/
def occurrenceSideToHalfEdge (v : V) : T.Occurrence v × Fin 2 → G.halfEdgesAt v :=
  fun os ↦ ⟨T.transitionHalfEdge os.1 os.2, T.vertex_transitionHalfEdge os.1 os.2⟩


-- @@ L90-93 verbatim
/-- The underlying map from a position and transition side to an edge end. -/
def positionSideToHalfEdge : T.Pos × Fin 2 → HalfEdge E
  | (i, 0) => (T.edge i, T.depart i)
  | (i, 1) => (T.edge (T.prev i), Fin.rev (T.depart (T.prev i)))


-- @@ L95-99 verbatim
/-- The inverse map: a departure end belongs to its own position, and an arrival end belongs to
side `1` of the next position. -/
def halfEdgeToPositionSide (h : HalfEdge E) : T.Pos × Fin 2 :=
  let i := T.edge.symm h.1
  if h.2 = T.depart i then (i, 0) else (T.next i, 1)


-- @@ L101-102 verbatim
private theorem rev_ne_self_fin_two (i : Fin 2) : Fin.rev i ≠ i := by
  fin_cases i <;> decide


-- @@ L104-105 verbatim
private theorem eq_rev_of_ne_fin_two {i j : Fin 2} (h : i ≠ j) : i = Fin.rev j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]


-- @@ L107-114 verbatim
omit [DecidableEq V] in
theorem halfEdgeToPositionSide_positionSideToHalfEdge (p : T.Pos × Fin 2) :
    T.halfEdgeToPositionSide (T.positionSideToHalfEdge p) = p := by
  rcases p with ⟨i, s⟩
  fin_cases s
  · simp [positionSideToHalfEdge, halfEdgeToPositionSide]
  · simp [positionSideToHalfEdge, halfEdgeToPositionSide, rev_ne_self_fin_two,
      T.next_prev]


-- @@ L116-128 verbatim
omit [DecidableEq V] in
theorem positionSideToHalfEdge_halfEdgeToPositionSide (h : HalfEdge E) :
    T.positionSideToHalfEdge (T.halfEdgeToPositionSide h) = h := by
  rcases h with ⟨e, j⟩
  let i : T.Pos := T.edge.symm e
  by_cases hj : j = T.depart i
  · subst j
    simp [halfEdgeToPositionSide, positionSideToHalfEdge, i]
  · have hrev : j = Fin.rev (T.depart i) := by
      exact eq_rev_of_ne_fin_two hj
    subst j
    simp [halfEdgeToPositionSide, positionSideToHalfEdge, i, rev_ne_self_fin_two,
      T.prev_next]


-- @@ L130-135 verbatim
/-- Edge positions with a choice of transition side are exactly all edge ends. -/
def positionSideEquivHalfEdge : T.Pos × Fin 2 ≃ HalfEdge E where
  toFun := T.positionSideToHalfEdge
  invFun := T.halfEdgeToPositionSide
  left_inv := T.halfEdgeToPositionSide_positionSideToHalfEdge
  right_inv := T.positionSideToHalfEdge_halfEdgeToPositionSide


-- @@ L137-144 verbatim
omit [DecidableEq V] in
theorem vertex_positionSideToHalfEdge (p : T.Pos × Fin 2) :
    G.vertex (T.positionSideToHalfEdge p) = T.vertexAt p.1 := by
  rcases p with ⟨i, s⟩
  fin_cases s
  · rfl
  · change T.arrivalAt (T.prev i) = T.vertexAt i
    exact T.arrival_prev_eq_vertexAt i


-- @@ L146-151 verbatim
/-- The two sides of all occurrences of `v` are exactly the half-edges incident with `v`. -/
def occurrenceSideEquivHalfEdgesAt (v : V) : T.Occurrence v × Fin 2 ≃ G.halfEdgesAt v :=
  (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun i : T.Pos ↦ T.vertexAt i = v)).symm |>.trans
    (T.positionSideEquivHalfEdge.subtypeEquiv fun p ↦ by
      change T.vertexAt p.1 = v ↔ G.vertex (T.positionSideToHalfEdge p) = v
      rw [T.vertex_positionSideToHalfEdge p])


-- @@ L153-157 verbatim
/-- The degree at `v` is twice its number of occurrences in the transition word. -/
theorem degree_eq_two_mul_card_occurrence (v : V) :
    G.degree v = 2 * Fintype.card (T.Occurrence v) := by
  rw [degree, ← Fintype.card_congr (T.occurrenceSideEquivHalfEdgesAt v), Fintype.card_prod]
  simp [Nat.mul_comm]


-- @@ L159-159 verbatim
end EulerTour


-- @@ L161-162 verbatim
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)


-- @@ L164-167 verbatim
/-- The incidence indicator of an edge at a vertex, with both edge ends counted. -/
def edgeIncidence (v : V) (e : E) : F₂ :=
  (if G.endAt e 0 = v then 1 else 0) +
    (if G.endAt e 1 = v then 1 else 0)


-- @@ L169-171 verbatim
/-- An edge set is even when every vertex has even degree in the induced multigraph. -/
def IsEvenEdgeSet (F : Finset E) : Prop :=
  ∀ v : V, ∑ e ∈ F, G.edgeIncidence v e = 0


-- @@ L173-184 verbatim
/-- A (multigraph) cycle is a nonempty inclusion-minimal even edge set.

This includes singleton loops and pairs of parallel non-loop edges. -/
structure Cycle where
  /-- The edges of the cycle. -/
  edges : Finset E
  /-- A cycle is nonempty. -/
  nonempty : edges.Nonempty
  /-- Every vertex has even degree in the cycle. -/
  even : G.IsEvenEdgeSet edges
  /-- The edge set is inclusion-minimal among nonempty even edge sets. -/
  minimal : ∀ D : Finset E, D.Nonempty → D ⊆ edges → G.IsEvenEdgeSet D → D = edges


-- @@ L186-195 verbatim
omit [DecidableEq E] in
/-- Both incidences of a loop cancel in characteristic two. -/
theorem singleton_loop_even (e : E) (hloop : G.endAt e 0 = G.endAt e 1) :
    G.IsEvenEdgeSet {e} := by
  intro v
  simp only [Finset.sum_singleton]
  change (if G.endAt e 0 = v then 1 else 0) +
      (if G.endAt e 1 = v then 1 else 0) = 0
  rw [← hloop]
  exact CharTwo.add_self_eq_zero _


-- @@ L197-204 verbatim
/-- A loop is a one-edge circuit in the minimal-even-set definition. -/
def loopCycle (e : E) (hloop : G.endAt e 0 = G.endAt e 1) : G.Cycle where
  edges := {e}
  nonempty := ⟨e, by simp⟩
  even := G.singleton_loop_even e hloop
  minimal := by
    intro D hDne hDsub _
    exact hDne.subset_singleton_iff.mp hDsub


-- @@ L206-212 verbatim
private theorem even_sdiff {F D : Finset E} (hDF : D ⊆ F)
    (hF : G.IsEvenEdgeSet F) (hD : G.IsEvenEdgeSet D) :
    G.IsEvenEdgeSet (F \ D) := by
  intro v
  have hsplit := Finset.sum_sdiff hDF (f := fun e ↦ G.edgeIncidence v e)
  rw [hD v, hF v] at hsplit
  simpa using hsplit


-- @@ L214-255 verbatim
/-- Every finite even edge set is an edge-disjoint union of multigraph cycles.  The displayed
equation records edge multiplicities and is stronger than mere equality of unions. -/
theorem decompose_even_edge_set (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by
  classical
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · by_cases hmin :
      (∀ D : Finset E, D.Nonempty → D ⊆ F → G.IsEvenEdgeSet D → D = F)
    · let C : G.Cycle :=
        { edges := F
          nonempty := hne
          even := hF
          minimal := hmin }
      refine ⟨[C], ?_⟩
      intro e
      by_cases he : e ∈ F <;> simp [C, he]
    · push Not at hmin
      obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
      have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
      have hRssub : F \ D ⊂ F := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨e, heD⟩ := hDne
        have : e ∈ F \ D := by simpa [heq] using hDF heD
        simp [heD] at this
      obtain ⟨LD, hLD⟩ := ih D hDssub hDeven
      obtain ⟨LR, hLR⟩ := ih (F \ D) hRssub (G.even_sdiff hDF hF hDeven)
      refine ⟨LD ++ LR, ?_⟩
      intro e
      rw [List.filter_append, List.length_append, hLD e, hLR e]
      by_cases heD : e ∈ D
      · have heF : e ∈ F := hDF heD
        simp [heD, heF]
      · by_cases heF : e ∈ F <;> simp [heD, heF]
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    exact ⟨[], by simp⟩


-- @@ L257-257 verbatim
open Sabidussi


-- @@ L259-260 verbatim
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)


-- @@ L262-267 verbatim
/-- A partition of all edge objects into circuits. -/
structure CircuitDecomposition where
  /-- The list of circuits partitioning the edges. -/
  circuits : List G.Cycle
  /-- Every edge object lies in exactly one circuit. -/
  coveredOnce : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 1


-- @@ L269-274 verbatim
/-- A circuit decomposition is compatible with an Euler tour when no one circuit contains both
edge objects of a transition. -/
def CircuitDecomposition.Compatible {G : LoopMultigraph V E}
    (S : G.CircuitDecomposition) (T : G.EulerTour) : Prop :=
  ∀ (i : T.Pos) (C : G.Cycle), C ∈ S.circuits →
    ¬ (T.edge (T.prev i) ∈ C.edges ∧ T.edge i ∈ C.edges)


-- @@ L276-284 verbatim
/-- The four-colour certificate produced by the cyclic-word part of the proof. -/
structure CompatibleFourColoring (T : G.EulerTour) where
  /-- The colour assigned to each edge object. -/
  color : E → Color
  /-- Consecutive edges of the tour receive different colours. -/
  transition_ne : ∀ i : T.Pos, color (T.edge (T.prev i)) ≠ color (T.edge i)
  /-- Each colour class is an even edge set. -/
  color_even : ∀ z : Color,
    G.IsEvenEdgeSet (Finset.univ.filter fun e ↦ color e = z)


-- @@ L286-286 verbatim
namespace CompatibleFourColoring


-- @@ L288-294 verbatim
private theorem filter_flatMap_length {A B : Type*} (p : B → Bool)
    (f : A → List B) (xs : List A) :
    ((xs.flatMap f).filter p).length =
      (xs.map fun x ↦ ((f x).filter p).length).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]


-- @@ L296-340 verbatim
/-- Every compatible four-colouring yields a compatible circuit decomposition. -/
theorem exists_compatible_circuit_decomposition
    {T : G.EulerTour} (K : G.CompatibleFourColoring T) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by
  classical
  let support : Color → Finset E := fun z ↦ Finset.univ.filter fun e ↦ K.color e = z
  have hex : ∀ z : Color, ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length =
        if e ∈ support z then 1 else 0 := by
    intro z
    exact G.decompose_even_edge_set (support z) (K.color_even z)
  choose pieces hpieces using hex
  have hpiece_subset : ∀ (z : Color) (C : G.Cycle), C ∈ pieces z → C.edges ⊆ support z := by
    intro z C hC e he
    by_contra hnot
    have hzero : ((pieces z).filter fun D ↦ e ∈ D.edges).length = 0 := by
      simpa [hnot] using hpieces z e
    have hmem : C ∈ (pieces z).filter fun D ↦ e ∈ D.edges := by
      simpa using ⟨hC, he⟩
    have hpos : 0 < ((pieces z).filter fun D ↦ e ∈ D.edges).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
    omega
  let allPieces : List G.Cycle := Finset.univ.toList.flatMap pieces
  have hcovered : ∀ e : E,
      (allPieces.filter fun C ↦ e ∈ C.edges).length = 1 := by
    intro e
    change ((Finset.univ.toList.flatMap pieces).filter fun C ↦ e ∈ C.edges).length = 1
    rw [filter_flatMap_length]
    simp_rw [hpieces]
    simp [support]
  let S : G.CircuitDecomposition :=
    { circuits := allPieces
      coveredOnce := hcovered }
  refine ⟨S, ?_⟩
  intro i C hC htransition
  change C ∈ Finset.univ.toList.flatMap pieces at hC
  rw [List.mem_flatMap] at hC
  obtain ⟨z, hz, hCz⟩ := hC
  have hprevSupport := hpiece_subset z C hCz htransition.1
  have hcurrSupport := hpiece_subset z C hCz htransition.2
  have hprevColor : K.color (T.edge (T.prev i)) = z := by
    simpa [support] using hprevSupport
  have hcurrColor : K.color (T.edge i) = z := by
    simpa [support] using hcurrSupport
  exact K.transition_ne i (hprevColor.trans hcurrColor.symm)


-- @@ L342-342 verbatim
end CompatibleFourColoring


-- @@ L344-344 verbatim
end LoopMultigraph

-- @@ L345-345 verbatim
end Sabidussi
