/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Fin.Rotate


-- @@ L11-17 verbatim
/-!
# Trusted statement layer for Sabidussi compatibility

This module contains only the public data and predicates occurring in the headline theorem. It is
the trusted import boundary for `leanprover/comparator`; proof modules build on it, but it does not
import them.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Sabidussi


-- @@ L23-26 verbatim
/-- A finite labelled endpoint multigraph. Parallel edges and loops are allowed. -/
structure LoopMultigraph (V E : Type*) [Fintype V] [Fintype E] where
  /-- The two numbered endpoints of each labelled edge. -/
  endAt : E → Fin 2 → V


-- @@ L28-28 verbatim
namespace LoopMultigraph


-- @@ L30-30 verbatim
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]


-- @@ L32-33 verbatim
/-- A labelled edge together with one of its two numbered ends. -/
abbrev HalfEdge (E : Type*) := E × Fin 2


-- @@ L35-36 verbatim
/-- The endpoint vertex of a half-edge. -/
def vertex (G : LoopMultigraph V E) (h : HalfEdge E) : V := G.endAt h.1 h.2


-- @@ L38-40 verbatim
/-- Half-edges incident with a vertex. A loop contributes both of its numbered ends. -/
def halfEdgesAt (G : LoopMultigraph V E) (v : V) :=
  {h : HalfEdge E // G.vertex h = v}


-- @@ L42-43 verbatim
instance (G : LoopMultigraph V E) (v : V) : Fintype (G.halfEdgesAt v) :=
  Subtype.fintype fun h : HalfEdge E ↦ G.vertex h = v


-- @@ L45-47 verbatim
/-- Degree counted in half-edge incidences. -/
def degree (G : LoopMultigraph V E) (v : V) : ℕ :=
  Fintype.card (G.halfEdgesAt v)


-- @@ L49-49 verbatim
variable {V E : Type*} [Fintype V] [Fintype E]


-- @@ L51-62 verbatim
/-- A nonempty closed Euler tour using every labelled edge exactly once. -/
structure EulerTour (G : LoopMultigraph V E) where
  /-- The edge positions are `Fin (n + 1)`. -/
  n : ℕ
  /-- Every edge object occurs at exactly one position. -/
  edge : Fin (n + 1) ≃ E
  /-- The end from which the edge at a position is traversed. -/
  depart : Fin (n + 1) → Fin 2
  /-- The arrival end at a position is the departure vertex at the next position. -/
  continuous : ∀ i,
    G.endAt (edge i) (Fin.rev (depart i)) =
      G.endAt (edge (finRotate (n + 1) i)) (depart (finRotate (n + 1) i))


-- @@ L64-64 verbatim
namespace EulerTour


-- @@ L66-66 verbatim
variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)


-- @@ L68-69 verbatim
/-- Positions in the cyclic edge word. -/
abbrev Pos := Fin (T.n + 1)


-- @@ L71-72 verbatim
/-- The next edge position. -/
def next (i : T.Pos) : T.Pos := finRotate (T.n + 1) i


-- @@ L74-75 verbatim
/-- The previous edge position. -/
def prev (i : T.Pos) : T.Pos := (finRotate (T.n + 1)).symm i


-- @@ L77-77 verbatim
end EulerTour


-- @@ L79-80 verbatim
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)


-- @@ L82-85 verbatim
/-- The ordinary natural-number degree of `v` in an edge set. Edge ends are counted, so this
definition also has the standard behavior for multigraphs. -/
def degreeIn (F : Finset E) (v : V) : ℕ :=
  ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ G.endAt h.1 h.2 = v).card


-- @@ L87-90 verbatim
/-- Two labelled edges meet if some numbered end of one has the same endpoint as some numbered
end of the other. An edge meets itself, and parallel edges meet at both endpoints. -/
def EdgeAdjacent (e f : E) : Prop :=
  ∃ i j : Fin 2, G.endAt e i = G.endAt f j


-- @@ L92-96 verbatim
/-- Edge-chain connectivity of a nonempty edge-supported subgraph. -/
def EdgeConnected (F : Finset E) : Prop :=
  ∃ root ∈ F, ∀ e ∈ F,
    Relation.ReflTransGen
      (fun x y : E ↦ x ∈ F ∧ y ∈ F ∧ G.EdgeAdjacent x y) root e


-- @@ L98-100 verbatim
/-- The vertices incident with at least one edge of `F`. -/
def edgeSupport (F : Finset E) : Finset V :=
  Finset.univ.filter fun v ↦ ∃ e ∈ F, ∃ i : Fin 2, G.endAt e i = v


-- @@ L102-112 verbatim
/-- An ordinary circuit: a nonempty connected edge-supported subgraph in which every supported
vertex has degree two. -/
structure OrdinaryCircuit where
  /-- The edges of the circuit. -/
  edges : Finset E
  /-- An ordinary circuit is nonempty. -/
  nonempty : edges.Nonempty
  /-- The circuit is edge-connected. -/
  connected : G.EdgeConnected edges
  /-- Every supported vertex has ordinary degree two. -/
  twoRegular : ∀ v : V, v ∈ G.edgeSupport edges → G.degreeIn edges v = 2


-- @@ L114-119 verbatim
/-- A partition of all labelled edges into ordinary connected 2-regular circuits. -/
structure OrdinaryCircuitDecomposition where
  /-- The list of ordinary circuits partitioning the edges. -/
  circuits : List G.OrdinaryCircuit
  /-- Every labelled edge lies in exactly one circuit. -/
  coveredOnce : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 1


-- @@ L121-125 verbatim
/-- Compatibility stated for ordinary circuits. -/
def OrdinaryCircuitDecomposition.Compatible {G : LoopMultigraph V E}
    (S : G.OrdinaryCircuitDecomposition) (T : G.EulerTour) : Prop :=
  ∀ (i : T.Pos) (C : G.OrdinaryCircuit), C ∈ S.circuits →
    ¬ (T.edge (T.prev i) ∈ C.edges ∧ T.edge i ∈ C.edges)


-- @@ L127-127 verbatim
end LoopMultigraph

-- @@ L128-128 verbatim
end Sabidussi
