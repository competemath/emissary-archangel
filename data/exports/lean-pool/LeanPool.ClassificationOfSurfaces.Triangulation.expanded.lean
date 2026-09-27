/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex
public import Mathlib.Geometry.Manifold.Instances.Real
import LeanPool.ClassificationOfSurfaces.Moise.ChartInduction
import LeanPool.ClassificationOfSurfaces.Moise.DualConnectivity
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L16-27 verbatim
/-!
# Finite surface triangulations

This finite incidence package is consumed by the cell-complex conversion and fed by the faithful
`GeometricTriangulation` object through
`GeometricTriangulation.toFiniteSurfaceTriangulation`. Radó's theorem enters as
`moise_triangulation`, proved in `ClassificationOfSurfaces/Moise/`.

An arbitrary `FiniteSurfaceTriangulation` record does not certify that its incidence data describe
its stored realization. The classification proof therefore starts from `GeometricTriangulation`
and uses the incidence certificate constructed by its bridge.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace LeanEval

-- @@ L32-32 verbatim
namespace Topology

-- @@ L33-33 verbatim
namespace ClassificationOfSurfaces


-- @@ L35-39 verbatim
/-- An oriented use of an edge in a triangle boundary word. -/
inductive OrientedEdge (α : Type*) where
  | pos : α → OrientedEdge α
  | neg : α → OrientedEdge α
deriving DecidableEq, Repr, Fintype


-- @@ L41-41 verbatim
namespace OrientedEdge


-- @@ L43-46 verbatim
/-- The underlying unoriented edge. -/
def edge {α : Type*} : OrientedEdge α → α
  | pos e => e
  | neg e => e


-- @@ L48-51 verbatim
/-- Reverse an oriented edge. -/
def flip {α : Type*} : OrientedEdge α → OrientedEdge α
  | pos e => neg e
  | neg e => pos e


-- @@ L53-54 verbatim
@[simp] theorem flip_flip {α : Type*} (e : OrientedEdge α) : flip (flip e) = e := by
  cases e <;> rfl


-- @@ L56-56 verbatim
end OrientedEdge


-- @@ L58-78 verbatim
/-- Finite combinatorial validity data for the project triangulation object.

This deliberately stays close to what the current PL complex handoff can prove:
edges have two vertices, triangles have three vertices, recorded endpoints lie
on their edge, and every edge appearing in a triangle boundary is a face of that
triangle.  Cyclic ordering and quotient-realization geometry are separate
theorem boundaries. -/
structure FiniteSurfaceTriangulation.Valid
    (Vertex Edge Triangle : Type*) [DecidableEq Vertex]
    (edgeVertices : Edge → Finset Vertex)
    (triangleVertices : Triangle → Finset Vertex)
    (edgeSource edgeTarget : Edge → Vertex)
    (triangleBoundary : Triangle → List (OrientedEdge Edge)) : Prop where
  edge_card : ∀ e : Edge, (edgeVertices e).card = 2
  triangle_card : ∀ t : Triangle, (triangleVertices t).card = 3
  edgeSource_mem : ∀ e : Edge, edgeSource e ∈ edgeVertices e
  edgeTarget_mem : ∀ e : Edge, edgeTarget e ∈ edgeVertices e
  edgeSource_ne_edgeTarget : ∀ e : Edge, edgeSource e ≠ edgeTarget e
  boundary_edge_vertices_subset :
    ∀ t : Triangle, ∀ oe ∈ triangleBoundary t,
      edgeVertices oe.edge ⊆ triangleVertices t


-- @@ L80-115 verbatim
/-- A finite triangulation of a topological surface.

This should eventually be replaced by, or bridged to, the best available mathlib notion of finite
simplicial/CW complex realization.  For now it records the public API needed by the common
triangulation-to-cell-complex bridge: finite incidence data, a topological realization, and a
homeomorphism from that realization to the target surface. -/
structure FiniteSurfaceTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The `Vertex` declaration. -/
  Vertex : Type
  /-- The `Edge` declaration. -/
  Edge : Type
  /-- The `Triangle` declaration. -/
  Triangle : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  edgeFintype : Fintype Edge
  triangleFintype : Fintype Triangle
  /-- The `realization` declaration. -/
  realization : Type
  realizationTop : TopologicalSpace realization
  /-- The `edgeVertices` declaration. -/
  edgeVertices : Edge → Finset Vertex
  /-- The `triangleVertices` declaration. -/
  triangleVertices : Triangle → Finset Vertex
  /-- The `edgeSource` declaration. -/
  edgeSource : Edge → Vertex
  /-- The `edgeTarget` declaration. -/
  edgeTarget : Edge → Vertex
  /-- The `triangleBoundary` declaration. -/
  triangleBoundary : Triangle → List (OrientedEdge Edge)
  /-- The `edgeIsBoundary` declaration. -/
  edgeIsBoundary : Edge → Prop
  isSurfaceTriangulation :
    FiniteSurfaceTriangulation.Valid Vertex Edge Triangle edgeVertices triangleVertices
      edgeSource edgeTarget triangleBoundary
  homeomorphSurface : Nonempty (realization ≃ₜ S)


-- @@ L117-117 verbatim
attribute [instance] FiniteSurfaceTriangulation.realizationTop

-- @@ L118-118 verbatim
attribute [instance] FiniteSurfaceTriangulation.vertexFintype

-- @@ L119-119 verbatim
attribute [instance] FiniteSurfaceTriangulation.vertexDecidableEq

-- @@ L120-120 verbatim
attribute [instance] FiniteSurfaceTriangulation.edgeFintype

-- @@ L121-121 verbatim
attribute [instance] FiniteSurfaceTriangulation.triangleFintype


-- @@ L123-123 verbatim
namespace FiniteSurfaceTriangulation


-- @@ L125-127 verbatim
/-- Number of vertices in a finite surface triangulation. -/
def numVertices {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Vertex


-- @@ L129-131 verbatim
/-- Number of edges in a finite surface triangulation. -/
def numEdges {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Edge


-- @@ L133-135 verbatim
/-- Number of triangles in a finite surface triangulation. -/
def numTriangles {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Triangle


-- @@ L137-141 verbatim
/-- Source vertex of an oriented edge occurrence in a triangulation. -/
def orientedEdgeSource {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeSource e
  | OrientedEdge.neg e => T.edgeTarget e


-- @@ L143-147 verbatim
/-- Target vertex of an oriented edge occurrence in a triangulation. -/
def orientedEdgeTarget {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeTarget e
  | OrientedEdge.neg e => T.edgeSource e


-- @@ L149-152 verbatim
/-- A position in one of the stored oriented triangle boundaries. -/
abbrev BoundaryPosition {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) :=
  Σ t : T.Triangle, Fin (T.triangleBoundary t).length


-- @@ L154-154 verbatim
namespace BoundaryPosition


-- @@ L156-159 verbatim
/-- The oriented edge stored at a triangle-boundary position. -/
def orientedEdge {S : Type*} [TopologicalSpace S] {T : FiniteSurfaceTriangulation S}
    (o : T.BoundaryPosition) : OrientedEdge T.Edge :=
  (T.triangleBoundary o.1).get o.2


-- @@ L161-164 verbatim
/-- The unoriented edge stored at a triangle-boundary position. -/
def edge {S : Type*} [TopologicalSpace S] {T : FiniteSurfaceTriangulation S}
    (o : T.BoundaryPosition) : T.Edge :=
  o.orientedEdge.edge


-- @@ L166-166 verbatim
end BoundaryPosition


-- @@ L168-171 verbatim
/-- Two triangles are adjacent when their stored boundaries share an unoriented edge. -/
def TriangleAdjacent {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) (f g : T.Triangle) : Prop :=
  ∃ df ∈ T.triangleBoundary f, ∃ dg ∈ T.triangleBoundary g, df.edge = dg.edge


-- @@ L173-191 verbatim
/-- Incidence information needed by the legacy triangulation-to-cell-complex bridge.

`edge_valence_le_two` is deliberately stated for boundary positions rather than merely named
edges. This detects repeated uses inside one boundary word as well as uses by different triangles.
The separate `edge_used` field is necessary because the legacy triangulation type can contain
named edges which occur in no triangle boundary. Genuine geometric triangulations will discharge
both fields from their generated two-vertex faces. -/
structure IncidenceCertificate {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) : Prop where
  triangle_nonempty : Nonempty T.Triangle
  boundary_rotated_injective :
    ∀ f g, (T.triangleBoundary f).IsRotated (T.triangleBoundary g) → f = g
  edge_used : ∀ e, ∃ o : T.BoundaryPosition, o.edge = e
  edge_valence_le_two :
    ∀ e (o₀ o₁ o₂ : T.BoundaryPosition),
      o₀.edge = e → o₁.edge = e → o₂.edge = e →
        o₀ = o₁ ∨ o₀ = o₂ ∨ o₁ = o₂
  dual_connected :
    ∀ f g, Relation.ReflTransGen T.TriangleAdjacent f g


-- @@ L193-193 verbatim
end FiniteSurfaceTriangulation



-- @@ L196-196 verbatim
namespace GeometricTriangulation


-- @@ L198-198 verbatim
variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)


-- @@ L200-204 verbatim
/-- Forget the target-space homeomorphism and retain the intrinsic two-complex. -/
@[reducible] def toIntrinsic : Moise.IntrinsicTwoComplex where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card


-- @@ L206-206 verbatim
@[simp] theorem toIntrinsic_faces : T.toIntrinsic.faces = T.faces := rfl


-- @@ L208-211 verbatim
/-- Source vertex of an oriented geometric edge. -/
noncomputable def orientedEdgeSource : OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeSource e
  | OrientedEdge.neg e => T.edgeTarget e


-- @@ L213-216 verbatim
/-- Target vertex of an oriented geometric edge. -/
noncomputable def orientedEdgeTarget : OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeTarget e
  | OrientedEdge.neg e => T.edgeSource e


-- @@ L218-226 verbatim
/-- The globally named edge between two consecutive cyclic vertices of a face, signed so that
its orientation follows the cyclic order of that face. -/
noncomputable def orientedFaceEdge (t : T.Triangle) (i : ZMod 3) :
    OrientedEdge T.Edge :=
  let e := T.toIntrinsic.faceEdge t i
  if T.edgeSource e = T.toIntrinsic.faceVertex t i then
    OrientedEdge.pos e
  else
    OrientedEdge.neg e


-- @@ L228-231 verbatim
@[simp] theorem orientedFaceEdge_edge (t : T.Triangle) (i : ZMod 3) :
    (T.orientedFaceEdge t i).edge = T.toIntrinsic.faceEdge t i := by
  rw [orientedFaceEdge]
  split_ifs <;> rfl


-- @@ L233-241 verbatim
@[simp] theorem orientedFaceEdge_source (t : T.Triangle) (i : ZMod 3) :
    T.orientedEdgeSource (T.orientedFaceEdge t i) =
      T.toIntrinsic.faceVertex t i := by
  rw [orientedFaceEdge]
  split_ifs with h
  · exact h
  · rcases T.toIntrinsic.faceEdge_endpoint_order t i with hforward | hreverse
    · exact (h hforward.1).elim
    · exact hreverse.2


-- @@ L243-254 verbatim
@[simp] theorem orientedFaceEdge_target (t : T.Triangle) (i : ZMod 3) :
    T.orientedEdgeTarget (T.orientedFaceEdge t i) =
      T.toIntrinsic.faceVertex t (i + 1) := by
  rw [orientedFaceEdge]
  split_ifs with h
  · rcases T.toIntrinsic.faceEdge_endpoint_order t i with hforward | hreverse
    · exact hforward.2
    · exact (T.toIntrinsic.faceVertex_ne_next t i
        (h.symm.trans hreverse.1)).elim
  · rcases T.toIntrinsic.faceEdge_endpoint_order t i with hforward | hreverse
    · exact (h hforward.1).elim
    · exact hreverse.1


-- @@ L256-259 verbatim
/-- The cyclic signed boundary of a geometric triangle.  Slot `i` traverses from the `i`-th
cyclic face vertex to the next one. -/
noncomputable def triangleBoundary (t : T.Triangle) : List (OrientedEdge T.Edge) :=
  List.ofFn fun i : Fin 3 => T.orientedFaceEdge t (ZMod.finEquiv 3 i)


-- @@ L261-264 verbatim
/-- Every cyclic triangle boundary has exactly three occurrences. -/
@[simp] theorem triangleBoundary_length (t : T.Triangle) :
    (T.triangleBoundary t).length = 3 := by
  simp [triangleBoundary]


-- @@ L266-278 verbatim
/-- Reading a cyclic triangle boundary recovers the correspondingly indexed oriented face
edge. -/
theorem triangleBoundary_get (t : T.Triangle)
    (i : Fin (T.triangleBoundary t).length) :
    (T.triangleBoundary t).get i =
      T.orientedFaceEdge t
        (ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) i)) := by
  let j : Fin 3 := Fin.cast (T.triangleBoundary_length t) i
  let boundaryFn := fun k : Fin 3 => T.orientedFaceEdge t (ZMod.finEquiv 3 k)
  let k : Fin (List.ofFn boundaryFn).length := ⟨j.val, by simp⟩
  change (List.ofFn boundaryFn).get k = boundaryFn j
  rw [List.get_ofFn]
  congr


-- @@ L280-288 verbatim
/-- The underlying edge at a cyclic boundary position is the intrinsic edge with the same
index. -/
theorem triangleBoundary_get_edge (t : T.Triangle)
    (i : Fin (T.triangleBoundary t).length) :
    ((T.triangleBoundary t).get i).edge =
      T.toIntrinsic.faceEdge t
        (ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) i)) := by
  rw [T.triangleBoundary_get]
  exact T.orientedFaceEdge_edge _ _


-- @@ L290-297 verbatim
/-- The source of a boundary occurrence is its cyclic face vertex. -/
theorem triangleBoundary_get_source (t : T.Triangle)
    (i : Fin (T.triangleBoundary t).length) :
    T.orientedEdgeSource ((T.triangleBoundary t).get i) =
      T.toIntrinsic.faceVertex t
        (ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) i)) := by
  rw [T.triangleBoundary_get]
  exact T.orientedFaceEdge_source _ _


-- @@ L299-306 verbatim
/-- The target of a boundary occurrence is the next cyclic face vertex. -/
theorem triangleBoundary_get_target (t : T.Triangle)
    (i : Fin (T.triangleBoundary t).length) :
    T.orientedEdgeTarget ((T.triangleBoundary t).get i) =
      T.toIntrinsic.faceVertex t
        (ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) i) + 1) := by
  rw [T.triangleBoundary_get]
  exact T.orientedFaceEdge_target _ _


-- @@ L308-313 verbatim
theorem edge_subset_of_mem_triangleBoundary {t : T.Triangle} {oe : OrientedEdge T.Edge}
    (hoe : oe ∈ T.triangleBoundary t) : oe.edge.1 ⊆ t.1 := by
  rw [triangleBoundary, List.mem_ofFn'] at hoe
  rcases hoe with ⟨i, rfl⟩
  rw [T.orientedFaceEdge_edge]
  exact T.toIntrinsic.faceEdge_subset_face t (ZMod.finEquiv 3 i)


-- @@ L315-332 verbatim
/-- A named geometric edge lies in the underlying triangle-boundary list exactly when it is a
face of that triangle. -/
theorem mem_map_edge_triangleBoundary_iff (t : T.Triangle) (e : T.Edge) :
    e ∈ (T.triangleBoundary t).map OrientedEdge.edge ↔ e.1 ⊆ t.1 := by
  constructor
  · rw [List.mem_map]
    rintro ⟨oe, hoe, rfl⟩
    exact T.edge_subset_of_mem_triangleBoundary hoe
  · intro he
    obtain ⟨i, hi⟩ := T.toIntrinsic.exists_faceEdge_eq_of_subset t e he
    have hmem : T.orientedFaceEdge t i ∈ T.triangleBoundary t := by
      rw [triangleBoundary, List.mem_ofFn']
      refine ⟨(ZMod.finEquiv 3).symm i, ?_⟩
      exact congrArg (T.orientedFaceEdge t)
        ((ZMod.finEquiv 3).apply_symm_apply i)
    rw [List.mem_map]
    refine ⟨T.orientedFaceEdge t i, hmem, ?_⟩
    rw [T.orientedFaceEdge_edge, hi]


-- @@ L334-348 verbatim
/-- Distinct cyclic positions in one face name distinct underlying edges. -/
theorem triangleBoundary_edge_get_injective (t : T.Triangle) :
    Function.Injective fun i : Fin (T.triangleBoundary t).length =>
      ((T.triangleBoundary t).get i).edge := by
  intro i j hij
  change ((T.triangleBoundary t).get i).edge =
    ((T.triangleBoundary t).get j).edge at hij
  rw [T.triangleBoundary_get_edge, T.triangleBoundary_get_edge] at hij
  have hz : ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) i) =
      ZMod.finEquiv 3 (Fin.cast (T.triangleBoundary_length t) j) :=
    T.toIntrinsic.faceEdge_injective t hij
  have hf : Fin.cast (T.triangleBoundary_length t) i =
      Fin.cast (T.triangleBoundary_length t) j :=
    (ZMod.finEquiv 3).injective hz
  exact Fin.cast_injective _ hf


-- @@ L350-357 verbatim
/-- Each geometric edge occurs at most once in a triangle's canonical boundary list. -/
theorem triangleBoundary_nodup (t : T.Triangle) : (T.triangleBoundary t).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  have hedge := congrArg OrientedEdge.edge hij
  simp only [orientedFaceEdge_edge] at hedge
  exact (ZMod.finEquiv 3).injective
    (T.toIntrinsic.faceEdge_injective t hedge)


-- @@ L359-388 verbatim
/-- Package a geometric triangulation as the project's `FiniteSurfaceTriangulation` object.

This is the compatibility bridge: downstream consumers (the cell-complex conversion and the
Gallier--Xu route) keep their interface, while the triangulation content now lives in the
faithful geometric object. -/
noncomputable def toFiniteSurfaceTriangulation : FiniteSurfaceTriangulation S where
  Vertex := T.Vertex
  Edge := T.Edge
  Triangle := T.Triangle
  vertexFintype := T.vertexFintype
  vertexDecidableEq := T.vertexDecidableEq
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := T.realization
  realizationTop := inferInstance
  edgeVertices := fun e => e.1
  triangleVertices := fun t => t.1
  edgeSource := T.edgeSource
  edgeTarget := T.edgeTarget
  triangleBoundary := T.triangleBoundary
  edgeIsBoundary := fun e => T.IsBoundaryEdge e
  isSurfaceTriangulation :=
    { edge_card := T.edge_card
      triangle_card := T.triangle_card
      edgeSource_mem := T.edgeSource_mem
      edgeTarget_mem := T.edgeTarget_mem
      edgeSource_ne_edgeTarget := T.edgeSource_ne_edgeTarget
      boundary_edge_vertices_subset := fun _t _oe hoe =>
        T.edge_subset_of_mem_triangleBoundary hoe }
  homeomorphSurface := ⟨T.homeo⟩


-- @@ L390-393 verbatim
/-- The bridge realizes the ambient space. -/
theorem toFiniteSurfaceTriangulation_homeomorphSurface :
    Nonempty (T.toFiniteSurfaceTriangulation.realization ≃ₜ S) :=
  T.toFiniteSurfaceTriangulation.homeomorphSurface


-- @@ L395-406 verbatim
private theorem boundaryPosition_eq_of_fst_eq_of_edge_eq
    {o p : T.toFiniteSurfaceTriangulation.BoundaryPosition}
    (hface : o.1 = p.1) (hedge : o.edge = p.edge) : o = p := by
  rcases o with ⟨f, i⟩
  rcases p with ⟨g, j⟩
  simp only at hface
  subst g
  change ((T.triangleBoundary f).get i).edge =
    ((T.triangleBoundary f).get j).edge at hedge
  have hij : i = j := T.triangleBoundary_edge_get_injective f hedge
  subst j
  rfl


-- @@ L408-437 verbatim
private theorem powersetCard_eq_of_boundary_rotated
    {f g : T.Triangle}
    (hrot : (T.triangleBoundary f).IsRotated (T.triangleBoundary g)) :
    f.1.powersetCard 2 = g.1.powersetCard 2 := by
  ext e
  constructor
  · intro he
    let E : T.Edge := ⟨e, T.mem_edges_of_subset_face f.2
      (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp he).2⟩
    have hmemf : E ∈ (T.triangleBoundary f).map OrientedEdge.edge :=
      (T.mem_map_edge_triangleBoundary_iff f E).mpr
        (Finset.mem_powersetCard.mp he).1
    have hmemg : E ∈ (T.triangleBoundary g).map OrientedEdge.edge :=
      (hrot.map OrientedEdge.edge).mem_iff.mp hmemf
    exact Finset.mem_powersetCard.mpr ⟨
      (T.mem_map_edge_triangleBoundary_iff g E).mp hmemg,
      (Finset.mem_powersetCard.mp he).2⟩
  · intro he
    let E : T.Edge := ⟨e, T.mem_edges_of_subset_face g.2
      (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp he).2⟩
    have hmemg : E ∈ (T.triangleBoundary g).map OrientedEdge.edge :=
      (T.mem_map_edge_triangleBoundary_iff g E).mpr
        (Finset.mem_powersetCard.mp he).1
    have hmemf : E ∈ (T.triangleBoundary f).map OrientedEdge.edge :=
      (hrot.map OrientedEdge.edge).mem_iff.mpr hmemg
    exact Finset.mem_powersetCard.mpr ⟨
      (T.mem_map_edge_triangleBoundary_iff f E).mp hmemf,
      (Finset.mem_powersetCard.mp he).2⟩


-- @@ L439-452 verbatim
private theorem faceAdjacent_to_triangleAdjacent
    {f g : TriangleFamily.Face T.faces}
    (hfg : TriangleFamily.FaceAdjacent T.faces f g) :
    T.toFiniteSurfaceTriangulation.TriangleAdjacent f g := by
  rcases hfg with ⟨e, hecard, hef, heg⟩
  let E : T.Edge := ⟨e, T.mem_edges_of_subset_face f.2 hef hecard⟩
  have hmemf : E ∈ (T.triangleBoundary f).map OrientedEdge.edge :=
    (T.mem_map_edge_triangleBoundary_iff f E).mpr hef
  have hmemg : E ∈ (T.triangleBoundary g).map OrientedEdge.edge :=
    (T.mem_map_edge_triangleBoundary_iff g E).mpr heg
  rw [List.mem_map] at hmemf hmemg
  rcases hmemf with ⟨df, hdf, hdfE⟩
  rcases hmemg with ⟨dg, hdg, hdgE⟩
  exact ⟨df, hdf, dg, hdg, hdfE.trans hdgE.symm⟩


-- @@ L454-535 verbatim
/-- A geometric surface-incidence certificate supplies every incidence obligation required by
the legacy finite triangulation bridge. -/
theorem incidenceCertificate_of_surfaceIncidence
    (h : T.SurfaceIncidence) :
    T.toFiniteSurfaceTriangulation.IncidenceCertificate := by
  classical
  refine {
    triangle_nonempty := ?_
    boundary_rotated_injective := ?_
    edge_used := ?_
    edge_valence_le_two := ?_
    dual_connected := ?_ }
  · rcases h.faces_nonempty with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · intro f g hrot
    apply Subtype.ext
    exact Finset.eq_of_powersetCard_eq
      ((T.triangle_card f).trans (T.triangle_card g).symm)
      (by decide) (by simp [T.triangle_card f])
      (T.powersetCard_eq_of_boundary_rotated hrot)
  · intro e
    rcases Finset.mem_biUnion.mp e.2 with ⟨t, ht, hep⟩
    let f : T.toFiniteSurfaceTriangulation.Triangle := ⟨t, ht⟩
    have hmem : e ∈
        (T.toFiniteSurfaceTriangulation.triangleBoundary f).map
          OrientedEdge.edge := by
      change e ∈
        (T.triangleBoundary (⟨t, ht⟩ : T.Triangle)).map
          OrientedEdge.edge
      exact (T.mem_map_edge_triangleBoundary_iff _ _).mpr
        (Finset.mem_powersetCard.mp hep).1
    rw [List.mem_map] at hmem
    rcases hmem with ⟨oe, hoe, hoeEdge⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hoe
    refine ⟨⟨f, i⟩, ?_⟩
    simp only [FiniteSurfaceTriangulation.BoundaryPosition.edge,
      FiniteSurfaceTriangulation.BoundaryPosition.orientedEdge, hi]
    exact hoeEdge
  · intro e o₀ o₁ o₂ ho₀ ho₁ ho₂
    by_contra hdistinct
    simp only [not_or] at hdistinct
    rcases hdistinct with ⟨ho₀₁, ho₀₂, ho₁₂⟩
    have hf₀₁ : o₀.1 ≠ o₁.1 := fun hfaces ↦
      ho₀₁ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₀.trans ho₁.symm))
    have hf₀₂ : o₀.1 ≠ o₂.1 := fun hfaces ↦
      ho₀₂ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₀.trans ho₂.symm))
    have hf₁₂ : o₁.1 ≠ o₂.1 := fun hfaces ↦
      ho₁₂ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₁.trans ho₂.symm))
    have hs₀ : e.1 ⊆ o₀.1.1 := by
      rw [← ho₀]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₀.1) o₀.2)
    have hs₁ : e.1 ⊆ o₁.1.1 := by
      rw [← ho₁]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₁.1) o₁.2)
    have hs₂ : e.1 ⊆ o₂.1.1 := by
      rw [← ho₂]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₂.1) o₂.2)
    have hm₀ : o₀.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₀.1.2, hs₀⟩
    have hm₁ : o₁.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₁.1.2, hs₁⟩
    have hm₂ : o₂.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₂.1.2, hs₂⟩
    have hv₀₁ : o₀.1.1 ≠ o₁.1.1 := fun hv ↦ hf₀₁ (Subtype.ext hv)
    have hv₀₂ : o₀.1.1 ≠ o₂.1.1 := fun hv ↦ hf₀₂ (Subtype.ext hv)
    have hv₁₂ : o₁.1.1 ≠ o₂.1.1 := fun hv ↦ hf₁₂ (Subtype.ext hv)
    have hthree : 2 < (T.faces.filter fun t ↦ e.1 ⊆ t).card :=
      Finset.two_lt_card_iff.mpr
        ⟨o₀.1.1, o₁.1.1, o₂.1.1, hm₀, hm₁, hm₂,
          hv₀₁, hv₀₂, hv₁₂⟩
    have heEdges : e.1 ∈ TriangleFamily.edges T.faces := by
      exact e.2
    exact (Nat.not_lt_of_ge (h.edge_valence_le_two e.1 heEdges)) hthree
  · intro f g
    apply Relation.ReflTransGen.mono (fun _ _ ↦ T.faceAdjacent_to_triangleAdjacent)
    exact h.dual_connected f g


-- @@ L537-537 verbatim
end GeometricTriangulation


-- @@ L539-539 verbatim
section EvalHypotheses


-- @@ L541-541 verbatim
open scoped Manifold


-- @@ L543-543 verbatim
variable (S : Type*) [TopologicalSpace S]

-- @@ L544-544 verbatim
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]

-- @@ L545-545 verbatim
variable [ChartedSpace (EuclideanHalfSpace 2) S]

-- @@ L546-546 verbatim
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]


-- @@ L548-562 verbatim
/-- The compact bordered extension of Radó's theorem.  Moise, *Geometric Topology in Dimensions
2 and 3*, Ch. 8, Thm. 3 proves the boundaryless case; the proof assembled here carries the same
induction through half-disk charts while preserving the manifold-boundary stratum.

Every compact connected surface in the Eval sense admits a finite geometric triangulation — a
homeomorphism onto the realization of a finite two-dimensional simplicial complex.

Semantic anchors: the conclusion implies `CompactSpace S` and `T2Space S`
(`GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`), and is refuted for
non-compact spaces (`Moise/Countermodels.lean`), so it cannot be discharged by a junk witness.

The proof is the assembled boundary-preserving Radó chart induction
(`Moise.moise_triangulation_of_boundaries`). -/
theorem moise_triangulation : Nonempty (GeometricTriangulation S) :=
  Moise.moise_triangulation_of_boundaries S


-- @@ L564-571 verbatim
/-- Radó's theorem with its conclusion expanded into the finite vertex type, the family of
three-vertex faces, and the homeomorphism from their barycentric realization.  This is a
definition-audit surface for `moise_triangulation`, not a second proof. -/
theorem moise_triangulation_explicit :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F : Finset (Finset V)),
      (∀ t ∈ F, t.card = 3) ∧ Nonempty (GeometricRealization V F ≃ₜ S) :=
  nonempty_geometricTriangulation_iff_explicit.mp (moise_triangulation S)


-- @@ L573-576 verbatim
/-- The named geometric triangulation produced for a compact connected Eval surface. -/
noncomputable def compactEvalSurfaceGeometricTriangulation :
    GeometricTriangulation S :=
  Classical.choice (moise_triangulation S)


-- @@ L578-581 verbatim
/-- The Radó triangulation carries nonempty-face, edge-valence, and dual-connectivity data. -/
theorem compact_eval_surface_geometricTriangulation_surfaceIncidence :
    (compactEvalSurfaceGeometricTriangulation S).SurfaceIncidence :=
  (compactEvalSurfaceGeometricTriangulation S).surfaceIncidence


-- @@ L583-588 verbatim
/-- The named finite surface triangulation produced for a compact connected Eval surface, obtained
from the geometric triangulation boundary `moise_triangulation` through the compatibility
bridge. -/
noncomputable def compactEvalSurfaceFiniteSurfaceTriangulation :
    FiniteSurfaceTriangulation S :=
  (compactEvalSurfaceGeometricTriangulation S).toFiniteSurfaceTriangulation


-- @@ L590-594 verbatim
/-- The compatibility triangulation inherits the complete incidence certificate. -/
theorem compact_eval_surface_finiteSurfaceTriangulation_incidenceCertificate :
    (compactEvalSurfaceFiniteSurfaceTriangulation S).IncidenceCertificate :=
    (compactEvalSurfaceGeometricTriangulation S).incidenceCertificate_of_surfaceIncidence
    (compact_eval_surface_geometricTriangulation_surfaceIncidence S)


-- @@ L596-599 verbatim
/-- The named compact connected Eval surface triangulation realizes the ambient surface. -/
theorem compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface :
    Nonempty ((compactEvalSurfaceFiniteSurfaceTriangulation S).realization ≃ₜ S) :=
  (compactEvalSurfaceFiniteSurfaceTriangulation S).homeomorphSurface


-- @@ L601-605 verbatim
/-- Moise/PL theorem boundary: compact connected Eval surfaces admit finite triangulations. -/
theorem compact_eval_surface_finitely_triangulable :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨compactEvalSurfaceFiniteSurfaceTriangulation S,
    compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface S⟩


-- @@ L607-607 verbatim
end EvalHypotheses



-- @@ L610-610 verbatim
end ClassificationOfSurfaces

-- @@ L611-611 verbatim
end Topology

-- @@ L612-612 verbatim
end LeanEval
