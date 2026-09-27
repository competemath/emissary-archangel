/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary
import Mathlib.CategoryTheory.Category.Init


-- @@ L11-19 verbatim
/-!
# A conforming plane model of an intrinsic replacement graph

The first intrinsic graph replacement need not be metrically close to the original embedding;
its role here is to polygonalize the abstract finite graph once.  A common segment arrangement
turns all replacement edges into one plane graph complex.  The original embedding can then be
transferred to that plane complex and the ordinary plane one-skeleton approximation theorem can
be applied at an arbitrary tolerance.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace LeanEval

-- @@ L24-24 verbatim
namespace Topology

-- @@ L25-25 verbatim
namespace ClassificationOfSurfaces

-- @@ L26-26 verbatim
namespace Moise


-- @@ L28-28 verbatim
namespace PlaneComplex


-- @@ L30-49 verbatim
/-- A nonempty face of cardinality at most two is the segment between two (possibly equal)
vertex positions. -/
theorem exists_cellCarrier_eq_segment (L : PlaneComplex)
    {s : Finset L.Vertex} (hs : s ∈ L.simplexes) (hcard : s.card ≤ 2) :
    ∃ a b : Plane, L.cellCarrier s = segment ℝ a b := by
  have hpos : 0 < s.card := Finset.card_pos.mpr (L.nonempty_of_mem s hs)
  have hcases : s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    refine ⟨L.position v, L.position v, ?_⟩
    simp [PlaneComplex.cellCarrier]
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp htwo
    refine ⟨L.position v, L.position w, ?_⟩
    rw [PlaneComplex.cellCarrier]
    have himage :
        L.position '' (↑({v, w} : Finset L.Vertex) : Set L.Vertex) =
          {L.position v, L.position w} := by
      ext x
      simp
    rw [himage, convexHull_pair]


-- @@ L51-51 verbatim
end PlaneComplex


-- @@ L53-53 verbatim
namespace IntrinsicTwoComplex


-- @@ L55-57 verbatim
variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}


-- @@ L59-64 verbatim
/-- A one- or two-vertex face from one finite complete-edge target complex.  These faces form a
finite segment cover of the corresponding complete replacement edge. -/
abbrev ReplacementSegmentFace :=
  Σ e : K.Edge,
    {s : Finset (K.replacementArc hcont hinj D C e).completeTarget.Vertex //
      s ∈ (K.replacementArc hcont hinj D C e).completeTarget.simplexes ∧ s.card ≤ 2}


-- @@ L66-73 verbatim
private theorem replacementSegmentFace_has_endpoints
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    ∃ a b : Plane,
      (K.replacementArc hcont hinj D C q.1).completeTarget.cellCarrier q.2.1 =
        segment ℝ a b :=
  (K.replacementArc hcont hinj D C q.1).completeTarget.exists_cellCarrier_eq_segment
    q.2.2.1 q.2.2.2


-- @@ L75-79 verbatim
/-- First endpoint of a selected replacement segment. -/
noncomputable def replacementSegmentLeft
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) : Plane :=
  Classical.choose (private_decl% (K.replacementSegmentFace_has_endpoints q))


-- @@ L81-86 verbatim
/-- Second endpoint of a selected replacement segment. -/
noncomputable def replacementSegmentRight
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) : Plane :=
  Classical.choose
    (Classical.choose_spec (private_decl% (K.replacementSegmentFace_has_endpoints q)))


-- @@ L88-94 verbatim
theorem replacementSegment_eq_cellCarrier
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)) :
    segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q) =
      (K.replacementArc hcont hinj D C q.1).completeTarget.cellCarrier q.2.1 := by
  exact (Classical.choose_spec
    (Classical.choose_spec (private_decl% (K.replacementSegmentFace_has_endpoints q)))).symm


-- @@ L96-100 verbatim
/-- Union of all selected segment faces over all complete replacement edges. -/
def replacementGraphCarrier : Set Plane :=
  ⋃ q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C),
    segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q)


-- @@ L102-108 verbatim
/-- The common arrangement used to reconcile every edge's independent finite target complex. -/
noncomputable def replacementGraphArrangement : BrokenLineData (Set.univ : Set Plane) :=
  BrokenLineData.segmentFamilyChain
    (K.replacementSegmentLeft
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    (K.replacementSegmentRight
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))


-- @@ L110-115 verbatim
/-- Restrict the common arrangement to the actual replacement segments. -/
noncomputable def replacementGraphBaseComplex : PlaneComplex :=
  (K.replacementGraphArrangement
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).arrangementMesh.toPlaneComplex
    |>.restrictToSet (K.replacementGraphCarrier
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))


-- @@ L117-120 verbatim
/-- The conforming finite plane graph complex of the simultaneous intrinsic replacement. -/
noncomputable def replacementGraphComplex : PlaneComplex :=
  (K.replacementGraphBaseComplex
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)).oneSkeleton


-- @@ L122-159 verbatim
private theorem exists_replacementGraphBase_face
    (q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C))
    {x : Plane}
    (hx : x ∈ segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q)) :
    ∃ s ∈ (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
      x ∈ (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
      (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
        segment ℝ (K.replacementSegmentLeft q) (K.replacementSegmentRight q) ∧
      s.card ≤ 2 := by
  let left := K.replacementSegmentLeft
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  let right := K.replacementSegmentRight
    (hcont := hcont) (hinj := hinj) (D := D) (C := C)
  obtain ⟨s, hs, hxs, hsSegment⟩ :=
    BrokenLineData.exists_face_on_segmentFamily left right q hx
  have hsCarrier :
      (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        K.replacementGraphCarrier
          (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
    exact hsSegment.trans (Set.subset_iUnion (fun q ↦ segment ℝ (left q) (right q)) q)
  have hsBase : s ∈ (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes :=
    ((K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.mem_restrictToSet_simplexes_iff
        (K.replacementGraphCarrier
          (hcont := hcont) (hinj := hinj) (D := D) (C := C))).mpr
      ⟨hs, hsCarrier⟩
  refine ⟨s, hsBase, hxs, ?_, ?_⟩
  · exact hsSegment
  · apply (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.card_le_two_of_vertices_mem_segment hs
    · intro v hv
      apply hsSegment
      exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩


-- @@ L161-173 verbatim
theorem replacementGraphBaseComplex_support :
    (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  apply Set.Subset.antisymm
  · exact (K.replacementGraphArrangement).arrangementMesh.toPlaneComplex
      |>.restrictToSet_support_subset K.replacementGraphCarrier
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, -, -⟩ := K.exists_replacementGraphBase_face q hxq
    rw [PlaneComplex.support]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hxs⟩


-- @@ L175-190 verbatim
theorem replacementGraphComplex_support :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) := by
  apply Set.Subset.antisymm
  · exact (K.replacementGraphBaseComplex).oneSkeleton_support_subset.trans_eq
      K.replacementGraphBaseComplex_support
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hxs, -, hscard⟩ := K.exists_replacementGraphBase_face q hxq
    rw [PlaneComplex.support]
    exact Set.mem_iUnion₂.mpr
      ⟨s, (K.replacementGraphBaseComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)
          |>.mem_oneSkeleton_simplexes).mpr ⟨hs, hscard⟩, hxs⟩


-- @@ L192-227 verbatim
theorem replacementGraphCarrier_eq_image :
    K.replacementGraphCarrier
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) =
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    rw [K.replacementSegment_eq_cellCarrier q] at hxq
    have hxEdge : x ∈
        (K.replacementArc hcont hinj D C q.1).completeCarrier := by
      rw [← (K.replacementArc hcont hinj D C q.1).completeTarget_support]
      exact (K.replacementArc hcont hinj D C q.1).completeTarget
        |>.cellCarrier_subset_support q.2.2.1 hxq
    rw [← K.graphReplacementMap_image_faceCarrier] at hxEdge
    obtain ⟨y, hye, rfl⟩ := hxEdge
    exact ⟨y, ⟨q.1, hye⟩, rfl⟩
  · rintro x ⟨y, ⟨e, hye⟩, rfl⟩
    have hyEdge : K.graphReplacementMap hcont hinj D C y ∈
        (K.replacementArc hcont hinj D C e).completeCarrier := by
      rw [← K.graphReplacementMap_image_faceCarrier]
      exact ⟨y, hye, rfl⟩
    obtain ⟨s, hs, hys, hsSub, hscard⟩ :=
      (K.replacementArc hcont hinj D C e).exists_completeTarget_face hyEdge
    have hsTarget : s ∈
        (K.replacementArc hcont hinj D C e).completeTarget.simplexes := by
      apply ((K.replacementArc hcont hinj D C e).completeChain.arrangementMesh.toPlaneComplex
        |>.mem_restrictedTo_simplexes_iff
          (K.replacementArc hcont hinj D C e).completeCarrier).mpr
      exact ⟨hs, hsSub⟩
    let q : K.ReplacementSegmentFace
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) :=
      ⟨e, ⟨s, hsTarget, hscard⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [K.replacementSegment_eq_cellCarrier q]
    exact hys


-- @@ L229-233 verbatim
theorem replacementGraphComplex_support_eq_image :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      K.graphReplacementMap hcont hinj D C '' K.oneSkeleton :=
  K.replacementGraphComplex_support.trans K.replacementGraphCarrier_eq_image


-- @@ L235-271 verbatim
/-- Every point of one complete replacement edge has a face of the conforming global graph
complex which remains inside that edge. -/
theorem exists_replacementGraphComplex_face_of_mem_completeCarrier
    (e : K.Edge) {x : Plane}
    (hx : x ∈ (K.replacementArc hcont hinj D C e).completeCarrier) :
    ∃ s ∈ (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
      x ∈ (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
        (K.replacementArc hcont hinj D C e).completeCarrier := by
  obtain ⟨u, hu, hxu, huSub, huCard⟩ :=
    (K.replacementArc hcont hinj D C e).exists_completeTarget_face hx
  have huTarget : u ∈ (K.replacementArc hcont hinj D C e).completeTarget.simplexes := by
    apply ((K.replacementArc hcont hinj D C e).completeChain.arrangementMesh.toPlaneComplex
      |>.mem_restrictedTo_simplexes_iff
        (K.replacementArc hcont hinj D C e).completeCarrier).mpr
    exact ⟨hu, huSub⟩
  let q : K.ReplacementSegmentFace
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) :=
    ⟨e, ⟨u, huTarget, huCard⟩⟩
  have hxSegment : x ∈ segment ℝ
      (K.replacementSegmentLeft q) (K.replacementSegmentRight q) := by
    rw [K.replacementSegment_eq_cellCarrier q]
    exact hxu
  obtain ⟨s, hs, hxs, hsSub, hsCard⟩ :=
    K.exists_replacementGraphBase_face q hxSegment
  refine ⟨s, ?_, hxs, ?_⟩
  · exact (K.replacementGraphBaseComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)
        |>.mem_oneSkeleton_simplexes).mpr ⟨hs, hsCard⟩
  · exact hsSub.trans (by
      rw [K.replacementSegment_eq_cellCarrier q]
      exact (K.replacementArc hcont hinj D C e).completeTarget
        |>.cellCarrier_subset_support huTarget |>.trans_eq
          (K.replacementArc hcont hinj D C e).completeTarget_support)


-- @@ L273-294 verbatim
/-- Each intrinsic face polygon is locally covered by faces of the one global conforming graph
complex. -/
theorem facePolygonalCircle_locallyCoveredBy_replacementGraphComplex (t : K.Face) :
    ∀ x ∈ (K.facePolygonalCircle
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier,
      ∃ s ∈ (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).simplexes,
        x ∈ (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ∧
        (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).cellCarrier s ⊆
          (K.facePolygonalCircle
            (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).carrier := by
  intro x hx
  rw [K.facePolygonalCircle_carrier] at hx ⊢
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsSub⟩ :=
    K.exists_replacementGraphComplex_face_of_mem_completeCarrier (K.faceEdge t i) hxi
  exact ⟨s, hs, hxs, hsSub.trans (Set.subset_iUnion
    (fun j : ZMod 3 ↦
      (K.faceReplacementArc
        (hcont := hcont) (hinj := hinj) (D := D) (C := C) t j).completeCarrier) i)⟩


-- @@ L296-307 verbatim
theorem replacementGraphComplex_support_eq_range :
    (K.replacementGraphComplex
      (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support =
      Set.range (fun x : K.oneSkeleton ↦
        K.graphReplacementMap hcont hinj D C x.1) := by
  rw [K.replacementGraphComplex_support_eq_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩


-- @@ L309-316 verbatim
/-- The intrinsic one-skeleton is homeomorphic to the support of its conforming polygonal plane
graph model. -/
noncomputable def replacementGraphHomeomorph :
    K.oneSkeleton ≃ₜ
      (K.replacementGraphComplex
        (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support :=
  (K.graphReplacementMap_isEmbedding_oneSkeleton hcont hinj D C).toHomeomorph.trans
    (Homeomorph.setCongr K.replacementGraphComplex_support_eq_range.symm)


-- @@ L318-323 verbatim
@[simp] theorem replacementGraphHomeomorph_coe (x : K.oneSkeleton) :
    ((K.replacementGraphHomeomorph
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) x :
        (K.replacementGraphComplex
          (hcont := hcont) (hinj := hinj) (D := D) (C := C)).support) : Plane) =
      K.graphReplacementMap hcont hinj D C x.1 := rfl


-- @@ L325-325 verbatim
end IntrinsicTwoComplex


-- @@ L327-327 verbatim
end Moise

-- @@ L328-328 verbatim
end ClassificationOfSurfaces

-- @@ L329-329 verbatim
end Topology

-- @@ L330-330 verbatim
end LeanEval
