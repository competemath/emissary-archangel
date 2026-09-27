/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.DiskSquare
public import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoves
public import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L16-24 verbatim
/-!
# Polygonal realization of Gallier--Xu P2

This file packages the local two-disk cut model from `DiskSquare` for finite cyclic
presentations.  The first layer normalizes the cyclic position of a nondegenerate positively
oriented cut and supplies an exact selected-face homeomorphism.  It is deliberately stated in
terms of the existing `P2Cut` data, so the presentation-level quotient comparison can use the
same side indices and no second formulation of P2 is introduced.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L30-30 verbatim
namespace FiniteCyclicPresentation


-- @@ L32-32 verbatim
open SurfaceCellComplex


-- @@ L34-34 verbatim
namespace P2


-- @@ L36-44 verbatim
/-- The selected source face has as many stored sides as the two linear cut pieces together. -/
theorem sourceBoundaryLength_eq_cutLength
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P.boundary cut.face.face).length =
      cut.left.length + cut.right.length := by
  obtain ⟨k, hk⟩ := cut.boundary_rotated
  have hlength := congrArg List.length hk
  rw [List.length_rotate, List.length_append] at hlength
  exact (P.orientedBoundary_length cut.face).symm.trans hlength


-- @@ L46-55 verbatim
/-- Rotation of the linear cut word that recovers the stored source boundary.  This version is
used after reducing to the positive traversal orientation. -/
noncomputable def positiveCutRotation
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) : ℕ :=
  Classical.choose (show
    (cut.left ++ cut.right).IsRotated
      (P.boundary cut.face.face) by
    have h := cut.boundary_rotated.symm
    simpa [orientedBoundary, horientation] using h)


-- @@ L57-67 verbatim
theorem rotate_cutBoundary_eq_sourceBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (cut.left ++ cut.right).rotate
        (positiveCutRotation P cut horientation) =
      P.boundary cut.face.face :=
  Classical.choose_spec (show
    (cut.left ++ cut.right).IsRotated
      (P.boundary cut.face.face) by
    have h := cut.boundary_rotated.symm
    simpa [orientedBoundary, horientation] using h)


-- @@ L69-78 verbatim
/-- The linear cut-word index carrying a stored source side. -/
noncomputable def positiveCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (_hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    Fin (cut.left.length + cut.right.length) :=
  ⟨(i.val + positiveCutRotation P cut horientation) %
      (cut.left.length + cut.right.length),
    Nat.mod_lt _ (Nat.add_pos_left hl _)⟩


-- @@ L80-89 verbatim
@[simp]
theorem positiveCutSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (positiveCutSideIndex P cut horientation hl hr i).val =
      (i.val + positiveCutRotation P cut horientation) %
        (cut.left.length + cut.right.length) :=
  rfl


-- @@ L91-114 verbatim
/-- Cyclic alignment of the source boundary is injective on side indices. -/
theorem positiveCutSideIndex_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length) :
    Function.Injective
      (positiveCutSideIndex P cut horientation hl hr) := by
  intro i j hij
  have hmod :
      i.val + positiveCutRotation P cut horientation ≡
        j.val + positiveCutRotation P cut horientation
          [MOD (cut.left.length + cut.right.length)] := by
    exact congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val
        [MOD (cut.left.length + cut.right.length)] :=
    Nat.ModEq.add_right_cancel'
      (positiveCutRotation P cut horientation) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← sourceBoundaryLength_eq_cutLength P cut,
    Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel


-- @@ L116-128 verbatim
theorem positiveCutSideIndex_surjective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length) :
    Function.Surjective
      (positiveCutSideIndex P cut horientation hl hr) := by
  exact ((Fintype.bijective_iff_injective_and_card
    (positiveCutSideIndex P cut horientation hl hr)).2
      ⟨positiveCutSideIndex_injective
          P cut horientation hl hr,
        by
          simp only [Fintype.card_fin]
          exact sourceBoundaryLength_eq_cutLength P cut⟩).2


-- @@ L130-156 verbatim
/-- Lookup at the rotated linear cut index recovers the stored source dart. -/
theorem cutBoundary_get_positiveCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (cut.left ++ cut.right)[
        (positiveCutSideIndex P cut horientation hl hr i).val] =
      (P.boundary cut.face.face)[i.val] := by
  have hiCut :
      i.val < (cut.left ++ cut.right).length := by
    rw [List.length_append,
      ← sourceBoundaryLength_eq_cutLength P cut]
    exact i.isLt
  have hpoint :=
    congrArg (fun word => word[i.val]?)
      (rotate_cutBoundary_eq_sourceBoundary
        P cut horientation)
  rw [List.getElem?_rotate hiCut] at hpoint
  rw [List.getElem?_eq_getElem
      (Nat.mod_lt _
        (by
          rw [List.length_append]
          exact Nat.add_pos_left hl _)),
    List.getElem?_eq_getElem i.isLt] at hpoint
  exact Option.some.inj (by
    simpa [positiveCutSideIndex, List.length_append] using hpoint)


-- @@ L158-170 verbatim
/-- The selected source face, with its cyclic starting point aligned to the cut, is exactly the
local one-polygon-to-two-child quotient model. -/
noncomputable def positiveSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
      (sourceBoundaryLength_eq_cutLength P cut)
      (positiveCutRotation P cut horientation)).trans
    (DiskSquare.sourceChildGluingHomeomorph
      cut.left.length cut.right.length hl hr)


-- @@ L172-188 verbatim
/-- Exact side computation for the cyclically aligned selected-face homeomorphism. -/
theorem positiveSelectedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      DiskSquare.sourceChildGluingHomeomorph
        cut.left.length cut.right.length hl hr
        (PolygonCell.side
          (positiveCutSideIndex P cut horientation hl hr i) t) := by
  rw [positiveSelectedCellHomeomorph, Homeomorph.trans_apply]
  congr 1
  exact PolygonCell.rotateHomeomorph_side_of_eq
    (sourceBoundaryLength_eq_cutLength P cut)
    (Nat.add_pos_left hl _) (positiveCutRotation P cut horientation) i t


-- @@ L190-200 verbatim
/-- A rotated source side lying in the left cut piece, viewed with its local left index. -/
noncomputable def positiveLeftSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    Fin cut.left.length :=
  ⟨(positiveCutSideIndex P cut horientation hl hr i).val, hleft⟩


-- @@ L202-213 verbatim
@[simp]
theorem positiveLeftSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    (positiveLeftSideIndex P cut horientation hl hr i hleft).val =
      (positiveCutSideIndex P cut horientation hl hr i).val :=
  rfl


-- @@ L215-230 verbatim
/-- A rotated source side lying in the right cut piece, viewed with its local right index. -/
noncomputable def positiveRightSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    Fin cut.right.length :=
  ⟨(positiveCutSideIndex P cut horientation hl hr i).val -
      cut.left.length,
    by
      have hbound :=
        (positiveCutSideIndex P cut horientation hl hr i).isLt
      omega⟩


-- @@ L232-244 verbatim
@[simp]
theorem positiveRightSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    (positiveRightSideIndex P cut horientation hl hr i hright).val =
      (positiveCutSideIndex P cut horientation hl hr i).val -
        cut.left.length :=
  rfl


-- @@ L246-264 verbatim
/-- In the left branch, the local cut-piece lookup is the stored source dart. -/
theorem left_get_positiveLeftSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    cut.left.get
        (positiveLeftSideIndex
          P cut horientation hl hr i hleft) =
      (P.boundary cut.face.face).get i := by
  change cut.left[
      (positiveCutSideIndex P cut horientation hl hr i).val] =
    (P.boundary cut.face.face)[i.val]
  rw [← cutBoundary_get_positiveCutSideIndex
    P cut horientation hl hr i]
  exact (List.getElem_append_left hleft).symm


-- @@ L266-290 verbatim
/-- In the right branch, the local cut-piece lookup is the stored source dart. -/
theorem right_get_positiveRightSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    cut.right.get
        (positiveRightSideIndex
          P cut horientation hl hr i hright) =
      (P.boundary cut.face.face).get i := by
  change cut.right[
      (positiveCutSideIndex P cut horientation hl hr i).val -
        cut.left.length] =
    (P.boundary cut.face.face)[i.val]
  rw [← cutBoundary_get_positiveCutSideIndex
    P cut horientation hl hr i]
  change cut.right[
      (positiveCutSideIndex P cut horientation hl hr i).val -
        cut.left.length] =
    (cut.left ++ cut.right)[
      (positiveCutSideIndex P cut horientation hl hr i).val]
  exact (List.getElem_append_right hright).symm


-- @@ L292-316 verbatim
/-- Exact selected-face computation for a side belonging to the left cut piece. -/
theorem positiveSelectedCellHomeomorph_side_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid cut.left.length cut.right.length)
        (.inl
          (PolygonCell.side
            (Fin.castAdd 1
              (positiveLeftSideIndex P cut horientation hl hr i hleft)) t)) := by
  rw [positiveSelectedCellHomeomorph_side]
  have hindex :
      positiveCutSideIndex P cut horientation hl hr i =
        Fin.castAdd cut.right.length
          (positiveLeftSideIndex P cut horientation hl hr i hleft) := by
    apply Fin.ext
    rfl
  rw [hindex, DiskSquare.sourceChildGluingHomeomorph_left_side]


-- @@ L318-342 verbatim
/-- Exact selected-face computation for a side belonging to the right cut piece. -/
theorem positiveSelectedCellHomeomorph_side_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid cut.left.length cut.right.length)
        (.inr
          (PolygonCell.side
            ((positiveRightSideIndex P cut horientation hl hr i hright).addNat 1) t)) := by
  rw [positiveSelectedCellHomeomorph_side]
  have hindex :
      positiveCutSideIndex P cut horientation hl hr i =
        Fin.natAdd cut.left.length
          (positiveRightSideIndex P cut horientation hl hr i hright) := by
    apply Fin.ext
    simp only [Fin.val_natAdd, positiveRightSideIndex_val]
    omega
  rw [hindex, DiskSquare.sourceChildGluingHomeomorph_right_side]


-- @@ L344-344 verbatim
/-! ### The fresh seam inside the actual split presentation -/


-- @@ L346-358 verbatim
theorem positive_split_boundary_selected_length
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    ((split P cut).boundary (oldFace P cut cut.face.face)).length =
      cut.left.length + 1 := by
  calc
    ((split P cut).boundary
        (oldFace P cut cut.face.face)).length =
        (selectedBoundary P cut).length :=
      congrArg List.length (split_boundary_selected P cut)
    _ = cut.left.length + 1 := by
      rw [selectedBoundary_of_orientation_false P cut horientation]
      simp [retainWord]


-- @@ L360-371 verbatim
theorem positive_split_boundary_right_length
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    ((split P cut).boundary (rightFace P cut)).length =
      cut.right.length + 1 := by
  calc
    ((split P cut).boundary (rightFace P cut)).length =
        (rightBoundary P cut).length :=
      congrArg List.length (split_boundary_right P cut)
    _ = cut.right.length + 1 := by
      rw [rightBoundary_of_orientation_false P cut horientation]
      simp [retainWord, Nat.add_comm]


-- @@ L373-381 verbatim
/-- Stored target index of the positive fresh dart in the selected child. -/
def positiveSelectedFreshIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Fin ((split P cut).boundary
      (oldFace P cut cut.face.face)).length :=
  ⟨cut.left.length, by
    rw [positive_split_boundary_selected_length P cut horientation]
    omega⟩


-- @@ L383-389 verbatim
@[simp]
theorem positiveSelectedFreshIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshIndex P cut horientation).val =
      cut.left.length :=
  rfl


-- @@ L391-398 verbatim
/-- Stored target index of the negative fresh dart in the right child. -/
def positiveRightFreshIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Fin ((split P cut).boundary (rightFace P cut)).length :=
  ⟨0, by
    rw [positive_split_boundary_right_length P cut horientation]
    omega⟩


-- @@ L400-405 verbatim
@[simp]
theorem positiveRightFreshIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshIndex P cut horientation).val = 0 :=
  rfl


-- @@ L407-413 verbatim
/-- The selected child's fresh-edge boundary occurrence. -/
def positiveSelectedFreshOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryOccurrence :=
  ⟨oldFace P cut cut.face.face,
    positiveSelectedFreshIndex P cut horientation⟩


-- @@ L415-420 verbatim
/-- The right child's fresh-edge boundary occurrence. -/
def positiveRightFreshOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryOccurrence :=
  ⟨rightFace P cut, positiveRightFreshIndex P cut horientation⟩


-- @@ L422-433 verbatim
theorem positiveSelectedBoundary_get_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (selectedBoundary P cut).get
        ⟨cut.left.length, by
          rw [selectedBoundary_of_orientation_false P cut horientation]
          unfold retainWord
          simp⟩ =
      .pos (freshEdge P) := by
  rw [List.get_of_eq
    (selectedBoundary_of_orientation_false P cut horientation)]
  simp [retainWord]


-- @@ L435-445 verbatim
theorem positiveRightBoundary_get_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (rightBoundary P cut).get
        ⟨0, by
          rw [rightBoundary_of_orientation_false P cut horientation]
          simp⟩ =
      .neg (freshEdge P) := by
  rw [List.get_of_eq
    (rightBoundary_of_orientation_false P cut horientation)]
  rfl


-- @@ L447-464 verbatim
@[simp]
theorem positiveSelectedFreshOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshOccurrence P cut horientation).dart =
      .pos (freshEdge P) := by
  rw [positiveSelectedFreshOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (split_boundary_selected P cut)]
  change
    (selectedBoundary P cut).get
        ⟨cut.left.length, by
          rw [selectedBoundary_of_orientation_false P cut horientation]
          unfold retainWord
          simp⟩ =
      (SignedDart.pos (freshEdge P) :
        SignedDart (Fin (P.edgeCount + 1)))
  simpa only [positiveSelectedFreshIndex_val] using
    positiveSelectedBoundary_get_fresh P cut horientation


-- @@ L466-482 verbatim
@[simp]
theorem positiveRightFreshOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshOccurrence P cut horientation).dart =
      .neg (freshEdge P) := by
  rw [positiveRightFreshOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (split_boundary_right P cut)]
  change
    (rightBoundary P cut).get
        ⟨0, by
          rw [rightBoundary_of_orientation_false P cut horientation]
          simp⟩ =
      (SignedDart.neg (freshEdge P) :
        SignedDart (Fin (P.edgeCount + 1)))
  simpa only [positiveRightFreshIndex_val] using
    positiveRightBoundary_get_fresh P cut horientation


-- @@ L484-492 verbatim
@[simp]
theorem positiveSelectedFreshOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshOccurrence P cut horientation).edge =
      freshEdge P := by
  rw [BoundaryOccurrence.edge,
    positiveSelectedFreshOccurrence_dart]
  rfl


-- @@ L494-502 verbatim
@[simp]
theorem positiveRightFreshOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshOccurrence P cut horientation).edge =
      freshEdge P := by
  rw [BoundaryOccurrence.edge,
    positiveRightFreshOccurrence_dart]
  rfl


-- @@ L504-513 verbatim
theorem positiveSelectedFreshOccurrence_ne_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    positiveSelectedFreshOccurrence P cut horientation ≠
      positiveRightFreshOccurrence P cut horientation := by
  intro h
  have hface := congrArg Sigma.fst h
  have hval := congrArg Fin.val hface
  change cut.face.face.val = P.faces.length at hval
  exact (Nat.ne_of_lt cut.face.face.isLt) hval


-- @@ L515-520 verbatim
theorem positiveFresh_not_boundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    ¬(split P cut).IsBoundaryEdge (freshEdge P) := by
  unfold IsBoundaryEdge
  rw [edgeMultiplicity_split_freshEdge]
  norm_num


-- @@ L522-541 verbatim
/-- The exact reversed-parameter pairing carried by the fresh P2 seam. -/
def positiveFreshPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryPairing where
  source := positiveSelectedFreshOccurrence P cut horientation
  target := positiveRightFreshOccurrence P cut horientation
  source_ne_target :=
    positiveSelectedFreshOccurrence_ne_right P cut horientation
  source_not_boundary := by
    rw [positiveSelectedFreshOccurrence_edge]
    exact positiveFresh_not_boundary P cut
  target_not_boundary := by
    rw [positiveRightFreshOccurrence_edge]
    exact positiveFresh_not_boundary P cut
  direction := .opposite
  compatible := by
    rw [positiveRightFreshOccurrence_dart,
      positiveSelectedFreshOccurrence_dart]
    rfl


-- @@ L543-549 verbatim
@[simp]
theorem positiveFreshPairing_source
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).source =
      positiveSelectedFreshOccurrence P cut horientation :=
  rfl


-- @@ L551-557 verbatim
@[simp]
theorem positiveFreshPairing_target
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).target =
      positiveRightFreshOccurrence P cut horientation :=
  rfl


-- @@ L559-564 verbatim
@[simp]
theorem positiveFreshPairing_direction
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).direction = .opposite :=
  rfl


-- @@ L566-566 verbatim
/-! ### Embedding the local child quotient in the target realization -/


-- @@ L568-577 verbatim
/-- Phantom side-count transport from the local selected child to the actual target face. -/
noncomputable def positiveSelectedChildCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell (cut.left.length + 1) ≃ₜ
      PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length :=
  PolygonCell.rotateHomeomorph
    (positive_split_boundary_selected_length P cut horientation).symm 0


-- @@ L579-586 verbatim
/-- Phantom side-count transport from the local right child to the actual target face. -/
noncomputable def positiveRightChildCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell (cut.right.length + 1) ≃ₜ
      PolygonCell ((split P cut).boundary (rightFace P cut)).length :=
  PolygonCell.rotateHomeomorph
    (positive_split_boundary_right_length P cut horientation).symm 0


-- @@ L588-597 verbatim
/-- The target selected-child index corresponding to a local child side. -/
def positiveSelectedChildSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.left.length + 1)) :
    Fin ((split P cut).boundary
      (oldFace P cut cut.face.face)).length :=
  ⟨i.val, by
    rw [positive_split_boundary_selected_length P cut horientation]
    exact i.isLt⟩


-- @@ L599-607 verbatim
/-- The target right-child index corresponding to a local child side. -/
def positiveRightChildSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.right.length + 1)) :
    Fin ((split P cut).boundary (rightFace P cut)).length :=
  ⟨i.val, by
    rw [positive_split_boundary_right_length P cut horientation]
    exact i.isLt⟩


-- @@ L609-634 verbatim
@[simp]
theorem positiveSelectedChildCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.left.length + 1)) (t : unitInterval) :
    positiveSelectedChildCellHomeomorph P cut horientation
        (PolygonCell.side i t) =
      PolygonCell.side
        (positiveSelectedChildSideIndex P cut horientation i) t := by
  rw [positiveSelectedChildCellHomeomorph]
  have hpos :
      0 <
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length := by
    rw [positive_split_boundary_selected_length P cut horientation]
    omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (positive_split_boundary_selected_length P cut horientation).symm
    hpos 0 i t]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk,
    positiveSelectedChildSideIndex]
  apply Nat.mod_eq_of_lt
  rw [positive_split_boundary_selected_length P cut horientation]
  simpa using i.isLt


-- @@ L636-659 verbatim
@[simp]
theorem positiveRightChildCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.right.length + 1)) (t : unitInterval) :
    positiveRightChildCellHomeomorph P cut horientation
        (PolygonCell.side i t) =
      PolygonCell.side
        (positiveRightChildSideIndex P cut horientation i) t := by
  rw [positiveRightChildCellHomeomorph]
  have hpos :
      0 < ((split P cut).boundary (rightFace P cut)).length := by
    rw [positive_split_boundary_right_length P cut horientation]
    omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (positive_split_boundary_right_length P cut horientation).symm
    hpos 0 i t]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk,
    positiveRightChildSideIndex]
  apply Nat.mod_eq_of_lt
  rw [positive_split_boundary_right_length P cut horientation]
  simpa using i.isLt


-- @@ L661-674 verbatim
/-- Include the two local child cells into the corresponding two faces of the split
pre-realization. -/
noncomputable def positiveChildPairPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    DiskSquare.ChildPair cut.left.length cut.right.length →
      (split P cut).PolygonalPreRealization :=
  Sum.elim
    (fun z =>
      ⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩)
    (fun z =>
      ⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩)


-- @@ L676-692 verbatim
theorem continuous_positiveChildPairPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Continuous (positiveChildPairPreMap P cut horientation) := by
  apply Continuous.sumElim
  · change Continuous (fun z =>
      (⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩ :
          (split P cut).PolygonalPreRealization))
    exact continuous_sigmaMk.comp
      (positiveSelectedChildCellHomeomorph P cut horientation).continuous
  · change Continuous (fun z =>
      (⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩ :
          (split P cut).PolygonalPreRealization))
    exact continuous_sigmaMk.comp
      (positiveRightChildCellHomeomorph P cut horientation).continuous


-- @@ L694-702 verbatim
@[simp]
theorem positiveChildPairPreMap_inl
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.left.length + 1)) :
    positiveChildPairPreMap P cut horientation (.inl z) =
      ⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩ :=
  rfl


-- @@ L704-712 verbatim
@[simp]
theorem positiveChildPairPreMap_inr
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.right.length + 1)) :
    positiveChildPairPreMap P cut horientation (.inr z) =
      ⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩ :=
  rfl


-- @@ L714-723 verbatim
/-- Send a local child point to its class in the complete split realization. -/
noncomputable def positiveChildPairMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ChildPair cut.left.length cut.right.length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  (split P cut).polygonalMk (split_isSurfaceValid P cut validP) ∘
    positiveChildPairPreMap P cut horientation


-- @@ L725-732 verbatim
theorem continuous_positiveChildPairMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveChildPairMap P cut horientation validP) :=
  ((split P cut).continuous_polygonalMk
      (split_isSurfaceValid P cut validP)).comp
    (continuous_positiveChildPairPreMap P cut horientation)


-- @@ L734-747 verbatim
theorem positiveChildPairPreMap_fresh_inl
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (t : unitInterval) :
    positiveChildPairPreMap P cut horientation
        (.inl (PolygonCell.side (Fin.last cut.left.length) t)) =
      ((split P cut).occurrenceSide
        (positiveSelectedFreshOccurrence P cut horientation)).point t := by
  rw [positiveChildPairPreMap_inl,
    positiveSelectedChildCellHomeomorph_side]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    congr 2


-- @@ L749-763 verbatim
theorem positiveChildPairPreMap_fresh_inr
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (t : unitInterval) :
    positiveChildPairPreMap P cut horientation
        (.inr
          (PolygonCell.side (0 : Fin (cut.right.length + 1)) t)) =
      ((split P cut).occurrenceSide
        (positiveRightFreshOccurrence P cut horientation)).point t := by
  rw [positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    congr 2


-- @@ L765-785 verbatim
/-- The local seam generator is exactly the fresh-edge gluing already present in the target
polygonal quotient. -/
theorem positiveChildPairMap_fresh_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    positiveChildPairMap P cut horientation validP
        (.inl (PolygonCell.side (Fin.last cut.left.length) t)) =
      positiveChildPairMap P cut horientation validP
        (.inr
          (PolygonCell.side (0 : Fin (cut.right.length + 1))
            (unitInterval.symm t))) := by
  simp only [positiveChildPairMap, Function.comp_apply]
  rw [positiveChildPairPreMap_fresh_inl,
    positiveChildPairPreMap_fresh_inr]
  simpa [positiveFreshPairing,
      PolygonGluing.Identification.parameter,
      PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (positiveFreshPairing P cut horientation) t


-- @@ L787-807 verbatim
/-- The target quotient map is constant on the complete local child-seam relation. -/
theorem positiveChildPairMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    {x y : DiskSquare.ChildPair cut.left.length cut.right.length}
    (hxy :
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator
          cut.left.length cut.right.length) x y) :
    positiveChildPairMap P cut horientation validP x =
      positiveChildPairMap P cut horientation validP y := by
  induction hxy with
  | rel _ _ h =>
      cases h with
      | glue t =>
          exact positiveChildPairMap_fresh_seam
            P cut horientation validP t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂


-- @@ L809-820 verbatim
/-- Include the locally glued pair of P2 children into the complete target realization. -/
noncomputable def positiveChildGluingMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ParamChildGluing cut.left.length cut.right.length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  Quotient.lift
    (positiveChildPairMap P cut horientation validP)
    (fun _ _ hxy =>
      positiveChildPairMap_respects P cut horientation validP hxy)


-- @@ L822-829 verbatim
theorem continuous_positiveChildGluingMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveChildGluingMap P cut horientation validP) :=
  (continuous_positiveChildPairMap P cut horientation validP).quotient_lift
    (fun _ _ hxy =>
      positiveChildPairMap_respects P cut horientation validP hxy)


-- @@ L831-843 verbatim
@[simp]
theorem positiveChildGluingMap_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    (x : DiskSquare.ChildPair cut.left.length cut.right.length) :
    positiveChildGluingMap P cut horientation validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length) x) =
      positiveChildPairMap P cut horientation validP x :=
  rfl


-- @@ L845-845 verbatim
/-! ### The selected source face as a map into the split realization -/


-- @@ L847-858 verbatim
/-- The positive, nondegenerate selected source face, cut into the two target children and then
included in the complete split quotient. -/
noncomputable def positiveSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary cut.face.face).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  positiveChildGluingMap P cut horientation validP ∘
    positiveSelectedCellHomeomorph P cut horientation hl hr


-- @@ L860-870 verbatim
theorem continuous_positiveSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous
      (positiveSelectedFaceMap
        P cut horientation hl hr validP) :=
  (continuous_positiveChildGluingMap P cut horientation validP).comp
    (positiveSelectedCellHomeomorph
      P cut horientation hl hr).continuous


-- @@ L872-898 verbatim
/-- A selected source side in the left cut piece lands on the exact old side of the selected
target child. -/
theorem positiveSelectedFaceMap_side_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveSelectedFaceMap P cut horientation hl hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut cut.face.face,
          PolygonCell.side
            (positiveSelectedChildSideIndex P cut horientation
              (Fin.castAdd 1
                (positiveLeftSideIndex
                  P cut horientation hl hr i hleft))) t⟩ := by
  rw [positiveSelectedFaceMap, Function.comp_apply,
    positiveSelectedCellHomeomorph_side_of_lt
      P cut horientation hl hr i t hleft]
  rw [positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inl,
    positiveSelectedChildCellHomeomorph_side]


-- @@ L900-925 verbatim
/-- A selected source side in the right cut piece lands on the exact old side of the right target
child. -/
theorem positiveSelectedFaceMap_side_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    positiveSelectedFaceMap P cut horientation hl hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((positiveRightSideIndex
                P cut horientation hl hr i hright).addNat 1)) t⟩ := by
  rw [positiveSelectedFaceMap, Function.comp_apply,
    positiveSelectedCellHomeomorph_side_of_not_lt
      P cut horientation hl hr i t hright]
  rw [positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]


-- @@ L927-927 verbatim
/-! ### The complete forward pre-realization map -/


-- @@ L929-940 verbatim
theorem split_boundary_old_length_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    ((split P cut).boundary (oldFace P cut f)).length =
      (P.boundary f).length := by
  calc
    ((split P cut).boundary (oldFace P cut f)).length =
        (retainWord (P.boundary f)).length :=
      congrArg List.length
        (split_boundary_old_of_ne P cut hface)
    _ = (P.boundary f).length := by
      simp [retainWord]


-- @@ L942-950 verbatim
/-- A retained source face differs from its target copy only by a phantom side-count equality. -/
noncomputable def retainedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell
        ((split P cut).boundary (oldFace P cut f)).length :=
  PolygonCell.rotateHomeomorph
    (split_boundary_old_length_of_ne P cut hface).symm 0


-- @@ L952-960 verbatim
/-- Target index corresponding to a side of a retained source face. -/
def retainedSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) :
    Fin ((split P cut).boundary (oldFace P cut f)).length :=
  ⟨i.val, by
    rw [split_boundary_old_length_of_ne P cut hface]
    exact i.isLt⟩


-- @@ L962-982 verbatim
@[simp]
theorem retainedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    retainedCellHomeomorph P cut hface (PolygonCell.side i t) =
      PolygonCell.side (retainedSideIndex P cut hface i) t := by
  rw [retainedCellHomeomorph]
  have hpos :
      0 < ((split P cut).boundary (oldFace P cut f)).length := by
    rw [split_boundary_old_length_of_ne P cut hface]
    exact Nat.zero_lt_of_lt i.isLt
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (split_boundary_old_length_of_ne P cut hface).symm
    hpos 0 i t]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk, retainedSideIndex]
  apply Nat.mod_eq_of_lt
  rw [split_boundary_old_length_of_ne P cut hface]
  exact i.isLt


-- @@ L984-994 verbatim
/-- A retained face maps directly to its unchanged target face class. -/
noncomputable def retainedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary f).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  fun z =>
    (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
      ⟨oldFace P cut f, retainedCellHomeomorph P cut hface z⟩


-- @@ L996-1004 verbatim
theorem continuous_retainedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (validP : P.IsSurfaceValid) :
    Continuous (retainedFaceMap P cut hface validP) :=
  ((split P cut).continuous_polygonalMk
      (split_isSurfaceValid P cut validP)).comp
    (continuous_sigmaMk.comp
      (retainedCellHomeomorph P cut hface).continuous)


-- @@ L1006-1020 verbatim
/-- Facewise forward map: cut the selected face and retain every other face. -/
noncomputable def positiveFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact positiveSelectedFaceMap
      P cut horientation hl hr validP
  · exact retainedFaceMap P cut hface validP


-- @@ L1022-1036 verbatim
theorem continuous_positiveFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (positiveFaceMap
      P cut horientation hl hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [positiveFaceMap] using
      continuous_positiveSelectedFaceMap
        P cut horientation hl hr validP
  · simpa [positiveFaceMap, hface] using
      continuous_retainedFaceMap P cut hface validP


-- @@ L1038-1048 verbatim
/-- Continuous forward map on the entire source polygonal pre-realization. -/
noncomputable def positivePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  fun x => positiveFaceMap
    P cut horientation hl hr validP x.1 x.2


-- @@ L1050-1059 verbatim
theorem continuous_positivePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (positivePreMap
      P cut horientation hl hr validP) := by
  apply continuous_sigma
  exact continuous_positiveFaceMap
    P cut horientation hl hr validP


-- @@ L1061-1072 verbatim
@[simp]
theorem positivePreMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    positivePreMap P cut horientation hl hr validP
        ⟨cut.face.face, z⟩ =
      positiveSelectedFaceMap
        P cut horientation hl hr validP z := by
  simp [positivePreMap, positiveFaceMap]


-- @@ L1074-1084 verbatim
@[simp]
theorem positivePreMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    positivePreMap P cut horientation hl hr validP ⟨f, z⟩ =
      retainedFaceMap P cut hface validP z := by
  simp [positivePreMap, positiveFaceMap, hface]


-- @@ L1086-1106 verbatim
theorem positivePreMap_selected_side_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positivePreMap P cut horientation hl hr validP
        ⟨cut.face.face, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut cut.face.face,
          PolygonCell.side
            (positiveSelectedChildSideIndex P cut horientation
              (Fin.castAdd 1
                (positiveLeftSideIndex
                  P cut horientation hl hr i hleft))) t⟩ := by
  rw [positivePreMap_selected,
    positiveSelectedFaceMap_side_of_lt
      P cut horientation hl hr validP i t hleft]


-- @@ L1108-1127 verbatim
theorem positivePreMap_selected_side_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    positivePreMap P cut horientation hl hr validP
        ⟨cut.face.face, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((positiveRightSideIndex
                P cut horientation hl hr i hright).addNat 1)) t⟩ := by
  rw [positivePreMap_selected,
    positiveSelectedFaceMap_side_of_not_lt
      P cut horientation hl hr validP i t hright]


-- @@ L1129-1144 verbatim
theorem positivePreMap_retained_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    positivePreMap P cut horientation hl hr validP
        ⟨f, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut f,
          PolygonCell.side
            (retainedSideIndex P cut hface i) t⟩ := by
  rw [positivePreMap_retained
      P cut horientation hl hr validP hface,
    retainedFaceMap, retainedCellHomeomorph_side]


-- @@ L1146-1153 verbatim
theorem oldFace_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Function.Injective (oldFace P cut) := by
  intro f g hfg
  have hcast :
      f.castSucc = g.castSucc :=
    (faceEquiv P cut).injective hfg
  exact Fin.castSucc_injective _ hcast


-- @@ L1155-1164 verbatim
theorem oldFace_ne_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (f : P.Face) :
    oldFace P cut f ≠ rightFace P cut := by
  intro h
  have hindex :
      f.castSucc = Fin.last P.faces.length :=
    (faceEquiv P cut).injective h
  have hval := congrArg Fin.val hindex
  exact (Nat.ne_of_lt f.isLt) hval


-- @@ L1166-1194 verbatim
/-- Transport a source boundary occurrence to the child or retained target face that carries the
same old edge after a positive nondegenerate split. -/
noncomputable def positiveMapOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (split P cut).BoundaryOccurrence := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    by_cases hleft :
        (positiveCutSideIndex
          P cut horientation hl hr i).val < cut.left.length
    · exact
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildSideIndex P cut horientation
            (Fin.castAdd 1
              (positiveLeftSideIndex
                P cut horientation hl hr i hleft))⟩
    · exact
        ⟨rightFace P cut,
          positiveRightChildSideIndex P cut horientation
            ((positiveRightSideIndex
              P cut horientation hl hr i
                (Nat.le_of_not_gt hleft)).addNat 1)⟩
  · exact
      ⟨oldFace P cut f, retainedSideIndex P cut hface i⟩


-- @@ L1196-1215 verbatim
theorem positiveMapOccurrence_selected_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveMapOccurrence P cut horientation hl hr
        ⟨cut.face.face, i⟩ =
      ⟨oldFace P cut cut.face.face,
        positiveSelectedChildSideIndex P cut horientation
          (Fin.castAdd 1
            (positiveLeftSideIndex
              P cut horientation hl hr i hleft))⟩ := by
  change
    (i.val + positiveCutRotation P cut horientation) %
        (cut.left.length + cut.right.length) <
      cut.left.length at hleft
  simp [positiveMapOccurrence, hleft]


-- @@ L1217-1236 verbatim
theorem positiveMapOccurrence_selected_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      ¬(positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveMapOccurrence P cut horientation hl hr
        ⟨cut.face.face, i⟩ =
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((positiveRightSideIndex
            P cut horientation hl hr i
              (Nat.le_of_not_gt hleft)).addNat 1)⟩ := by
  change
    ¬(i.val + positiveCutRotation P cut horientation) %
        (cut.left.length + cut.right.length) <
      cut.left.length at hleft
  simp [positiveMapOccurrence, hleft]


-- @@ L1238-1246 verbatim
theorem positiveMapOccurrence_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) :
    positiveMapOccurrence P cut horientation hl hr ⟨f, i⟩ =
      ⟨oldFace P cut f, retainedSideIndex P cut hface i⟩ := by
  simp [positiveMapOccurrence, hface]


-- @@ L1248-1291 verbatim
/-- Exact side-point computation for the complete forward occurrence transport. -/
theorem positivePreMap_occurrenceSide
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    positivePreMap P cut horientation hl hr validP
        ((P.occurrenceSide o).point t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        (((split P cut).occurrenceSide
          (positiveMapOccurrence
            P cut horientation hl hr o)).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    by_cases hleft :
        (positiveCutSideIndex
          P cut horientation hl hr i).val < cut.left.length
    · rw [positiveMapOccurrence_selected_of_lt
        P cut horientation hl hr i hleft]
      simp only [occurrenceSide, PolygonGluing.Side.point]
      convert
        positivePreMap_selected_side_of_lt
          P cut horientation hl hr validP i t hleft using 1
    · have hright :
          cut.left.length ≤
            (positiveCutSideIndex
              P cut horientation hl hr i).val :=
        Nat.le_of_not_gt hleft
      rw [positiveMapOccurrence_selected_of_not_lt
        P cut horientation hl hr i hleft]
      simp only [occurrenceSide, PolygonGluing.Side.point]
      convert
        positivePreMap_selected_side_of_not_lt
          P cut horientation hl hr validP i t hright using 1
  · rw [positiveMapOccurrence_retained
      P cut horientation hl hr hface i]
    simp only [occurrenceSide, PolygonGluing.Side.point]
    convert
      positivePreMap_retained_side
        P cut horientation hl hr validP hface i t using 1


-- @@ L1293-1427 verbatim
/-- The transported occurrence carries exactly the retained old dart. -/
theorem positiveMapOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (positiveMapOccurrence
        P cut horientation hl hr o).dart =
      P1.castSuccDart o.dart := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    by_cases hleft :
        (positiveCutSideIndex
          P cut horientation hl hr i).val < cut.left.length
    · rw [positiveMapOccurrence_selected_of_lt
        P cut horientation hl hr i hleft,
        BoundaryOccurrence.dart_mk]
      rw [List.get_of_eq (split_boundary_selected P cut)]
      change
        (selectedBoundary P cut).get
            ⟨(positiveLeftSideIndex
                P cut horientation hl hr i hleft).val,
              by
                rw [selectedBoundary_of_orientation_false
                  P cut horientation]
                simp only [retainWord, List.length_map,
                  positiveLeftSideIndex_val,
                  positiveCutSideIndex_val, List.length_append,
                  List.length_cons, List.length_nil, zero_add,
                  Order.lt_add_one_iff]
                have hlocal := (positiveLeftSideIndex
                  P cut horientation hl hr i hleft).isLt
                exact Nat.le_of_lt (by
                  simpa only [positiveLeftSideIndex_val,
                    positiveCutSideIndex_val] using hlocal)⟩ =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      rw [List.get_of_eq
        (selectedBoundary_of_orientation_false
          P cut horientation)]
      change
        (retainWord cut.left ++ [.pos (freshEdge P)])[
            (positiveLeftSideIndex
              P cut horientation hl hr i hleft).val]'(by
                simp only [retainWord, List.length_map,
                  positiveLeftSideIndex_val,
                  positiveCutSideIndex_val, List.length_append,
                  List.length_cons, List.length_nil, zero_add,
                  Order.lt_add_one_iff]
                have hlocal := (positiveLeftSideIndex
                  P cut horientation hl hr i hleft).isLt
                exact Nat.le_of_lt (by
                  simpa only [positiveLeftSideIndex_val,
                    positiveCutSideIndex_val] using hlocal)) =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      have hretain :
          (positiveLeftSideIndex
              P cut horientation hl hr i hleft).val <
            (retainWord cut.left).length := by
        unfold retainWord
        simpa using
          (positiveLeftSideIndex
            P cut horientation hl hr i hleft).isLt
      rw [List.getElem_append_left hretain]
      have hmap :
            (positiveLeftSideIndex
              P cut horientation hl hr i hleft).val <
            (List.map P1.castSuccDart cut.left).length := by
        simpa using
          (positiveLeftSideIndex
            P cut horientation hl hr i hleft).isLt
      change
        (List.map P1.castSuccDart cut.left)[
            (positiveLeftSideIndex
              P cut horientation hl hr i hleft).val]'hmap =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      simp only [List.getElem_map]
      exact congrArg P1.castSuccDart
        (left_get_positiveLeftSideIndex
          P cut horientation hl hr i hleft)
    · have hright :
          cut.left.length ≤
            (positiveCutSideIndex
              P cut horientation hl hr i).val :=
        Nat.le_of_not_gt hleft
      rw [positiveMapOccurrence_selected_of_not_lt
        P cut horientation hl hr i hleft,
        BoundaryOccurrence.dart_mk]
      rw [List.get_of_eq (split_boundary_right P cut)]
      change
        (rightBoundary P cut).get
            ⟨(positiveRightSideIndex
                P cut horientation hl hr i hright).val + 1,
              by
                rw [rightBoundary_of_orientation_false
                  P cut horientation]
                simp [retainWord, Nat.add_comm]
                have hlocal := (positiveRightSideIndex
                  P cut horientation hl hr i hright).isLt
                simpa only [positiveRightSideIndex_val,
                  positiveCutSideIndex_val] using hlocal⟩ =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      rw [List.get_of_eq
        (rightBoundary_of_orientation_false
          P cut horientation)]
      change
        (.neg (freshEdge P) :: retainWord cut.right)[
            (positiveRightSideIndex
              P cut horientation hl hr i hright).val + 1]'(by
                simp [retainWord]
                have hlocal := (positiveRightSideIndex
                  P cut horientation hl hr i hright).isLt
                simpa only [positiveRightSideIndex_val,
                  positiveCutSideIndex_val] using hlocal) =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      rw [List.getElem_cons_succ]
      change
        (List.map P1.castSuccDart cut.right)[
            (positiveRightSideIndex
              P cut horientation hl hr i hright).val] =
          P1.castSuccDart ((P.boundary cut.face.face)[i.val])
      rw [List.getElem_map]
      exact congrArg P1.castSuccDart
        (right_get_positiveRightSideIndex
          P cut horientation hl hr i hright)
  · rw [positiveMapOccurrence_retained
      P cut horientation hl hr hface i,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq
      (split_boundary_old_of_ne P cut hface)]
    change
      (List.map P1.castSuccDart (P.boundary f))[i.val] =
        P1.castSuccDart ((P.boundary f)[i.val])
    rw [List.getElem_map]


-- @@ L1429-1441 verbatim
theorem positiveMapOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (positiveMapOccurrence
        P cut horientation hl hr o).edge =
      o.edge.castSucc := by
  rw [BoundaryOccurrence.edge,
    positiveMapOccurrence_dart]
  change edgeOfDart (P1.castSuccDart o.dart) =
    (edgeOfDart o.dart).castSucc
  exact P1.edgeOfDart_castSuccDart o.dart


-- @@ L1443-1573 verbatim
/-- Distinct source boundary positions remain distinct after routing the selected face between its
two P2 children. -/
theorem positiveMapOccurrence_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length) :
    Function.Injective
      (positiveMapOccurrence P cut horientation hl hr) := by
  classical
  rintro ⟨f, i⟩ ⟨g, j⟩ hmap
  by_cases hf : f = cut.face.face
  · subst f
    by_cases hg : g = cut.face.face
    · subst g
      by_cases hi :
          (positiveCutSideIndex
            P cut horientation hl hr i).val < cut.left.length
      · by_cases hj :
          (positiveCutSideIndex
            P cut horientation hl hr j).val < cut.left.length
        · rw [positiveMapOccurrence_selected_of_lt
              P cut horientation hl hr i hi,
            positiveMapOccurrence_selected_of_lt
              P cut horientation hl hr j hj] at hmap
          have hval := congrArg
            (fun o : (split P cut).BoundaryOccurrence => o.2.val) hmap
          have hindex :
              positiveCutSideIndex P cut horientation hl hr i =
                positiveCutSideIndex P cut horientation hl hr j := by
            apply Fin.ext
            simpa [positiveSelectedChildSideIndex,
              positiveLeftSideIndex] using hval
          have hij :=
            positiveCutSideIndex_injective
              P cut horientation hl hr hindex
          subst j
          rfl
        · rw [positiveMapOccurrence_selected_of_lt
              P cut horientation hl hr i hi,
            positiveMapOccurrence_selected_of_not_lt
              P cut horientation hl hr j hj] at hmap
          exact (oldFace_ne_rightFace P cut cut.face.face
            (congrArg Sigma.fst hmap)).elim
      · by_cases hj :
          (positiveCutSideIndex
            P cut horientation hl hr j).val < cut.left.length
        · rw [positiveMapOccurrence_selected_of_not_lt
              P cut horientation hl hr i hi,
            positiveMapOccurrence_selected_of_lt
              P cut horientation hl hr j hj] at hmap
          exact (oldFace_ne_rightFace P cut cut.face.face
            (congrArg Sigma.fst hmap).symm).elim
        · rw [positiveMapOccurrence_selected_of_not_lt
              P cut horientation hl hr i hi,
            positiveMapOccurrence_selected_of_not_lt
              P cut horientation hl hr j hj] at hmap
          have hval := congrArg
            (fun o : (split P cut).BoundaryOccurrence => o.2.val) hmap
          have hiright :
              cut.left.length ≤
                (positiveCutSideIndex
                  P cut horientation hl hr i).val :=
            Nat.le_of_not_gt hi
          have hjright :
              cut.left.length ≤
                (positiveCutSideIndex
                  P cut horientation hl hr j).val :=
            Nat.le_of_not_gt hj
          have hindex :
              positiveCutSideIndex P cut horientation hl hr i =
                positiveCutSideIndex P cut horientation hl hr j := by
            apply Fin.ext
            simp only [positiveRightChildSideIndex,
              Fin.val_addNat, positiveRightSideIndex_val] at hval
            omega
          have hij :=
            positiveCutSideIndex_injective
              P cut horientation hl hr hindex
          subst j
          rfl
    · by_cases hi :
        (positiveCutSideIndex
          P cut horientation hl hr i).val < cut.left.length
      · rw [positiveMapOccurrence_selected_of_lt
            P cut horientation hl hr i hi,
          positiveMapOccurrence_retained
            P cut horientation hl hr hg j] at hmap
        have hface :
            cut.face.face = g :=
          oldFace_injective P cut (congrArg Sigma.fst hmap)
        exact (hg hface.symm).elim
      · rw [positiveMapOccurrence_selected_of_not_lt
            P cut horientation hl hr i hi,
          positiveMapOccurrence_retained
            P cut horientation hl hr hg j] at hmap
        exact (oldFace_ne_rightFace P cut g
          (congrArg Sigma.fst hmap).symm).elim
  · by_cases hg : g = cut.face.face
    · subst g
      by_cases hj :
          (positiveCutSideIndex
            P cut horientation hl hr j).val < cut.left.length
      · rw [positiveMapOccurrence_retained
            P cut horientation hl hr hf i,
          positiveMapOccurrence_selected_of_lt
            P cut horientation hl hr j hj] at hmap
        have hface :
            f = cut.face.face :=
          oldFace_injective P cut (congrArg Sigma.fst hmap)
        exact (hf hface).elim
      · rw [positiveMapOccurrence_retained
            P cut horientation hl hr hf i,
          positiveMapOccurrence_selected_of_not_lt
            P cut horientation hl hr j hj] at hmap
        exact (oldFace_ne_rightFace P cut f
          (congrArg Sigma.fst hmap)).elim
    · rw [positiveMapOccurrence_retained
          P cut horientation hl hr hf i,
        positiveMapOccurrence_retained
          P cut horientation hl hr hg j] at hmap
      have hface :
          f = g :=
        oldFace_injective P cut (congrArg Sigma.fst hmap)
      subst g
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence => o.2.val) hmap
      have hij : i = j := by
        apply Fin.ext
        simpa [retainedSideIndex] using hval
      subst j
      rfl


-- @@ L1575-1638 verbatim
/-- Transport an old-edge source pairing to the corresponding pairing of target occurrences. -/
noncomputable def positiveMapPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (split P cut).BoundaryPairing where
  source :=
    positiveMapOccurrence
      P cut horientation hl hr pairing.source
  target :=
    positiveMapOccurrence
      P cut horientation hl hr pairing.target
  source_ne_target := by
    intro h
    exact pairing.source_ne_target
      (positiveMapOccurrence_injective
        P cut horientation hl hr h)
  source_not_boundary := by
    rw [positiveMapOccurrence_edge]
    intro hboundary
    apply pairing.source_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  target_not_boundary := by
    rw [positiveMapOccurrence_edge]
    intro hboundary
    apply pairing.target_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction with
    | same =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (positiveMapOccurrence
            P cut horientation hl hr pairing.target).dart =
          (positiveMapOccurrence
            P cut horientation hl hr pairing.source).dart
        rw [positiveMapOccurrence_dart,
          positiveMapOccurrence_dart]
        change
          P1.castSuccDart pairing.target.dart =
            P1.castSuccDart pairing.source.dart
        exact congrArg P1.castSuccDart hcompatible
    | opposite =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (positiveMapOccurrence
            P cut horientation hl hr pairing.target).dart =
          (positiveMapOccurrence
            P cut horientation hl hr pairing.source).dart.flip
        rw [positiveMapOccurrence_dart,
          positiveMapOccurrence_dart]
        change
          P1.castSuccDart pairing.target.dart =
            (P1.castSuccDart pairing.source.dart).flip
        rw [← P2.castSuccDart_flip]
        exact congrArg P1.castSuccDart hcompatible


-- @@ L1640-1650 verbatim
@[simp]
theorem positiveMapPairing_source
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (positiveMapPairing
      P cut horientation hl hr pairing).source =
      positiveMapOccurrence
        P cut horientation hl hr pairing.source :=
  rfl


-- @@ L1652-1662 verbatim
@[simp]
theorem positiveMapPairing_target
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (positiveMapPairing
      P cut horientation hl hr pairing).target =
      positiveMapOccurrence
        P cut horientation hl hr pairing.target :=
  rfl


-- @@ L1664-1673 verbatim
@[simp]
theorem positiveMapPairing_direction
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (positiveMapPairing
      P cut horientation hl hr pairing).direction =
      pairing.direction :=
  rfl


-- @@ L1675-1696 verbatim
/-- Every source gluing generator has equal images under the complete forward P2 map. -/
theorem positivePreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    positivePreMap P cut horientation hl hr validP
        (pairing.identification.source.point t) =
      positivePreMap P cut horientation hl hr validP
        (pairing.identification.target.point
          (pairing.identification.parameter t)) := by
  rw [BoundaryPairing.identification_source,
    BoundaryPairing.identification_target,
    positivePreMap_occurrenceSide,
    positivePreMap_occurrenceSide]
  simpa [positiveMapPairing,
      PolygonGluing.Identification.parameter] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (positiveMapPairing
        P cut horientation hl hr pairing) t


-- @@ L1698-1720 verbatim
/-- The forward pre-map is constant on the complete source gluing relation. -/
theorem positivePreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    positivePreMap P cut horientation hl hr validP x =
      positivePreMap P cut horientation hl hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact positivePreMap_pairing_eq
            P cut horientation hl hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂


-- @@ L1722-1722 verbatim
/-! ### Local inverse maps for the two target children -/


-- @@ L1724-1736 verbatim
/-- Collapse the local child quotient back to the selected source face class. -/
noncomputable def positiveChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ParamChildGluing cut.left.length cut.right.length →
      P.PolygonalRealization validP :=
  fun q =>
    P.polygonalMk validP
      ⟨cut.face.face,
        (positiveSelectedCellHomeomorph
          P cut horientation hl hr).symm q⟩


-- @@ L1738-1748 verbatim
theorem continuous_positiveChildGluingInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveChildGluingInvMap
      P cut horientation hl hr validP) :=
  (P.continuous_polygonalMk validP).comp
    (continuous_sigmaMk.comp
      (positiveSelectedCellHomeomorph
        P cut horientation hl hr).symm.continuous)


-- @@ L1750-1762 verbatim
@[simp]
theorem positiveChildGluingInvMap_selectedCell
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    positiveChildGluingInvMap
        P cut horientation hl hr validP
        (positiveSelectedCellHomeomorph
          P cut horientation hl hr z) =
      P.polygonalMk validP ⟨cut.face.face, z⟩ := by
  simp [positiveChildGluingInvMap]


-- @@ L1764-1780 verbatim
/-- Include a point of the actual selected target child into the local child quotient. -/
noncomputable def positiveSelectedChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length →
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  fun z =>
    @Quotient.mk''
      (DiskSquare.ChildPair cut.left.length cut.right.length)
      (DiskSquare.paramChildSeamSetoid
        cut.left.length cut.right.length)
      (.inl
        ((positiveSelectedChildCellHomeomorph
          P cut horientation).symm z))


-- @@ L1782-1790 verbatim
theorem continuous_positiveSelectedChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Continuous
      (positiveSelectedChildToGluing P cut horientation) :=
  continuous_quotient_mk'.comp
    (continuous_inl.comp
      (positiveSelectedChildCellHomeomorph
        P cut horientation).symm.continuous)


-- @@ L1792-1807 verbatim
/-- Include a point of the actual right target child into the local child quotient. -/
noncomputable def positiveRightChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell
        ((split P cut).boundary (rightFace P cut)).length →
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  fun z =>
    @Quotient.mk''
      (DiskSquare.ChildPair cut.left.length cut.right.length)
      (DiskSquare.paramChildSeamSetoid
        cut.left.length cut.right.length)
      (.inr
        ((positiveRightChildCellHomeomorph
          P cut horientation).symm z))


-- @@ L1809-1817 verbatim
theorem continuous_positiveRightChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Continuous
      (positiveRightChildToGluing P cut horientation) :=
  continuous_quotient_mk'.comp
    (continuous_inr.comp
      (positiveRightChildCellHomeomorph
        P cut horientation).symm.continuous)


-- @@ L1819-1832 verbatim
@[simp]
theorem positiveSelectedChildToGluing_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.left.length + 1)) :
    positiveSelectedChildToGluing P cut horientation
        (positiveSelectedChildCellHomeomorph
          P cut horientation z) =
      @Quotient.mk''
        (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid
          cut.left.length cut.right.length)
        (.inl z) := by
  simp [positiveSelectedChildToGluing]


-- @@ L1834-1847 verbatim
@[simp]
theorem positiveRightChildToGluing_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.right.length + 1)) :
    positiveRightChildToGluing P cut horientation
        (positiveRightChildCellHomeomorph
          P cut horientation z) =
      @Quotient.mk''
        (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid
          cut.left.length cut.right.length)
        (.inr z) := by
  simp [positiveRightChildToGluing]


-- @@ L1849-1861 verbatim
/-- Inverse map on the selected target child. -/
noncomputable def positiveSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length →
      P.PolygonalRealization validP :=
  positiveChildGluingInvMap
      P cut horientation hl hr validP ∘
    positiveSelectedChildToGluing P cut horientation


-- @@ L1863-1873 verbatim
theorem continuous_positiveSelectedChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveSelectedChildInvFaceMap
      P cut horientation hl hr validP) :=
  (continuous_positiveChildGluingInvMap
      P cut horientation hl hr validP).comp
    (continuous_positiveSelectedChildToGluing
      P cut horientation)


-- @@ L1875-1886 verbatim
/-- Inverse map on the right target child. -/
noncomputable def positiveRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary (rightFace P cut)).length →
      P.PolygonalRealization validP :=
  positiveChildGluingInvMap
      P cut horientation hl hr validP ∘
    positiveRightChildToGluing P cut horientation


-- @@ L1888-1898 verbatim
theorem continuous_positiveRightChildInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveRightChildInvFaceMap
      P cut horientation hl hr validP) :=
  (continuous_positiveChildGluingInvMap
      P cut horientation hl hr validP).comp
    (continuous_positiveRightChildToGluing
      P cut horientation)


-- @@ L1900-1910 verbatim
/-- Inverse map on a retained target face. -/
noncomputable def retainedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (validP : P.IsSurfaceValid) :
    PolygonCell
        ((split P cut).boundary (oldFace P cut f)).length →
      P.PolygonalRealization validP :=
  fun z =>
    P.polygonalMk validP
      ⟨f, (retainedCellHomeomorph P cut hface).symm z⟩


-- @@ L1912-1919 verbatim
theorem continuous_retainedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (validP : P.IsSurfaceValid) :
    Continuous (retainedInvFaceMap P cut hface validP) :=
  (P.continuous_polygonalMk validP).comp
    (continuous_sigmaMk.comp
      (retainedCellHomeomorph P cut hface).symm.continuous)


-- @@ L1921-1930 verbatim
@[simp]
theorem retainedInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary f).length) :
    retainedInvFaceMap P cut hface validP
        (retainedCellHomeomorph P cut hface z) =
      P.polygonalMk validP ⟨f, z⟩ := by
  simp [retainedInvFaceMap]


-- @@ L1932-1947 verbatim
/-- Inverse map at an old target-face position, selecting the cut-child inverse exactly at the
chosen source face. -/
noncomputable def positiveOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell
        ((split P cut).boundary (oldFace P cut f)).length →
      P.PolygonalRealization validP := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact positiveSelectedChildInvFaceMap
      P cut horientation hl hr validP
  · exact retainedInvFaceMap P cut hface validP


-- @@ L1949-1963 verbatim
theorem continuous_positiveOldInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (positiveOldInvFaceMap
      P cut horientation hl hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [positiveOldInvFaceMap] using
      continuous_positiveSelectedChildInvFaceMap
        P cut horientation hl hr validP
  · simpa [positiveOldInvFaceMap, hface] using
      continuous_retainedInvFaceMap P cut hface validP


-- @@ L1965-1981 verbatim
/-- Inverse face map indexed before applying the explicit target `faceEquiv`. -/
noncomputable def positiveIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    PolygonCell
        ((split P cut).boundary (faceEquiv P cut j)).length →
      P.PolygonalRealization validP :=
  Fin.lastCases
    (positiveRightChildInvFaceMap
      P cut horientation hl hr validP)
    (fun f =>
      positiveOldInvFaceMap
        P cut horientation hl hr validP f)
    j


-- @@ L1983-1993 verbatim
@[simp]
theorem positiveIndexedInvFaceMap_last
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    positiveIndexedInvFaceMap
        P cut horientation hl hr validP (Fin.last P.faces.length) =
      positiveRightChildInvFaceMap
        P cut horientation hl hr validP :=
  Fin.lastCases_last


-- @@ L1995-2005 verbatim
@[simp]
theorem positiveIndexedInvFaceMap_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    positiveIndexedInvFaceMap
        P cut horientation hl hr validP f.castSucc =
      positiveOldInvFaceMap
        P cut horientation hl hr validP f :=
  Fin.lastCases_castSucc f


-- @@ L2007-2023 verbatim
theorem continuous_positiveIndexedInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (j : Fin (P.faces.length + 1)) :
    Continuous (positiveIndexedInvFaceMap
      P cut horientation hl hr validP j) := by
  induction j using Fin.lastCases with
  | last =>
      rw [positiveIndexedInvFaceMap_last]
      exact continuous_positiveRightChildInvFaceMap
        P cut horientation hl hr validP
  | cast f =>
      rw [positiveIndexedInvFaceMap_castSucc]
      exact continuous_positiveOldInvFaceMap
        P cut horientation hl hr validP f


-- @@ L2025-2038 verbatim
/-- Inverse face map on the actual target face type. -/
noncomputable def positiveInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    PolygonCell ((split P cut).boundary q).length →
      P.PolygonalRealization validP := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  exact hq ▸ positiveIndexedInvFaceMap
    P cut horientation hl hr validP j


-- @@ L2040-2055 verbatim
theorem continuous_positiveInvFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).Face) :
    Continuous (positiveInvFaceMap
      P cut horientation hl hr validP q) := by
  let j := (faceEquiv P cut).symm q
  have hq : faceEquiv P cut j = q :=
    (faceEquiv P cut).apply_symm_apply q
  change Continuous (hq ▸ positiveIndexedInvFaceMap
    P cut horientation hl hr validP j)
  cases hq
  exact continuous_positiveIndexedInvFaceMap
    P cut horientation hl hr validP j


-- @@ L2057-2074 verbatim
@[simp]
theorem positiveInvFaceMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    positiveInvFaceMap P cut horientation hl hr validP
        (oldFace P cut f) =
      positiveOldInvFaceMap
        P cut horientation hl hr validP f := by
  unfold positiveInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (oldFace P cut f) = f.castSucc :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact positiveIndexedInvFaceMap_castSucc
    P cut horientation hl hr validP f


-- @@ L2076-2094 verbatim
@[simp]
theorem positiveInvFaceMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    positiveInvFaceMap P cut horientation hl hr validP
        (rightFace P cut) =
      positiveRightChildInvFaceMap
        P cut horientation hl hr validP := by
  unfold positiveInvFaceMap
  dsimp only
  have hj :
      (faceEquiv P cut).symm (rightFace P cut) =
        Fin.last P.faces.length :=
    (faceEquiv P cut).symm_apply_eq.mpr rfl
  cases hj
  exact positiveIndexedInvFaceMap_last
    P cut horientation hl hr validP


-- @@ L2096-2105 verbatim
/-- Continuous inverse map on the complete split polygonal pre-realization. -/
noncomputable def positiveInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalPreRealization →
      P.PolygonalRealization validP :=
  fun x => positiveInvFaceMap
    P cut horientation hl hr validP x.1 x.2


-- @@ L2107-2116 verbatim
theorem continuous_positiveInvPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveInvPreMap
      P cut horientation hl hr validP) := by
  apply continuous_sigma
  exact continuous_positiveInvFaceMap
    P cut horientation hl hr validP


-- @@ L2118-2130 verbatim
@[simp]
theorem positiveInvPreMap_oldFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face)
    (z : PolygonCell
      ((split P cut).boundary (oldFace P cut f)).length) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨oldFace P cut f, z⟩ =
      positiveOldInvFaceMap
        P cut horientation hl hr validP f z := by
  simp [positiveInvPreMap]


-- @@ L2132-2144 verbatim
@[simp]
theorem positiveInvPreMap_rightFace
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell
      ((split P cut).boundary (rightFace P cut)).length) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨rightFace P cut, z⟩ =
      positiveRightChildInvFaceMap
        P cut horientation hl hr validP z := by
  simp [positiveInvPreMap]


-- @@ L2146-2156 verbatim
@[simp]
theorem positiveOldInvFaceMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    positiveOldInvFaceMap
        P cut horientation hl hr validP cut.face.face =
      positiveSelectedChildInvFaceMap
        P cut horientation hl hr validP := by
  simp [positiveOldInvFaceMap]


-- @@ L2158-2168 verbatim
@[simp]
theorem positiveOldInvFaceMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    positiveOldInvFaceMap
        P cut horientation hl hr validP f =
      retainedInvFaceMap P cut hface validP := by
  simp [positiveOldInvFaceMap, hface]


-- @@ L2170-2188 verbatim
@[simp]
theorem positiveSelectedChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    positiveSelectedChildInvFaceMap
        P cut horientation hl hr validP
        (positiveSelectedChildCellHomeomorph
          P cut horientation z) =
      positiveChildGluingInvMap
        P cut horientation hl hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  simp [positiveSelectedChildInvFaceMap, Function.comp_apply]


-- @@ L2190-2207 verbatim
@[simp] theorem positiveRightChildInvFaceMap_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    positiveRightChildInvFaceMap
        P cut horientation hl hr validP
        (positiveRightChildCellHomeomorph
          P cut horientation z) =
      positiveChildGluingInvMap
        P cut horientation hl hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  simp [positiveRightChildInvFaceMap, Function.comp_apply]


-- @@ L2209-2223 verbatim
theorem positiveInvPreMap_retained_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨oldFace P cut f,
          retainedCellHomeomorph P cut hface z⟩ =
      P.polygonalMk validP ⟨f, z⟩ := by
  rw [positiveInvPreMap_oldFace,
    positiveOldInvFaceMap_retained
      P cut horientation hl hr validP hface,
    retainedInvFaceMap_apply]


-- @@ L2225-2244 verbatim
theorem positiveInvPreMap_selectedChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.left.length + 1)) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph
            P cut horientation z⟩ =
      positiveChildGluingInvMap
        P cut horientation hl hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inl z)) := by
  rw [positiveInvPreMap_oldFace,
    positiveOldInvFaceMap_selected,
    positiveSelectedChildInvFaceMap_apply]


-- @@ L2246-2264 verbatim
theorem positiveInvPreMap_rightChild_apply
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (cut.right.length + 1)) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph
            P cut horientation z⟩ =
      positiveChildGluingInvMap
        P cut horientation hl hr validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length)
          (.inr z)) := by
  rw [positiveInvPreMap_rightFace,
    positiveRightChildInvFaceMap_apply]


-- @@ L2266-2289 verbatim
/-- The inverse pre-map identifies the target's fresh seam for the same local quotient reason used
by the forward construction. -/
theorem positiveInvPreMap_fresh_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    positiveInvPreMap P cut horientation hl hr validP
        ⟨oldFace P cut cut.face.face,
          positiveSelectedChildCellHomeomorph P cut horientation
            (PolygonCell.side (Fin.last cut.left.length) t)⟩ =
      positiveInvPreMap P cut horientation hl hr validP
        ⟨rightFace P cut,
          positiveRightChildCellHomeomorph P cut horientation
            (PolygonCell.side (0 : Fin (cut.right.length + 1))
              (unitInterval.symm t))⟩ := by
  rw [positiveInvPreMap_selectedChild_apply,
    positiveInvPreMap_rightChild_apply]
  apply congrArg
    (positiveChildGluingInvMap
      P cut horientation hl hr validP)
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (DiskSquare.ParamChildSeamGenerator.glue t)


-- @@ L2291-2363 verbatim
/-- On every old boundary side, the inverse pre-map exactly undoes occurrence transport. -/
theorem positiveInvPreMap_mapOccurrence_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    positiveInvPreMap P cut horientation hl hr validP
        (((split P cut).occurrenceSide
          (positiveMapOccurrence
            P cut horientation hl hr o)).point t) =
      P.polygonalMk validP ((P.occurrenceSide o).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    by_cases hleft :
        (positiveCutSideIndex
          P cut horientation hl hr i).val < cut.left.length
    · rw [positiveMapOccurrence_selected_of_lt
          P cut horientation hl hr i hleft]
      change
        positiveInvPreMap P cut horientation hl hr validP
            ⟨oldFace P cut cut.face.face,
              PolygonCell.side
                (positiveSelectedChildSideIndex P cut horientation
                  (Fin.castAdd 1
                    (positiveLeftSideIndex
                      P cut horientation hl hr i hleft))) t⟩ =
          P.polygonalMk validP
            ⟨cut.face.face, PolygonCell.side i t⟩
      rw [← positiveSelectedChildCellHomeomorph_side
          P cut horientation
          (Fin.castAdd 1
            (positiveLeftSideIndex
              P cut horientation hl hr i hleft)) t,
        positiveInvPreMap_selectedChild_apply,
        ← positiveSelectedCellHomeomorph_side_of_lt
          P cut horientation hl hr i t hleft,
        positiveChildGluingInvMap_selectedCell]
    · have hright :
          cut.left.length ≤
            (positiveCutSideIndex
              P cut horientation hl hr i).val :=
        Nat.le_of_not_gt hleft
      rw [positiveMapOccurrence_selected_of_not_lt
          P cut horientation hl hr i hleft]
      change
        positiveInvPreMap P cut horientation hl hr validP
            ⟨rightFace P cut,
              PolygonCell.side
                (positiveRightChildSideIndex P cut horientation
                  ((positiveRightSideIndex
                    P cut horientation hl hr i hright).addNat 1)) t⟩ =
          P.polygonalMk validP
            ⟨cut.face.face, PolygonCell.side i t⟩
      rw [← positiveRightChildCellHomeomorph_side
          P cut horientation
          ((positiveRightSideIndex
            P cut horientation hl hr i hright).addNat 1) t,
        positiveInvPreMap_rightChild_apply,
        ← positiveSelectedCellHomeomorph_side_of_not_lt
          P cut horientation hl hr i t hright,
        positiveChildGluingInvMap_selectedCell]
  · rw [positiveMapOccurrence_retained
        P cut horientation hl hr hface i]
    change
      positiveInvPreMap P cut horientation hl hr validP
          ⟨oldFace P cut f,
            PolygonCell.side (retainedSideIndex P cut hface i) t⟩ =
        P.polygonalMk validP ⟨f, PolygonCell.side i t⟩
    rw [← retainedCellHomeomorph_side P cut hface i t,
      positiveInvPreMap_retained_apply]


-- @@ L2365-2487 verbatim
/-- Every target boundary occurrence on an old edge is the transported copy of a source
occurrence. The two omitted target occurrences are exactly the fresh seam. -/
theorem exists_positiveMapOccurrence_eq_of_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (q : (split P cut).BoundaryOccurrence) (e : P.Edge)
    (hedge : q.edge = e.castSucc) :
    ∃ o : P.BoundaryOccurrence,
      positiveMapOccurrence P cut horientation hl hr o = q := by
  classical
  rcases q with ⟨qf, j⟩
  rcases face_cases P cut qf with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      by_cases hj : j.val < cut.left.length
      · let k : Fin (cut.left.length + cut.right.length) :=
          Fin.castAdd cut.right.length ⟨j.val, hj⟩
        obtain ⟨i, hi⟩ :=
          positiveCutSideIndex_surjective
            P cut horientation hl hr k
        have hleft :
            (positiveCutSideIndex
              P cut horientation hl hr i).val < cut.left.length := by
          rw [hi]
          exact hj
        refine ⟨⟨cut.face.face, i⟩, ?_⟩
        rw [positiveMapOccurrence_selected_of_lt
          P cut horientation hl hr i hleft]
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          simp only [positiveSelectedChildSideIndex,
            Fin.val_castAdd, positiveLeftSideIndex_val]
          rw [hi]
          rfl
      · have hjval : j.val = cut.left.length := by
          have hlen :=
            positive_split_boundary_selected_length
              P cut horientation
          have hjlt := j.isLt
          omega
        have hqfresh :
            (show (split P cut).BoundaryOccurrence from
              ⟨oldFace P cut cut.face.face, j⟩) =
              positiveSelectedFreshOccurrence
                P cut horientation := by
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Fin.ext
            exact hjval
        have hqedge := congrArg BoundaryOccurrence.edge hqfresh
        rw [positiveSelectedFreshOccurrence_edge] at hqedge
        have hbad : e.castSucc = freshEdge P :=
          hedge.symm.trans hqedge
        exact
          (P1.firstSubedge_ne_freshEdge e hbad).elim
    · let i : Fin (P.boundary f).length :=
        ⟨j.val, by
          rw [← split_boundary_old_length_of_ne P cut hface]
          exact j.isLt⟩
      refine ⟨⟨f, i⟩, ?_⟩
      rw [positiveMapOccurrence_retained
        P cut horientation hl hr hface i]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        rfl
  · by_cases hj : j.val = 0
    · have hqfresh :
          (show (split P cut).BoundaryOccurrence from
            ⟨rightFace P cut, j⟩) =
            positiveRightFreshOccurrence P cut horientation := by
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          exact hj
      have hqedge := congrArg BoundaryOccurrence.edge hqfresh
      rw [positiveRightFreshOccurrence_edge] at hqedge
      have hbad : e.castSucc = freshEdge P :=
        hedge.symm.trans hqedge
      exact
        (P1.firstSubedge_ne_freshEdge e hbad).elim
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
      let rightIndex : Fin cut.right.length :=
        ⟨j.val - 1, by
          have hlen :=
            positive_split_boundary_right_length
              P cut horientation
          have hjlt := j.isLt
          omega⟩
      let k : Fin (cut.left.length + cut.right.length) :=
        Fin.natAdd cut.left.length rightIndex
      obtain ⟨i, hi⟩ :=
        positiveCutSideIndex_surjective
          P cut horientation hl hr k
      have hright :
          cut.left.length ≤
            (positiveCutSideIndex
              P cut horientation hl hr i).val := by
        rw [hi]
        simp only [k, Fin.val_natAdd]
        omega
      have hnotleft :
          ¬(positiveCutSideIndex
              P cut horientation hl hr i).val < cut.left.length :=
        Nat.not_lt.mpr hright
      refine ⟨⟨cut.face.face, i⟩, ?_⟩
      rw [positiveMapOccurrence_selected_of_not_lt
        P cut horientation hl hr i hnotleft]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        simp only [positiveRightChildSideIndex,
          Fin.val_addNat, positiveRightSideIndex_val]
        rw [hi]
        simp only [k, Fin.val_natAdd, rightIndex]
        omega


-- @@ L2489-2504 verbatim
/-- Compatible boundary occurrences in a pairing carry the same unoriented edge. -/
theorem targetPairing_edge_eq_source_edge
    {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.target.edge = pairing.source.edge := by
  cases hdirection : pairing.direction with
  | same =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible]
  | opposite =>
      have hcompatible :
          pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      simp only [BoundaryOccurrence.edge, hcompatible,
        edgeOfDart_flip]


-- @@ L2506-2547 verbatim
/-- Once source and target occurrences agree, compatibility forces the same parameter direction. -/
theorem targetPairing_direction_eq_of_source_target_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source)
    (htarget : p.target = q.target) :
    p.direction = q.direction := by
  have hsourceDart :=
    congrArg BoundaryOccurrence.dart hsource
  have htargetDart :=
    congrArg BoundaryOccurrence.dart htarget
  cases hp : p.direction <;> cases hq : q.direction
  · rfl
  · have hpcompatible :
        p.target.dart = p.source.dart := by
      simpa only [hp] using p.compatible
    have hqcompatible :
        q.target.dart = q.source.dart.flip := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart = p.source.dart.flip := by
      calc
        p.source.dart = p.target.dart := hpcompatible.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart.flip := hqcompatible
        _ = p.source.dart.flip :=
          congrArg SignedDart.flip hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · have hpcompatible :
        p.target.dart = p.source.dart.flip := by
      simpa only [hp] using p.compatible
    have hqcompatible :
        q.target.dart = q.source.dart := by
      simpa only [hq] using q.compatible
    have hbad : p.source.dart.flip = p.source.dart := by
      calc
        p.source.dart.flip = p.target.dart := hpcompatible.symm
        _ = q.target.dart := htargetDart
        _ = q.source.dart := hqcompatible
        _ = p.source.dart := hsourceDart.symm
    cases hdart : p.source.dart <;>
      simp [hdart, SignedDart.flip] at hbad
  · rfl


-- @@ L2549-2558 verbatim
/-- Boundary pairings are determined by their two occurrences and parameter direction. -/
theorem targetPairing_eq_of_source_target_direction_eq
    {P : FiniteCyclicPresentation} (p q : P.BoundaryPairing)
    (hsource : p.source = q.source)
    (htarget : p.target = q.target)
    (hdirection : p.direction = q.direction) :
    p = q := by
  cases p
  cases q
  simp_all


-- @@ L2560-2604 verbatim
/-- The two explicitly constructed fresh occurrences exhaust the fresh edge. -/
theorem positiveFreshOccurrence_cases
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryOccurrence)
    (hedge : q.edge = freshEdge P) :
    q = positiveSelectedFreshOccurrence P cut horientation ∨
      q = positiveRightFreshOccurrence P cut horientation := by
  by_cases hselected :
      q = positiveSelectedFreshOccurrence P cut horientation
  · exact Or.inl hselected
  · let validQ := split_isSurfaceValid P cut validP
    obtain ⟨_partner, _hpartner, hunique⟩ :=
      validQ.exists_unique_partner
        (positiveSelectedFreshOccurrence P cut horientation)
        (by
          rw [positiveSelectedFreshOccurrence_edge]
          exact positiveFresh_not_boundary P cut)
    have hqcondition :
        positiveSelectedFreshOccurrence P cut horientation ≠ q ∧
          q.edge =
            (positiveSelectedFreshOccurrence
              P cut horientation).edge := by
      constructor
      · exact Ne.symm hselected
      · rw [positiveSelectedFreshOccurrence_edge]
        exact hedge
    have hrightcondition :
        positiveSelectedFreshOccurrence P cut horientation ≠
            positiveRightFreshOccurrence P cut horientation ∧
          (positiveRightFreshOccurrence
              P cut horientation).edge =
            (positiveSelectedFreshOccurrence
              P cut horientation).edge := by
      constructor
      · exact positiveSelectedFreshOccurrence_ne_right
          P cut horientation
      · rw [positiveRightFreshOccurrence_edge,
          positiveSelectedFreshOccurrence_edge]
    exact Or.inr
      ((hunique q hqcondition).trans
        (hunique
          (positiveRightFreshOccurrence P cut horientation)
          hrightcondition).symm)


-- @@ L2606-2701 verbatim
/-- A target pairing based at an old edge is exactly the transported pairing of the two
corresponding source occurrences. -/
theorem exists_positiveMapPairing_eq_of_source_edge_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (e : P.Edge)
    (hsourceEdge : q.source.edge = e.castSucc) :
    ∃ r : P.BoundaryPairing,
      positiveMapPairing P cut horientation hl hr r = q := by
  have htargetEdge : q.target.edge = e.castSucc :=
    (targetPairing_edge_eq_source_edge q).trans hsourceEdge
  obtain ⟨source, hsource⟩ :=
    exists_positiveMapOccurrence_eq_of_edge_castSucc
      P cut horientation hl hr q.source e hsourceEdge
  obtain ⟨target, htarget⟩ :=
    exists_positiveMapOccurrence_eq_of_edge_castSucc
      P cut horientation hl hr q.target e htargetEdge
  have hsourceOldEdge : source.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge hsource
    rw [positiveMapOccurrence_edge, hsourceEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have htargetOldEdge : target.edge = e := by
    have hmapEdge :=
      congrArg BoundaryOccurrence.edge htarget
    rw [positiveMapOccurrence_edge, htargetEdge] at hmapEdge
    exact Fin.castSucc_injective P.edgeCount hmapEdge
  have heInternal : ¬P.IsBoundaryEdge e := by
    intro heBoundary
    apply q.source_not_boundary
    unfold IsBoundaryEdge at heBoundary ⊢
    rw [hsourceEdge]
    exact
      (edgeMultiplicity_split_castSucc P cut e).symm.trans
        heBoundary
  have hsourceInternal : ¬P.IsBoundaryEdge source.edge := by
    rw [hsourceOldEdge]
    exact heInternal
  obtain ⟨r, hrsource⟩ :=
    validP.exists_pairing_source source hsourceInternal
  obtain ⟨_partner, _hpartner, hunique⟩ :=
    validP.exists_unique_partner source hsourceInternal
  have hsourceneTarget : source ≠ target := by
    intro heq
    apply q.source_ne_target
    calc
      q.source =
          positiveMapOccurrence
            P cut horientation hl hr source :=
        hsource.symm
      _ = positiveMapOccurrence
            P cut horientation hl hr target :=
        congrArg
          (positiveMapOccurrence
            P cut horientation hl hr) heq
      _ = q.target := htarget
  have hrcondition :
      source ≠ r.target ∧ r.target.edge = source.edge := by
    constructor
    · intro heq
      exact r.source_ne_target (hrsource.trans heq)
    · calc
        r.target.edge = r.source.edge :=
          targetPairing_edge_eq_source_edge r
        _ = source.edge :=
          congrArg BoundaryOccurrence.edge hrsource
  have htcondition :
      source ≠ target ∧ target.edge = source.edge := by
    exact
      ⟨hsourceneTarget,
        htargetOldEdge.trans hsourceOldEdge.symm⟩
  have hrtarget : r.target = target :=
    (hunique r.target hrcondition).trans
      (hunique target htcondition).symm
  have hmapSource :
      (positiveMapPairing
        P cut horientation hl hr r).source = q.source := by
    rw [positiveMapPairing_source, hrsource, hsource]
  have hmapTarget :
      (positiveMapPairing
        P cut horientation hl hr r).target = q.target := by
    rw [positiveMapPairing_target, hrtarget, htarget]
  have hmapDirection :
      (positiveMapPairing
        P cut horientation hl hr r).direction = q.direction :=
    targetPairing_direction_eq_of_source_target_eq
      (positiveMapPairing
        P cut horientation hl hr r) q
      hmapSource hmapTarget
  exact ⟨r,
    targetPairing_eq_of_source_target_direction_eq
      (positiveMapPairing
        P cut horientation hl hr r) q
      hmapSource hmapTarget hmapDirection⟩


-- @@ L2703-2723 verbatim
/-- Occurrence-side form of the exact fresh-seam equality for the inverse pre-map. -/
theorem positiveInvPreMap_fresh_occurrence_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    positiveInvPreMap P cut horientation hl hr validP
        (((split P cut).occurrenceSide
          (positiveSelectedFreshOccurrence
            P cut horientation)).point t) =
      positiveInvPreMap P cut horientation hl hr validP
        (((split P cut).occurrenceSide
          (positiveRightFreshOccurrence
            P cut horientation)).point
              (unitInterval.symm t)) := by
  rw [← positiveChildPairPreMap_fresh_inl
      P cut horientation t,
    ← positiveChildPairPreMap_fresh_inr
      P cut horientation (unitInterval.symm t)]
  exact positiveInvPreMap_fresh_seam
    P cut horientation hl hr validP t


-- @@ L2725-2811 verbatim
/-- The inverse pre-map identifies every target gluing generator: old-edge generators are
transported source pairings, while the final edge is the fresh child seam. -/
theorem positiveInvPreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : (split P cut).BoundaryPairing) (t : unitInterval) :
    positiveInvPreMap P cut horientation hl hr validP
        (q.identification.source.point t) =
      positiveInvPreMap P cut horientation hl hr validP
        (q.identification.target.point
          (q.identification.parameter t)) := by
  let edge : Fin (P.edgeCount + 1) := q.source.edge
  have hsourceEdge : q.source.edge = edge := rfl
  refine Fin.lastCases
    (motive := fun edge : Fin (P.edgeCount + 1) =>
      q.source.edge = edge →
        positiveInvPreMap P cut horientation hl hr validP
            (q.identification.source.point t) =
          positiveInvPreMap P cut horientation hl hr validP
            (q.identification.target.point
              (q.identification.parameter t)))
    ?_ (fun e hedge ↦ ?_) edge hsourceEdge
  · intro hedge
    have hfresh : q.source.edge = freshEdge P := by
      simpa only [freshEdge, P1.freshEdge] using hedge
    have htargetFresh : q.target.edge = freshEdge P :=
      (targetPairing_edge_eq_source_edge q).trans hfresh
    rcases positiveFreshOccurrence_cases
        P cut horientation validP q.source hfresh with
      hsourceSelected | hsourceRight
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · exact (q.source_ne_target
          (hsourceSelected.trans htargetSelected.symm)).elim
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceSelected, htargetRight,
                positiveRightFreshOccurrence_dart,
                positiveSelectedFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceSelected, htargetRight, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          positiveInvPreMap_fresh_occurrence_seam
            P cut horientation hl hr validP t
    · rcases positiveFreshOccurrence_cases
          P cut horientation validP q.target htargetFresh with
        htargetSelected | htargetRight
      · have hdirection : q.direction = .opposite := by
          cases hdirection : q.direction with
          | same =>
              have hcompatible := q.compatible
              rw [hdirection, hsourceRight, htargetSelected,
                positiveSelectedFreshOccurrence_dart,
                positiveRightFreshOccurrence_dart] at hcompatible
              cases hcompatible
          | opposite => rfl
        rw [BoundaryPairing.identification_source,
          BoundaryPairing.identification_target]
        simpa [hsourceRight, htargetSelected, hdirection,
            PolygonGluing.Identification.parameter,
            PolygonGluing.ParameterDirection.homeomorph_opposite_apply] using
          (positiveInvPreMap_fresh_occurrence_seam
            P cut horientation hl hr validP
            (unitInterval.symm t)).symm
      · exact (q.source_ne_target
          (hsourceRight.trans htargetRight.symm)).elim
  · obtain ⟨r, hr⟩ :=
      exists_positiveMapPairing_eq_of_source_edge_castSucc
        P cut horientation hl hr validP q e hedge
    rw [← hr, BoundaryPairing.identification_source,
      BoundaryPairing.identification_target]
    simp only [positiveMapPairing_source,
      positiveMapPairing_target]
    rw [positiveInvPreMap_mapOccurrence_side,
      positiveInvPreMap_mapOccurrence_side]
    simpa [positiveMapPairing,
        PolygonGluing.Identification.parameter] using
      P.polygonalMk_pairing_eq validP r t


-- @@ L2813-2838 verbatim
/-- The inverse pre-map is constant on the complete target gluing relation. -/
theorem positiveInvPreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : (split P cut).PolygonalPreRealization}
    (hxy :
      (split P cut).PolygonalGluingRel
        (split_isSurfaceValid P cut validP) x y) :
    positiveInvPreMap P cut horientation hl hr validP x =
      positiveInvPreMap P cut horientation hl hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      ((split P cut).polygonalIdentifications
        (split_isSurfaceValid P cut validP))) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact positiveInvPreMap_pairing_eq
            P cut horientation hl hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂


-- @@ L2840-2853 verbatim
/-- Forward map after descent through the source polygonal quotient. -/
noncomputable def positiveRealizationMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  Quotient.lift
    (positivePreMap P cut horientation hl hr validP)
    (fun _ _ hxy =>
      positivePreMap_respects
        P cut horientation hl hr validP hxy)


-- @@ L2855-2868 verbatim
/-- Inverse map after descent through the target polygonal quotient. -/
noncomputable def positiveRealizationInvMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) →
      P.PolygonalRealization validP :=
  Quotient.lift
    (positiveInvPreMap P cut horientation hl hr validP)
    (fun _ _ hxy =>
      positiveInvPreMap_respects
        P cut horientation hl hr validP hxy)


-- @@ L2870-2880 verbatim
@[simp]
theorem positiveRealizationMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    positiveRealizationMap P cut horientation hl hr validP
        (P.polygonalMk validP x) =
      positivePreMap P cut horientation hl hr validP x :=
  rfl


-- @@ L2882-2893 verbatim
@[simp]
theorem positiveRealizationInvMap_polygonalMk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    positiveRealizationInvMap P cut horientation hl hr validP
        ((split P cut).polygonalMk
          (split_isSurfaceValid P cut validP) y) =
      positiveInvPreMap P cut horientation hl hr validP y :=
  rfl


-- @@ L2895-2944 verbatim
/-- On the locally glued child pair, the descended inverse is the explicit collapse map. -/
theorem positiveRealizationInvMap_childGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    positiveRealizationInvMap P cut horientation hl hr validP
        (positiveChildGluingMap
          P cut horientation validP q) =
      positiveChildGluingInvMap
        P cut horientation hl hr validP q := by
  induction q using Quotient.inductionOn'
  case _ x =>
    cases x with
    | inl z =>
        rw [positiveChildGluingMap_mk]
        change
          positiveInvPreMap P cut horientation hl hr validP
              ⟨oldFace P cut cut.face.face,
                positiveSelectedChildCellHomeomorph
                  P cut horientation z⟩ =
            positiveChildGluingInvMap
              P cut horientation hl hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inl z))
        exact positiveInvPreMap_selectedChild_apply
          P cut horientation hl hr validP z
    | inr z =>
        rw [positiveChildGluingMap_mk]
        change
          positiveInvPreMap P cut horientation hl hr validP
              ⟨rightFace P cut,
                positiveRightChildCellHomeomorph
                  P cut horientation z⟩ =
            positiveChildGluingInvMap
              P cut horientation hl hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inr z))
        exact positiveInvPreMap_rightChild_apply
          P cut horientation hl hr validP z


-- @@ L2946-2962 verbatim
/-- The descended forward map sends the explicit child-collapse class back to the same local
child quotient class. -/
theorem positiveRealizationMap_childGluingInv
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    positiveRealizationMap P cut horientation hl hr validP
        (positiveChildGluingInvMap
          P cut horientation hl hr validP q) =
      positiveChildGluingMap P cut horientation validP q := by
  rw [positiveChildGluingInvMap,
    positiveRealizationMap_polygonalMk,
    positivePreMap_selected]
  simp [positiveSelectedFaceMap, Function.comp_apply]


-- @@ L2964-2982 verbatim
/-- Including a selected-child point in the local child quotient and then in the global quotient
is its ordinary polygonal quotient class. -/
theorem positiveChildGluingMap_selectedChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell
      ((split P cut).boundary
        (oldFace P cut cut.face.face)).length) :
    positiveChildGluingMap P cut horientation validP
        (positiveSelectedChildToGluing
          P cut horientation z) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut cut.face.face, z⟩ := by
  rw [positiveSelectedChildToGluing,
    positiveChildGluingMap_mk]
  simp [positiveChildPairMap,
    positiveChildPairPreMap, Function.comp_apply]


-- @@ L2984-3001 verbatim
/-- Including a right-child point in the local child quotient and then in the global quotient is
its ordinary polygonal quotient class. -/
theorem positiveChildGluingMap_rightChildToGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell
      ((split P cut).boundary (rightFace P cut)).length) :
    positiveChildGluingMap P cut horientation validP
        (positiveRightChildToGluing
          P cut horientation z) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut, z⟩ := by
  rw [positiveRightChildToGluing,
    positiveChildGluingMap_mk]
  simp [positiveChildPairMap,
    positiveChildPairPreMap, Function.comp_apply]


-- @@ L3003-3029 verbatim
/-- The descended inverse is a left inverse on every source pre-realization point. -/
theorem positiveRealization_left_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (x : P.PolygonalPreRealization) :
    positiveRealizationInvMap P cut horientation hl hr validP
        (positivePreMap P cut horientation hl hr validP x) =
      P.polygonalMk validP x := by
  rcases x with ⟨f, z⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [positivePreMap_selected]
    change
      positiveRealizationInvMap P cut horientation hl hr validP
          (positiveChildGluingMap P cut horientation validP
            (positiveSelectedCellHomeomorph
              P cut horientation hl hr z)) =
        P.polygonalMk validP ⟨cut.face.face, z⟩
    rw [positiveRealizationInvMap_childGluing,
      positiveChildGluingInvMap_selectedCell]
  · rw [positivePreMap_retained
        P cut horientation hl hr validP hface,
      retainedFaceMap,
      positiveRealizationInvMap_polygonalMk,
      positiveInvPreMap_retained_apply]


-- @@ L3031-3086 verbatim
/-- The descended forward map is a right inverse on every target pre-realization point. -/
theorem positiveRealization_right_inverse_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (y : (split P cut).PolygonalPreRealization) :
    positiveRealizationMap P cut horientation hl hr validP
        (positiveInvPreMap P cut horientation hl hr validP y) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP) y := by
  rcases y with ⟨q, z⟩
  rcases face_cases P cut q with ⟨f, rfl⟩ | rfl
  · by_cases hface : f = cut.face.face
    · subst f
      rw [positiveInvPreMap_oldFace,
        positiveOldInvFaceMap_selected]
      change
        positiveRealizationMap P cut horientation hl hr validP
            (positiveChildGluingInvMap
              P cut horientation hl hr validP
              (positiveSelectedChildToGluing
                P cut horientation z)) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut cut.face.face, z⟩
      rw [positiveRealizationMap_childGluingInv,
        positiveChildGluingMap_selectedChildToGluing]
    · rw [positiveInvPreMap_oldFace,
        positiveOldInvFaceMap_retained
          P cut horientation hl hr validP hface]
      change
        positiveRealizationMap P cut horientation hl hr validP
            (P.polygonalMk validP
              ⟨f, (retainedCellHomeomorph
                P cut hface).symm z⟩) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            ⟨oldFace P cut f, z⟩
      rw [positiveRealizationMap_polygonalMk,
        positivePreMap_retained
          P cut horientation hl hr validP hface,
        retainedFaceMap]
      simp
  · rw [positiveInvPreMap_rightFace]
    change
      positiveRealizationMap P cut horientation hl hr validP
          (positiveChildGluingInvMap
            P cut horientation hl hr validP
            (positiveRightChildToGluing
              P cut horientation z)) =
        (split P cut).polygonalMk
          (split_isSurfaceValid P cut validP)
          ⟨rightFace P cut, z⟩
    rw [positiveRealizationMap_childGluingInv,
      positiveChildGluingMap_rightChildToGluing]


-- @@ L3088-3117 verbatim
/-- Complete cut-and-paste certificate for a positive, nondegenerate P2 face split. -/
noncomputable def positiveRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    RealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) where
  toPre :=
    positivePreMap P cut horientation hl hr validP
  invPre :=
    positiveInvPreMap P cut horientation hl hr validP
  continuous_toPre :=
    continuous_positivePreMap
      P cut horientation hl hr validP
  continuous_invPre :=
    continuous_positiveInvPreMap
      P cut horientation hl hr validP
  to_respects := fun _ _ hxy =>
    positivePreMap_respects
      P cut horientation hl hr validP hxy
  inv_respects := fun _ _ hxy =>
    positiveInvPreMap_respects
      P cut horientation hl hr validP hxy
  left_inverse_mk :=
    positiveRealization_left_inverse_mk
      P cut horientation hl hr validP
  right_inverse_mk :=
    positiveRealization_right_inverse_mk
      P cut horientation hl hr validP


-- @@ L3119-3129 verbatim
/-- Explicit homeomorphism induced by a positive, nondegenerate P2 face split. -/
noncomputable def positiveRealizationHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  (positiveRealizationEquivData
    P cut horientation hl hr validP).homeomorph


-- @@ L3131-3140 verbatim
/-- Propositional realization-invariance form for a positive, nondegenerate P2 face split. -/
theorem positivePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) :=
  (positiveRealizationEquivData
    P cut horientation hl hr validP).polygonallyEquivalent


-- @@ L3142-3142 verbatim
/-! ### Transport across reversal of the chosen cut orientation -/


-- @@ L3144-3148 verbatim
/-- Swap the selected-face position with the fresh right-child position. -/
def flipFaceIndexEquiv
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Fin (P.faces.length + 1) ≃ Fin (P.faces.length + 1) :=
  Equiv.swap cut.face.face.castSucc (Fin.last P.faces.length)


-- @@ L3150-3156 verbatim
/-- Reversing a cut exchanges its two child faces and fixes every retained face. -/
def flipFaceEquiv
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut.flip).Face ≃ (split P cut).Face :=
  ((faceEquiv P cut.flip).symm.trans
    (flipFaceIndexEquiv P cut)).trans
      (faceEquiv P cut)


-- @@ L3158-3165 verbatim
@[simp]
theorem flipFaceEquiv_old_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    flipFaceEquiv P cut
        (oldFace P cut.flip cut.face.face) =
      rightFace P cut := by
  simp [flipFaceEquiv, flipFaceIndexEquiv,
    oldFace, rightFace]


-- @@ L3167-3173 verbatim
@[simp]
theorem flipFaceEquiv_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    flipFaceEquiv P cut (rightFace P cut.flip) =
      oldFace P cut cut.face.face := by
  simp [flipFaceEquiv, flipFaceIndexEquiv,
    oldFace, rightFace]


-- @@ L3175-3190 verbatim
@[simp]
theorem flipFaceEquiv_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    flipFaceEquiv P cut (oldFace P cut.flip f) =
      oldFace P cut f := by
  have hselected :
      f.castSucc ≠ cut.face.face.castSucc := by
    exact fun h =>
      hface (Fin.castSucc_injective _ h)
  have hlast :
      f.castSucc ≠ Fin.last P.faces.length :=
    Fin.castSucc_ne_last f
  simp [flipFaceEquiv, flipFaceIndexEquiv,
    oldFace, Equiv.swap_apply_of_ne_of_ne
      hselected hlast]


-- @@ L3192-3198 verbatim
/-- Swapping the two cut pieces exchanges the child faces and fixes every retained face. -/
def swapFaceEquiv
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (split P cut.swap).Face ≃ (split P cut).Face :=
  ((faceEquiv P cut.swap).symm.trans
    (flipFaceIndexEquiv P cut)).trans
      (faceEquiv P cut)


-- @@ L3200-3207 verbatim
@[simp]
theorem swapFaceEquiv_old_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    swapFaceEquiv P cut
        (oldFace P cut.swap cut.face.face) =
      rightFace P cut := by
  simp [swapFaceEquiv, flipFaceIndexEquiv,
    oldFace, rightFace]


-- @@ L3209-3215 verbatim
@[simp]
theorem swapFaceEquiv_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    swapFaceEquiv P cut (rightFace P cut.swap) =
      oldFace P cut cut.face.face := by
  simp [swapFaceEquiv, flipFaceIndexEquiv,
    oldFace, rightFace]


-- @@ L3217-3232 verbatim
@[simp]
theorem swapFaceEquiv_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    swapFaceEquiv P cut (oldFace P cut.swap f) =
      oldFace P cut f := by
  have hselected :
      f.castSucc ≠ cut.face.face.castSucc := by
    exact fun h =>
      hface (Fin.castSucc_injective _ h)
  have hlast :
      f.castSucc ≠ Fin.last P.faces.length :=
    Fin.castSucc_ne_last f
  simp [swapFaceEquiv, flipFaceIndexEquiv,
    oldFace, Equiv.swap_apply_of_ne_of_ne
      hselected hlast]


-- @@ L3234-3240 verbatim
/-- The raw edge relabeling for a swapped cut reverses precisely the fresh edge. -/
def swapRawEdgeRelabeling
    (P : FiniteCyclicPresentation) (_cut : P2Cut P) :
    EdgeRelabeling (Fin (P.edgeCount + 1))
      (Fin (P.edgeCount + 1)) where
  edgeEquiv := Equiv.refl _
  reverse := fun e ↦ decide (e = freshEdge P)


-- @@ L3242-3250 verbatim
/-- The raw swapped-cut relabeling at the two split presentations' exact edge types. -/
def swapEdgeRelabeling
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    EdgeRelabeling (split P cut.swap).Edge
      (split P cut).Edge := by
  change
    EdgeRelabeling (Fin (P.edgeCount + 1))
      (Fin (P.edgeCount + 1))
  exact swapRawEdgeRelabeling P cut


-- @@ L3252-3257 verbatim
@[simp]
theorem swapEdgeRelabeling_edgeEquiv
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (e : Fin (P.edgeCount + 1)) :
    (swapRawEdgeRelabeling P cut).edgeEquiv e = e :=
  rfl


-- @@ L3259-3264 verbatim
@[simp]
theorem swapEdgeRelabeling_pos_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (swapRawEdgeRelabeling P cut).mapDart (.pos (freshEdge P)) =
      .neg (freshEdge P) := by
  simp [swapRawEdgeRelabeling, EdgeRelabeling.mapDart]


-- @@ L3266-3271 verbatim
@[simp]
theorem swapEdgeRelabeling_neg_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (swapRawEdgeRelabeling P cut).mapDart (.neg (freshEdge P)) =
      .pos (freshEdge P) := by
  simp [swapRawEdgeRelabeling, EdgeRelabeling.mapDart]


-- @@ L3273-3290 verbatim
@[simp]
theorem swapEdgeRelabeling_castSucc
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (d : P.Dart) :
    (swapRawEdgeRelabeling P cut).mapDart (P1.castSuccDart d) =
      P1.castSuccDart d := by
  have hne :
      (edgeOfDart d).castSucc ≠ freshEdge P :=
    P1.firstSubedge_ne_freshEdge (edgeOfDart d)
  cases d with
  | pos e =>
      have he : e.castSucc ≠ freshEdge P := by
        simpa [edgeOfDart] using hne
      simp [swapRawEdgeRelabeling, EdgeRelabeling.mapDart, he]
  | neg e =>
      have he : e.castSucc ≠ freshEdge P := by
        simpa [edgeOfDart] using hne
      simp [swapRawEdgeRelabeling, EdgeRelabeling.mapDart, he]


-- @@ L3292-3305 verbatim
@[simp]
theorem map_swapEdgeRelabeling_retainWord
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (word : List P.Dart) :
    (retainWord word).map (swapRawEdgeRelabeling P cut).mapDart =
      retainWord word := by
  change
    (word.map P1.castSuccDart).map
        (swapRawEdgeRelabeling P cut).mapDart =
      word.map P1.castSuccDart
  rw [List.map_map]
  apply List.map_congr_left
  intro d _hd
  exact swapEdgeRelabeling_castSucc P cut d


-- @@ L3307-3330 verbatim
theorem map_swap_selectedBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (selectedBoundary P cut.swap).map
        (swapRawEdgeRelabeling P cut).mapDart |>.IsRotated
      (rightBoundary P cut) := by
  cases h : cut.face.orientation
  · rw [selectedBoundary_of_orientation_false P cut.swap (by simpa using h),
      rightBoundary_of_orientation_false P cut h]
    simp only [List.map_append, List.map_singleton,
      swapEdgeRelabeling_pos_fresh,
      map_swapEdgeRelabeling_retainWord, P2Cut.swap]
    exact
      (List.isRotated_append
        (l := retainWord cut.right)
        (l' := [SignedDart.neg (freshEdge P)]))
  · rw [selectedBoundary_of_orientation_true P cut.swap (by simpa using h),
      rightBoundary_of_orientation_true P cut h]
    simp only [List.map_cons, swapEdgeRelabeling_neg_fresh,
      ← EdgeRelabeling.inverseWord_map_mapDart,
      map_swapEdgeRelabeling_retainWord, P2Cut.swap]
    exact
      (List.isRotated_append
        (l := [SignedDart.pos (freshEdge P)])
        (l' := inverseWord (retainWord cut.right)))


-- @@ L3332-3355 verbatim
theorem map_swap_rightBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (rightBoundary P cut.swap).map
        (swapRawEdgeRelabeling P cut).mapDart |>.IsRotated
      (selectedBoundary P cut) := by
  cases h : cut.face.orientation
  · rw [rightBoundary_of_orientation_false P cut.swap (by simpa using h),
      selectedBoundary_of_orientation_false P cut h]
    simp only [List.map_cons, swapEdgeRelabeling_neg_fresh,
      map_swapEdgeRelabeling_retainWord, P2Cut.swap]
    exact
      (List.isRotated_append
        (l := [SignedDart.pos (freshEdge P)])
        (l' := retainWord cut.left))
  · rw [rightBoundary_of_orientation_true P cut.swap (by simpa using h),
      selectedBoundary_of_orientation_true P cut h]
    simp only [List.map_append, List.map_singleton,
      swapEdgeRelabeling_pos_fresh,
      ← EdgeRelabeling.inverseWord_map_mapDart,
      map_swapEdgeRelabeling_retainWord, P2Cut.swap]
    exact
      (List.isRotated_append
        (l := inverseWord (retainWord cut.left))
        (l' := [SignedDart.neg (freshEdge P)]))


-- @@ L3357-3370 verbatim
theorem map_boundary_swap_old_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (((split P cut.swap).boundary
        (oldFace P cut.swap cut.face.face)).map
          (swapEdgeRelabeling P cut).mapDart).IsRotated
      ((split P cut).boundary (rightFace P cut)) := by
  have hface : cut.face.face = cut.swap.face.face := by
    rfl
  rw [hface, split_boundary_selected, split_boundary_right]
  change
    ((selectedBoundary P cut.swap).map
      (swapRawEdgeRelabeling P cut).mapDart).IsRotated
        (rightBoundary P cut)
  exact map_swap_selectedBoundary P cut


-- @@ L3372-3384 verbatim
theorem map_boundary_swap_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (((split P cut.swap).boundary
        (rightFace P cut.swap)).map
          (swapEdgeRelabeling P cut).mapDart).IsRotated
      ((split P cut).boundary
        (oldFace P cut cut.face.face)) := by
  rw [split_boundary_right, split_boundary_selected]
  change
    ((rightBoundary P cut.swap).map
      (swapRawEdgeRelabeling P cut).mapDart).IsRotated
        (selectedBoundary P cut)
  exact map_swap_rightBoundary P cut


-- @@ L3386-3413 verbatim
theorem map_boundary_swap_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    ((split P cut.swap).boundary
        (oldFace P cut.swap f)).map
          (swapEdgeRelabeling P cut).mapDart =
      (split P cut).boundary (oldFace P cut f) := by
  have hfaceSwap : f ≠ cut.swap.face.face := by
    simpa using hface
  calc
    ((split P cut.swap).boundary
        (oldFace P cut.swap f)).map
          (swapEdgeRelabeling P cut).mapDart =
        (retainWord (P.boundary f)).map
          (swapEdgeRelabeling P cut).mapDart :=
      congrArg
        (List.map (swapEdgeRelabeling P cut).mapDart)
        (split_boundary_old_of_ne P cut.swap hfaceSwap)
    _ = (show List (split P cut).Dart from
        retainWord (P.boundary f)) :=
      by
        change
          (retainWord (P.boundary f)).map
              (swapRawEdgeRelabeling P cut).mapDart =
            retainWord (P.boundary f)
        exact map_swapEdgeRelabeling_retainWord P cut _
    _ = (split P cut).boundary (oldFace P cut f) :=
      (split_boundary_old_of_ne P cut hface).symm


-- @@ L3415-3432 verbatim
/-- Swapping the two displayed P2 pieces changes only child order and fresh-edge orientation. -/
def swapSignedPresentationIso
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedPresentationIso (split P cut.swap) (split P cut) where
  edgeRelabeling := swapEdgeRelabeling P cut
  faceEquiv := swapFaceEquiv P cut
  boundary_rotated := by
    intro q
    rcases face_cases P cut.swap q with ⟨f, rfl⟩ | rfl
    · by_cases hface : f = cut.face.face
      · subst f
        simpa only [swapFaceEquiv_old_selected] using
          map_boundary_swap_old_selected P cut
      · rw [map_boundary_swap_old_of_ne P cut hface,
          swapFaceEquiv_old_of_ne P cut hface,
          split_boundary_old_of_ne P cut hface]
    · simpa only [swapFaceEquiv_right] using
        map_boundary_swap_right P cut


-- @@ L3434-3442 verbatim
/-- Identity edge relabeling between the definitionally equal edge types of the two reversed-cut
splits. Naming the transport keeps the signed-isomorphism boundary proof transparent. -/
def flipEdgeRelabeling
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    EdgeRelabeling (split P cut.flip).Edge (split P cut).Edge := by
  change
    EdgeRelabeling (Fin (P.edgeCount + 1))
      (Fin (P.edgeCount + 1))
  exact EdgeRelabeling.refl _


-- @@ L3444-3449 verbatim
@[simp]
theorem flipEdgeRelabeling_mapDart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (d : (split P cut.flip).Dart) :
    (flipEdgeRelabeling P cut).mapDart d = d := by
  cases d <;> rfl


-- @@ L3451-3461 verbatim
@[simp]
theorem map_flipEdgeRelabeling
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (word : List (split P cut.flip).Dart) :
    word.map (flipEdgeRelabeling P cut).mapDart = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [List.map_cons,
        flipEdgeRelabeling_mapDart]
      exact congrArg (List.cons d) ih


-- @@ L3463-3485 verbatim
theorem map_boundary_flip_old_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    ((split P cut.flip).boundary
        (oldFace P cut.flip cut.face.face)).map
          (flipEdgeRelabeling P cut).mapDart =
      (split P cut).boundary (rightFace P cut) := by
  calc
    ((split P cut.flip).boundary
        (oldFace P cut.flip cut.face.face)).map
          (flipEdgeRelabeling P cut).mapDart =
        (selectedBoundary P cut.flip).map
          (flipEdgeRelabeling P cut).mapDart :=
      congrArg
        (List.map (flipEdgeRelabeling P cut).mapDart)
        (split_boundary_selected P cut.flip)
    _ = (show List (split P cut).Dart from
        selectedBoundary P cut.flip) :=
      map_flipEdgeRelabeling P cut _
    _ = (show List (split P cut).Dart from
        rightBoundary P cut) :=
      selectedBoundary_flip P cut
    _ = (split P cut).boundary (rightFace P cut) :=
      (split_boundary_right P cut).symm


-- @@ L3487-3511 verbatim
theorem map_boundary_flip_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    ((split P cut.flip).boundary
        (rightFace P cut.flip)).map
          (flipEdgeRelabeling P cut).mapDart =
      (split P cut).boundary
        (oldFace P cut cut.face.face) := by
  calc
    ((split P cut.flip).boundary
        (rightFace P cut.flip)).map
          (flipEdgeRelabeling P cut).mapDart =
        (rightBoundary P cut.flip).map
          (flipEdgeRelabeling P cut).mapDart :=
      congrArg
        (List.map (flipEdgeRelabeling P cut).mapDart)
        (split_boundary_right P cut.flip)
    _ = (show List (split P cut).Dart from
        rightBoundary P cut.flip) :=
      map_flipEdgeRelabeling P cut _
    _ = (show List (split P cut).Dart from
        selectedBoundary P cut) :=
      rightBoundary_flip P cut
    _ = (split P cut).boundary
        (oldFace P cut cut.face.face) :=
      (split_boundary_selected P cut).symm


-- @@ L3513-3536 verbatim
theorem map_boundary_flip_old_of_ne
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    {f : P.Face} (hface : f ≠ cut.face.face) :
    ((split P cut.flip).boundary
        (oldFace P cut.flip f)).map
          (flipEdgeRelabeling P cut).mapDart =
      (split P cut).boundary (oldFace P cut f) := by
  have hfaceFlip : f ≠ cut.flip.face.face := by
    simpa using hface
  calc
    ((split P cut.flip).boundary
        (oldFace P cut.flip f)).map
          (flipEdgeRelabeling P cut).mapDart =
        (retainWord (P.boundary f)).map
          (flipEdgeRelabeling P cut).mapDart :=
      congrArg
        (List.map (flipEdgeRelabeling P cut).mapDart)
        (split_boundary_old_of_ne
          P cut.flip hfaceFlip)
    _ = (show List (split P cut).Dart from
        retainWord (P.boundary f)) :=
      map_flipEdgeRelabeling P cut _
    _ = (split P cut).boundary (oldFace P cut f) :=
      (split_boundary_old_of_ne P cut hface).symm


-- @@ L3538-3558 verbatim
/-- The split presentations obtained from the two orientations of a cut differ only by swapping
the two child faces. -/
def flipSignedPresentationIso
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    SignedPresentationIso (split P cut.flip) (split P cut) where
  edgeRelabeling := flipEdgeRelabeling P cut
  faceEquiv := flipFaceEquiv P cut
  boundary_rotated := by
    intro q
    rcases face_cases P cut.flip q with ⟨f, rfl⟩ | rfl
    · by_cases hface : f = cut.face.face
      · subst f
        rw [map_boundary_flip_old_selected,
          flipFaceEquiv_old_selected,
          split_boundary_right]
      · rw [map_boundary_flip_old_of_ne P cut hface,
          flipFaceEquiv_old_of_ne P cut hface,
          split_boundary_old_of_ne P cut hface]
    · rw [map_boundary_flip_right,
        flipFaceEquiv_right,
        split_boundary_selected]


-- @@ L3560-3583 verbatim
/-- A negative-orientation nondegenerate cut reduces to the positive theorem after reversing the
cut and swapping the two child faces. -/
theorem negativePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = true)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hflipOrientation :
      cut.flip.face.orientation = false := by
    simp [P2Cut.flip, OrientedFace.flip, horientation]
  have hflipLeft : 0 < cut.flip.left.length := by
    simpa [P2Cut.flip, inverseWord] using hr
  have hflipRight : 0 < cut.flip.right.length := by
    simpa [P2Cut.flip, inverseWord] using hl
  let validFlip :=
    split_isSurfaceValid P cut.flip validP
  exact
    (positivePolygonallyEquivalent
      P cut.flip hflipOrientation
        hflipLeft hflipRight validP).trans
      ((flipSignedPresentationIso P cut).polygonallyEquivalent
        validFlip (split_isSurfaceValid P cut validP))


-- @@ L3585-3597 verbatim
/-- Every nondegenerate P2 split preserves the faithful polygonal realization, independently of
the chosen traversal orientation. -/
theorem nondegeneratePolygonallyEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  cases horientation : cut.face.orientation
  · exact positivePolygonallyEquivalent
      P cut horientation hl hr validP
  · exact negativePolygonallyEquivalent
      P cut horientation hl hr validP


-- @@ L3599-3599 verbatim
end P2


-- @@ L3601-3618 verbatim
/-- Every ordinary P2 subdivision preserves the faithful polygonal realization.

For an ordinary-valid source, the exceptional empty-word-sphere alternative in
`P2Subdivision` is impossible, so the public move relation supplies exactly the two positivity
hypotheses required by the local two-disk gluing model. -/
theorem P2Subdivision.preservesPolygonalRealization :
    P2Subdivision.PreservesPolygonalRealization := by
  intro P Q hPQ validP validQ
  rcases hPQ with ⟨cut, hcut | hempty, ⟨e⟩⟩
  · have hlengths :
        0 < cut.left.length ∧ 0 < cut.right.length :=
      (P2Cut.isNondegenerate_iff_lengths_pos cut).mp hcut
    let validSplit := P2.split_isSurfaceValid P cut validP
    exact
      (P2.nondegeneratePolygonallyEquivalent
        P cut hlengths.1 hlengths.2 validP).trans
      (e.polygonallyEquivalent validSplit validQ)
  · exact (hempty.not_isSurfaceValid validP).elim


-- @@ L3620-3620 verbatim
end FiniteCyclicPresentation


-- @@ L3622-3622 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
