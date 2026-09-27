/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L15-26 verbatim
/-!
# Polygonal realization under signed presentation isomorphism

A signed presentation isomorphism may rename and independently reverse edge names, relabel faces,
and cyclically rotate each stored face word. This file realizes those operations geometrically.
The selected cyclic rotation acts on the circular polygon carrier by an exact complex rotation,
so every labelled source side is sent to the target side carrying its relabelled dart.

The resulting homeomorphism of polygonal pre-realizations transports both the elementary gluing
generators and their equivalence closures. It therefore descends to a homeomorphism of the faithful
polygonal quotients.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L32-32 verbatim
open Complex


-- @@ L34-34 verbatim
namespace PolygonCell


-- @@ L36-38 verbatim
/-- The `rotationUnit` declaration. -/
noncomputable def rotationUnit (n k : ℕ) : Circle :=
  Circle.exp (2 * Real.pi * k / n)


-- @@ L40-68 verbatim
/-- The `rotateHomeomorph` declaration. -/
noncomputable def rotateHomeomorph {n m : ℕ} (h : n = m) (k : ℕ) :
    PolygonCell n ≃ₜ PolygonCell m := by
  subst m
  exact
    { toFun := fun z => ⟨(rotationUnit n k : ℂ) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      invFun := fun z => ⟨((rotationUnit n k)⁻¹ : Circle) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      left_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      right_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      continuous_toFun := by
        apply continuous_induced_rng.2
        fun_prop
      continuous_invFun := by
        apply continuous_induced_rng.2
        fun_prop }


-- @@ L70-76 verbatim
@[simp]
theorem rotateHomeomorph_apply_val {n m : ℕ} (h : n = m) (k : ℕ)
    (z : PolygonCell n) :
    (rotateHomeomorph h k z).val = (rotationUnit n k : ℂ) * z.val :=
  by
    subst m
    rfl


-- @@ L78-80 verbatim
/-- The `rotateIndex` declaration. -/
def rotateIndex {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩


-- @@ L82-85 verbatim
@[simp]
theorem rotateIndex_val {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) :
    (rotateIndex hn k i).val = (i.val + k) % n :=
  rfl


-- @@ L87-110 verbatim
theorem rotateHomeomorph_side {n : ℕ} (hn : 0 < n) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph (Eq.refl n) k (side i t) =
      side (rotateIndex hn k i) t := by
  apply PolygonCell.ext
  change ((Circle.exp (2 * Real.pi * k / n) : Circle) : ℂ) *
      ((Circle.exp (sideAngle i t) : Circle) : ℂ) =
    ((Circle.exp (sideAngle (rotateIndex hn k i) t) : Circle) : ℂ)
  rw [← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨Int.ofNat ((i.val + k) / n), ?_⟩
  simp only [sideAngle, rotateIndex_val]
  have hdecomp : (i.val + k) % n + n * ((i.val + k) / n) = i.val + k :=
    Nat.mod_add_div (i.val + k) n
  have hdecompR := congrArg (fun q : ℕ => (q : ℝ)) hdecomp
  push_cast at hdecompR
  have hquot :
      ((Int.ofNat ((i.val + k) / n) : ℤ) : ℝ) =
        (((i.val + k) / n : ℕ) : ℝ) := by
    rfl
  rw [hquot]
  field_simp [hn.ne']
  nlinarith [hdecompR]


-- @@ L112-120 verbatim
/-- Rotation sends a side to the correspondingly shifted side after changing only the phantom
side-count index. -/
theorem rotateHomeomorph_side_of_eq {n m : ℕ} (h : n = m) (hm : 0 < m) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph h k (side i t) =
      side
        (⟨(i.val + k) % m, Nat.mod_lt _ hm⟩ : Fin m) t := by
  subst m
  exact rotateHomeomorph_side hm k i t


-- @@ L122-122 verbatim
end PolygonCell


-- @@ L124-124 verbatim
namespace FiniteCyclicPresentation.SignedPresentationIso


-- @@ L126-126 verbatim
open SurfaceCellComplex


-- @@ L128-128 verbatim
variable {P Q : FiniteCyclicPresentation}


-- @@ L130-132 verbatim
/-- The target-boundary rotation selected for a signed presentation isomorphism. -/
noncomputable def faceRotation (e : SignedPresentationIso P Q) (f : P.Face) : ℕ :=
  Classical.choose (e.boundary_rotated f).symm


-- @@ L134-137 verbatim
theorem rotate_target_boundary (e : SignedPresentationIso P Q) (f : P.Face) :
    (Q.boundary (e.faceEquiv f)).rotate (e.faceRotation f) =
      (P.boundary f).map e.edgeRelabeling.mapDart :=
  Classical.choose_spec (e.boundary_rotated f).symm


-- @@ L139-147 verbatim
/-- The target side occupied by a source side after the selected face rotation. -/
noncomputable def sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    Fin (Q.boundary (e.faceEquiv f)).length := by
  have hpos : 0 < (Q.boundary (e.faceEquiv f)).length :=
    List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  exact ⟨(i.val + e.faceRotation f) %
    (Q.boundary (e.faceEquiv f)).length, Nat.mod_lt _ hpos⟩


-- @@ L149-156 verbatim
@[simp]
theorem sideIndex_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (e.sideIndex validQ f i).val =
      (i.val + e.faceRotation f) %
        (Q.boundary (e.faceEquiv f)).length :=
  rfl


-- @@ L158-190 verbatim
/-- The rotated target side carries exactly the relabeled source dart. -/
theorem boundary_get_sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  let target := Q.boundary (e.faceEquiv f)
  let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
  have hrot : target.rotate (e.faceRotation f) = mapped :=
    e.rotate_target_boundary f
  have hlen : target.length = mapped.length := by
    rw [← hrot, List.length_rotate]
  have hiTarget : i.val < target.length := by
    rw [hlen]
    simpa only [mapped, List.length_map] using i.isLt
  have hpoint :
      (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
    congrArg (fun word => word[i.val]?) hrot
  rw [List.getElem?_rotate hiTarget] at hpoint
  have hmapped :
      mapped[i.val]? =
        some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
    simp [mapped, i.isLt]
  rw [hmapped] at hpoint
  have htarget :
      target.get
          ⟨(i.val + e.faceRotation f) % target.length,
            Nat.mod_lt _ (List.length_pos_of_ne_nil
              (validQ.2.1 (e.faceEquiv f)))⟩ =
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
    rw [← Option.some_inj, ← hpoint]
    simp
  exact htarget


-- @@ L192-196 verbatim
/-- The disk homeomorphism on a face selected by the cyclic boundary rotation. -/
noncomputable def faceHomeomorph (e : SignedPresentationIso P Q) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell (Q.boundary (e.faceEquiv f)).length :=
  PolygonCell.rotateHomeomorph (e.boundary_length_eq f) (e.faceRotation f)


-- @@ L198-204 verbatim
/-- A signed presentation isomorphism gives a facewise homeomorphism of polygonal
pre-realizations. -/
noncomputable def preHomeomorph (e : SignedPresentationIso P Q) :
    P.PolygonalPreRealization ≃ₜ Q.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap e.faceEquiv.bijective
      (fun f => (e.faceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map e.faceEquiv fun f => e.faceHomeomorph f)


-- @@ L206-210 verbatim
@[simp]
theorem preHomeomorph_apply_fst (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).1 = e.faceEquiv x.1 :=
  rfl


-- @@ L212-216 verbatim
@[simp]
theorem preHomeomorph_apply_snd (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).2 = e.faceHomeomorph x.1 x.2 :=
  rfl


-- @@ L218-231 verbatim
/-- On a labelled side, the pre-realization homeomorphism is exactly the selected cyclic shift. -/
theorem preHomeomorph_side (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    e.preHomeomorph ⟨f, PolygonCell.side i t⟩ =
      ⟨e.faceEquiv f, PolygonCell.side (e.sideIndex validQ f i) t⟩ := by
  apply Sigma.ext
  · rfl
  · simp only [preHomeomorph_apply_snd, faceHomeomorph]
    apply heq_of_eq
    exact PolygonCell.rotateHomeomorph_side_of_eq
        (e.boundary_length_eq f)
        (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
        (e.faceRotation f) i t


-- @@ L233-237 verbatim
/-- Transport a boundary occurrence through the selected cyclic shift. -/
noncomputable def mapOccurrence (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence → Q.BoundaryOccurrence
  | ⟨f, i⟩ => ⟨e.faceEquiv f, e.sideIndex validQ f i⟩


-- @@ L239-244 verbatim
@[simp]
theorem mapOccurrence_fst (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).1 = e.faceEquiv o.1 := by
  cases o
  rfl


-- @@ L246-253 verbatim
@[simp]
theorem mapOccurrence_snd_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).2.val =
      (o.2.val + e.faceRotation o.1) %
        (Q.boundary (e.faceEquiv o.1)).length := by
  cases o
  rfl


-- @@ L255-261 verbatim
/-- The transported occurrence carries the signed relabeling of the source dart. -/
theorem mapOccurrence_dart (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).dart =
      e.edgeRelabeling.mapDart o.dart := by
  rcases o with ⟨f, i⟩
  exact e.boundary_get_sideIndex validQ f i


-- @@ L263-279 verbatim
/-- Cyclic shifting is injective on the finite side-index type. -/
private theorem sideIndex_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face) :
    Function.Injective (e.sideIndex validQ f) := by
  intro i j hij
  have hlen := e.boundary_length_eq f
  have hmod :
      i.val + e.faceRotation f ≡ j.val + e.faceRotation f
        [MOD (Q.boundary (e.faceEquiv f)).length] := by
    exact congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD (Q.boundary (e.faceEquiv f)).length] :=
    Nat.ModEq.add_right_cancel' (e.faceRotation f) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← hlen, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel


-- @@ L281-294 verbatim
/-- Transport of boundary occurrences is injective. -/
theorem mapOccurrence_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    Function.Injective (e.mapOccurrence validQ) := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hface : f = g := by
    apply e.faceEquiv.injective
    exact congrArg Sigma.fst h
  subst g
  have hindex : i = j := by
    apply e.sideIndex_injective validQ f
    exact eq_of_heq ((Sigma.ext_iff.mp h).2)
  subst j
  rfl


-- @@ L296-302 verbatim
@[simp]
theorem mapOccurrence_edge (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).edge = e.edgeEquiv o.edge := by
  rw [BoundaryOccurrence.edge, e.mapOccurrence_dart,
    EdgeRelabeling.edgeOfDart_mapDart]
  rfl


-- @@ L304-329 verbatim
/-- A compatible source pairing transports to a compatible target pairing. -/
noncomputable def mapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    Q.BoundaryPairing where
  source := e.mapOccurrence validQ pairing.source
  target := e.mapOccurrence validQ pairing.target
  source_ne_target :=
    (e.mapOccurrence_injective validQ).ne pairing.source_ne_target
  source_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.source.edge).not.mp
      pairing.source_not_boundary
  target_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.target.edge).not.mp
      pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible]
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible,
        EdgeRelabeling.mapDart_flip]


-- @@ L331-335 verbatim
@[simp]
theorem mapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).direction = pairing.direction :=
  rfl


-- @@ L337-342 verbatim
@[simp]
theorem mapPairing_source (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).source =
      e.mapOccurrence validQ pairing.source :=
  rfl


-- @@ L344-349 verbatim
@[simp]
theorem mapPairing_target (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).target =
      e.mapOccurrence validQ pairing.target :=
  rfl


-- @@ L351-358 verbatim
/-- The pre-realization homeomorphism maps an occurrence-side point to its transported side. -/
theorem preHomeomorph_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph ((P.occurrenceSide o).point t) =
      (Q.occurrenceSide (e.mapOccurrence validQ o)).point t := by
  rcases o with ⟨f, i⟩
  exact e.preHomeomorph_side validQ f i t


-- @@ L360-364 verbatim
/-- Ignoring cyclic shifts, corresponding boundary-occurrence types have the same cardinality. -/
noncomputable def rawOccurrenceEquiv (e : SignedPresentationIso P Q) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.sigmaCongr e.faceEquiv fun f =>
    (Fin.castOrderIso (e.boundary_length_eq f)).toEquiv


-- @@ L366-373 verbatim
/-- The cyclic occurrence transport bundled as an equivalence. -/
noncomputable def occurrenceEquiv (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.ofBijective (e.mapOccurrence validQ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨e.mapOccurrence_injective validQ,
        Fintype.card_congr e.rawOccurrenceEquiv⟩)


-- @@ L375-379 verbatim
@[simp]
theorem occurrenceEquiv_apply (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    e.occurrenceEquiv validQ o = e.mapOccurrence validQ o :=
  rfl


-- @@ L381-386 verbatim
@[simp]
theorem mapOccurrence_occurrenceEquiv_symm
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.mapOccurrence validQ ((e.occurrenceEquiv validQ).symm o) = o :=
  (e.occurrenceEquiv validQ).apply_symm_apply o


-- @@ L388-396 verbatim
theorem preHomeomorph_symm_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph.symm ((Q.occurrenceSide o).point t) =
      (P.occurrenceSide ((e.occurrenceEquiv validQ).symm o)).point t := by
  apply e.preHomeomorph.injective
  rw [e.preHomeomorph.apply_symm_apply]
  rw [e.preHomeomorph_occurrenceSide_point validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]


-- @@ L398-404 verbatim
theorem occurrenceEquiv_symm_dart
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeRelabeling.mapDart ((e.occurrenceEquiv validQ).symm o).dart =
      o.dart := by
  rw [← e.mapOccurrence_dart validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]


-- @@ L406-411 verbatim
theorem occurrenceEquiv_symm_edge
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeEquiv ((e.occurrenceEquiv validQ).symm o).edge = o.edge := by
  rw [← e.mapOccurrence_edge validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]


-- @@ L413-445 verbatim
/-- Pull a compatible target pairing back through the occurrence equivalence. -/
noncomputable def comapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    P.BoundaryPairing where
  source := (e.occurrenceEquiv validQ).symm pairing.source
  target := (e.occurrenceEquiv validQ).symm pairing.target
  source_ne_target :=
    (e.occurrenceEquiv validQ).symm.injective.ne pairing.source_ne_target
  source_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.source).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.source_not_boundary
  target_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.target).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      simpa only [EdgeRelabeling.dartEquiv_apply,
        e.occurrenceEquiv_symm_dart validQ] using hcompatible
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      rw [EdgeRelabeling.dartEquiv_apply, EdgeRelabeling.dartEquiv_apply,
        EdgeRelabeling.mapDart_flip, e.occurrenceEquiv_symm_dart,
        e.occurrenceEquiv_symm_dart]
      exact hcompatible


-- @@ L447-451 verbatim
@[simp]
theorem comapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).direction = pairing.direction :=
  rfl


-- @@ L453-458 verbatim
theorem preHomeomorph_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.source.point t) =
      ((e.mapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.source t


-- @@ L460-465 verbatim
theorem preHomeomorph_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.target.point t) =
      ((e.mapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.target t


-- @@ L467-476 verbatim
theorem preHomeomorph_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.mapPairing validQ pairing).identification.target.point
        ((e.mapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_pairing_target_point]
  rfl


-- @@ L478-493 verbatim
/-- The facewise homeomorphism sends every source gluing generator into the target generated
relation. -/
theorem preHomeomorph_generator_related
    (e : SignedPresentationIso P Q) (_validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    Q.PolygonalGluingRel validQ
      (e.preHomeomorph (pairing.identification.source.point t))
      (e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_pairing_source_point,
    e.preHomeomorph_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.mapPairing validQ pairing).identification
    (pairing_identification_mem validQ (e.mapPairing validQ pairing)) t


-- @@ L495-514 verbatim
/-- The facewise homeomorphism preserves the complete generated gluing relation. -/
theorem preHomeomorph_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂


-- @@ L516-521 verbatim
theorem preHomeomorph_symm_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.source.point t) =
      ((e.comapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.source t


-- @@ L523-528 verbatim
theorem preHomeomorph_symm_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.target.point t) =
      ((e.comapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.target t


-- @@ L530-539 verbatim
theorem preHomeomorph_symm_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.comapPairing validQ pairing).identification.target.point
        ((e.comapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_symm_pairing_target_point]
  rfl


-- @@ L541-555 verbatim
/-- The inverse facewise homeomorphism sends every target generator into the source relation. -/
theorem preHomeomorph_symm_generator_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm (pairing.identification.source.point t))
      (e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_symm_pairing_source_point,
    e.preHomeomorph_symm_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.comapPairing validQ pairing).identification
    (pairing_identification_mem validP (e.comapPairing validQ pairing)) t


-- @@ L557-577 verbatim
/-- The inverse facewise homeomorphism preserves the complete generated relation. -/
theorem preHomeomorph_symm_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : Q.PolygonalPreRealization}
    (hxy : Q.PolygonalGluingRel validQ x y) :
    P.PolygonalGluingRel validP (e.preHomeomorph.symm x)
      (e.preHomeomorph.symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (Q.polygonalIdentifications validQ)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_symm_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂


-- @@ L579-589 verbatim
/-- The selected pre-realization homeomorphism identifies the two generated gluing relations. -/
theorem preHomeomorph_related_iff
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  constructor
  · exact e.preHomeomorph_related validP validQ
  · intro hxy
    simpa only [e.preHomeomorph.symm_apply_apply] using
      e.preHomeomorph_symm_related validP validQ hxy


-- @@ L591-598 verbatim
/-- Signed edge relabeling, face relabeling, and cyclic boundary rotation preserve the faithful
polygonal realization. -/
noncomputable def realizationHomeomorph
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ :=
  PolygonGluing.realizationCongr e.preHomeomorph
    (e.preHomeomorph_related_iff validP validQ)


-- @@ L600-605 verbatim
/-- Propositional realization-invariance form used by elementary-move closures. -/
theorem polygonallyEquivalent
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  ⟨e.realizationHomeomorph validP validQ⟩


-- @@ L607-607 verbatim
end FiniteCyclicPresentation.SignedPresentationIso


-- @@ L609-609 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
