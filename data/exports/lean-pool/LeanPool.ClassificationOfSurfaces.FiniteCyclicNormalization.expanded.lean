/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.FiniteCyclicCrosscap
import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoveRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2DegenerateRealization
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L16-32 verbatim
/-!
# Stable closure for Gallier--Xu normalization chains

Directed P1/P2 chains and common subdivisions preserve ordinary validity internally. The
cross-cap rewrite additionally reads one refined face backwards, and the current
orientation-sensitive validity predicate is not invariant under arbitrary face reversal.

`ValidPresentation` therefore bundles the ordinary-validity witness at every node of a
normalization chain. `NormalizationStep` has exactly two proof-producing seams:

* a common directed P1/P2/signed-isomorphism subdivision;
* an unoriented presentation isomorphism in either direction.

The equivalence closure composes these seams, and its realization theorem needs no extra
intermediate validity arguments. This is the stable target for the remaining derived
normalization chains.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L38-38 verbatim
namespace FiniteCyclicPresentation


-- @@ L40-44 verbatim
/-- An ordinary-valid finite cyclic presentation, used as a node in a normalization chain. -/
structure ValidPresentation where
  /-- The `presentation` declaration. -/
  presentation : FiniteCyclicPresentation
  valid : presentation.IsSurfaceValid


-- @@ L46-46 verbatim
namespace ValidPresentation


-- @@ L48-49 verbatim
instance : Coe ValidPresentation FiniteCyclicPresentation :=
  ⟨ValidPresentation.presentation⟩


-- @@ L51-61 verbatim
@[ext]
theorem ext {P Q : ValidPresentation}
    (h : P.presentation = Q.presentation) :
    P = Q := by
  cases P with
  | mk presentation valid =>
      cases Q with
      | mk presentation' valid' =>
          dsimp at h
          subst presentation'
          rfl


-- @@ L63-66 verbatim
/-- Package an ordinary-valid presentation. -/
def mk' (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    ValidPresentation :=
  ⟨P, validP⟩


-- @@ L68-68 verbatim
end ValidPresentation


-- @@ L70-88 verbatim
/-- One validity-safe normalization comparison. Common subdivisions cover the P1/P2/signed
closure; the second constructor covers an independent choice of face traversal in either
direction. -/
inductive NormalizationStep : ValidPresentation → ValidPresentation → Prop
  | commonSubdivision {P Q : ValidPresentation}
      (h : HasCommonSubdivision P.presentation Q.presentation) :
      NormalizationStep P Q
  | unoriented {P Q : ValidPresentation}
      (h : Nonempty (UnorientedPresentationIso P.presentation Q.presentation) ∨
        Nonempty (UnorientedPresentationIso Q.presentation P.presentation)) :
      NormalizationStep P Q
  | oneSidedP2 {P : ValidPresentation}
      (cut : P2Cut P.presentation)
      (honeSided :
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = [])) :
      NormalizationStep P
        ⟨P2.split P.presentation cut,
          P2.split_isSurfaceValid P.presentation cut P.valid⟩


-- @@ L90-90 verbatim
namespace NormalizationStep


-- @@ L92-95 verbatim
theorem ofUnorientedIso {P Q : ValidPresentation}
    (e : UnorientedPresentationIso P.presentation Q.presentation) :
    NormalizationStep P Q :=
  .unoriented (Or.inl ⟨e⟩)


-- @@ L97-100 verbatim
theorem ofUnorientedIsoSymm {P Q : ValidPresentation}
    (e : UnorientedPresentationIso Q.presentation P.presentation) :
    NormalizationStep P Q :=
  .unoriented (Or.inr ⟨e⟩)


-- @@ L102-111 verbatim
/-- A one-sided-degenerate P2 split is a normalization step. -/
theorem ofOneSidedP2 {P : ValidPresentation}
    (cut : P2Cut P.presentation)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = [])) :
    NormalizationStep P
      ⟨P2.split P.presentation cut,
        P2.split_isSurfaceValid P.presentation cut P.valid⟩ :=
  .oneSidedP2 cut honeSided


-- @@ L113-129 verbatim
/-- Every normalization step preserves the faithful polygonal realization of its bundled valid
endpoints. -/
theorem polygonallyEquivalent {P Q : ValidPresentation}
    (h : NormalizationStep P Q) :
    P.presentation.PolygonallyEquivalent Q.presentation P.valid Q.valid := by
  cases h with
  | commonSubdivision hcommon =>
      exact hcommon.toPolygonallyEquivalent P.valid Q.valid
  | unoriented horiented =>
      rcases horiented with hforward | hbackward
      · rcases hforward with ⟨e⟩
        exact e.polygonallyEquivalent P.valid Q.valid
      · rcases hbackward with ⟨e⟩
        exact (e.polygonallyEquivalent Q.valid P.valid).symm
  | oneSidedP2 cut honeSided =>
      exact P2.oneSidedPolygonallyEquivalent
        P.presentation cut honeSided P.valid


-- @@ L131-131 verbatim
end NormalizationStep


-- @@ L133-135 verbatim
/-- Equivalence closure of validity-safe normalization comparisons. -/
def NormalizationEquivalent (P Q : ValidPresentation) : Prop :=
  Relation.EqvGen NormalizationStep P Q


-- @@ L137-137 verbatim
namespace NormalizationEquivalent


-- @@ L139-140 verbatim
theorem refl (P : ValidPresentation) : NormalizationEquivalent P P :=
  Relation.EqvGen.refl P


-- @@ L142-144 verbatim
theorem ofStep {P Q : ValidPresentation} (h : NormalizationStep P Q) :
    NormalizationEquivalent P Q :=
  Relation.EqvGen.rel P Q h


-- @@ L146-149 verbatim
theorem ofCommonSubdivision {P Q : ValidPresentation}
    (h : HasCommonSubdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.commonSubdivision h)


-- @@ L151-156 verbatim
/-- A directed subdivision is a normalization equivalence, using its target as the common
subdivision. -/
theorem ofSubdivides {P Q : ValidPresentation}
    (h : Subdivides P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofCommonSubdivision ⟨Q.presentation, h, Subdivides.refl Q.presentation⟩


-- @@ L158-162 verbatim
/-- A signed presentation isomorphism is a normalization equivalence. -/
theorem ofSignedIso {P Q : ValidPresentation}
    (e : SignedPresentationIso P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.signedIso e)


-- @@ L164-168 verbatim
/-- A P1 subdivision is a normalization equivalence. -/
theorem ofP1 {P Q : ValidPresentation}
    (h : P1Subdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.p1 h)


-- @@ L170-174 verbatim
/-- A P2 subdivision is a normalization equivalence. -/
theorem ofP2 {P Q : ValidPresentation}
    (h : P2Subdivision P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofSubdivides (Subdivides.p2 h)


-- @@ L176-179 verbatim
theorem ofUnorientedIso {P Q : ValidPresentation}
    (e : UnorientedPresentationIso P.presentation Q.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.ofUnorientedIso e)


-- @@ L181-184 verbatim
theorem ofUnorientedIsoSymm {P Q : ValidPresentation}
    (e : UnorientedPresentationIso Q.presentation P.presentation) :
    NormalizationEquivalent P Q :=
  ofStep (.ofUnorientedIsoSymm e)


-- @@ L186-195 verbatim
/-- A one-sided-degenerate P2 split is a normalization equivalence. -/
theorem ofOneSidedP2 {P : ValidPresentation}
    (cut : P2Cut P.presentation)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = [])) :
    NormalizationEquivalent P
      ⟨P2.split P.presentation cut,
        P2.split_isSurfaceValid P.presentation cut P.valid⟩ :=
  ofStep (.ofOneSidedP2 cut honeSided)


-- @@ L197-199 verbatim
theorem symm {P Q : ValidPresentation} (h : NormalizationEquivalent P Q) :
    NormalizationEquivalent Q P :=
  Relation.EqvGen.symm P Q h


-- @@ L201-205 verbatim
theorem trans {P Q R : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q)
    (hQR : NormalizationEquivalent Q R) :
    NormalizationEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR


-- @@ L207-220 verbatim
/-- A normalization chain yields a homeomorphism of the faithful polygonal realizations of its
endpoints. -/
theorem polygonallyEquivalent {P Q : ValidPresentation}
    (h : NormalizationEquivalent P Q) :
    P.presentation.PolygonallyEquivalent Q.presentation P.valid Q.valid := by
  induction h with
  | rel _ _ hstep =>
      exact hstep.polygonallyEquivalent
  | refl _ =>
      exact PolygonallyEquivalent.refl _ _
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ihPQ ihQR =>
      exact ihPQ.trans ihQR


-- @@ L222-222 verbatim
end NormalizationEquivalent


-- @@ L224-224 verbatim
namespace Dyck


-- @@ L226-238 verbatim
/-- The generic Dyck rewrite as a node in the stable normalization closure. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SurfaceCellComplex.SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (source a U V X).IsSurfaceValid)
    (validTarget : (target a U V X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a U V X, validSource⟩
      ⟨target a U V X, validTarget⟩ :=
  NormalizationEquivalent.ofCommonSubdivision
    (hasCommonSubdivision a U V X haU haV haX)


-- @@ L240-240 verbatim
end Dyck


-- @@ L242-242 verbatim
namespace Crosscap


-- @@ L244-282 verbatim
/-- The generic cross-cap rewrite as a three-step normalization chain: split the source, reverse
the right refined face, and merge to the target. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (X Y : List (SurfaceCellComplex.SignedDart (Fin n)))
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (validSource : (source a X Y).IsSurfaceValid)
    (validTarget : (target a X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a X Y, validSource⟩
      ⟨target a X Y, validTarget⟩ := by
  let sourceSplit :=
    P2.split (source a X Y) (sourceCut a X Y)
  let targetSplit :=
    P2.split (target a X Y) (targetCut a X Y)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source a X Y) (sourceCut a X Y) validSource
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (target a X Y) (targetCut a X Y) validTarget
  let P : ValidPresentation := ⟨source a X Y, validSource⟩
  let S : ValidPresentation := ⟨sourceSplit, validSourceSplit⟩
  let T : ValidPresentation := ⟨targetSplit, validTargetSplit⟩
  let Q : ValidPresentation := ⟨target a X Y, validTarget⟩
  have hPS : NormalizationEquivalent P S := by
    apply NormalizationEquivalent.ofCommonSubdivision
    refine ⟨sourceSplit, ?_, Subdivides.refl sourceSplit⟩
    exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (sourceCut_isNondegenerate a X Y))
  have hST : NormalizationEquivalent S T := by
    exact NormalizationEquivalent.ofUnorientedIsoSymm
      (splitUnorientedPresentationIso a X Y haX haY)
  have hTQ : NormalizationEquivalent T Q := by
    apply NormalizationEquivalent.ofCommonSubdivision
    refine ⟨targetSplit, Subdivides.refl targetSplit, ?_⟩
    exact Subdivides.p2
      (P2Subdivision.canonical _ _
        (targetCut_isNondegenerate a X Y))
  exact hPS.trans (hST.trans hTQ)


-- @@ L284-284 verbatim
end Crosscap


-- @@ L286-286 verbatim
namespace P1


-- @@ L288-298 verbatim
/-- Contract a canonical P1 expansion inside the normalization closure. -/
theorem contractionNormalizationEquivalent
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨expand P a, expand_isSurfaceValid P a validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofP1
    (P := ⟨P, validP⟩)
    (Q := ⟨expand P a, expand_isSurfaceValid P a validP⟩)
    (P1Subdivision.canonical P a)).symm


-- @@ L300-300 verbatim
end P1


-- @@ L302-302 verbatim
namespace P2


-- @@ L304-316 verbatim
/-- Merge the two children of a nondegenerate canonical P2 split inside the normalization
closure. -/
theorem mergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut : cut.IsNondegenerate)
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofP2
    (P := ⟨P, validP⟩)
    (Q := ⟨split P cut, split_isSurfaceValid P cut validP⟩)
    (P2Subdivision.canonical P cut hcut)).symm


-- @@ L318-330 verbatim
/-- Merge the two children of a one-sided-degenerate P2 split. This is the inverse form needed
by cancellation chains, where one child is a monogon. -/
theorem oneSidedMergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ :=
  (NormalizationEquivalent.ofOneSidedP2
    (P := ⟨P, validP⟩) cut honeSided).symm


-- @@ L332-346 verbatim
/-- Merge any ordinary-valid canonical P2 split whose cut is either nondegenerate or
one-sided-degenerate. -/
theorem ordinaryMergeNormalizationEquivalent
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨split P cut, split_isSurfaceValid P cut validP⟩
      ⟨P, validP⟩ := by
  rcases hcut with hnondegenerate | honeSided
  · exact mergeNormalizationEquivalent P cut hnondegenerate validP
  · exact oneSidedMergeNormalizationEquivalent P cut honeSided validP


-- @@ L348-348 verbatim
end P2


-- @@ L350-350 verbatim
end FiniteCyclicPresentation


-- @@ L352-352 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
