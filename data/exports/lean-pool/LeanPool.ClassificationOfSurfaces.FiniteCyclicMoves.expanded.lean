/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2
public import LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L16-31 verbatim
/-!
# Finite cyclic move closures

This file combines signed presentation isomorphisms and the two primitive Gallier--Xu
subdivisions into stable closure APIs.

`Subdivides` is the directed reflexive-transitive closure. It preserves ordinary validity,
connectivity, and Gallier validity. `HasCommonSubdivision P Q` supplies a validity-safe common
target for topological comparison: starting with two ordinary-valid presentations, both forward
chains remain ordinary-valid. This is stronger operational data than an unrestricted symmetric
move chain, which may pass through the exceptional empty-word sphere where
`PolygonalRealization` is deliberately unavailable.

`MoveEquivalent` is also provided as the purely syntactic equivalence closure. A common
subdivision implies move equivalence, but no converse or confluence theorem is asserted here.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L37-37 verbatim
namespace FiniteCyclicPresentation


-- @@ L39-42 verbatim
/-- One directed presentation step: a signed isomorphism, P1 subdivision, or P2 subdivision. -/
def SubdivisionStep (P Q : FiniteCyclicPresentation) : Prop :=
  Nonempty (SignedPresentationIso P Q) ∨
    P1Subdivision P Q ∨ P2Subdivision P Q


-- @@ L44-44 verbatim
namespace SubdivisionStep


-- @@ L46-49 verbatim
theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    SubdivisionStep P Q :=
  Or.inl ⟨e⟩


-- @@ L51-54 verbatim
theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inl h)


-- @@ L56-59 verbatim
theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inr h)


-- @@ L61-70 verbatim
/-- Every directed step preserves ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isSurfaceValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isSurfaceValid validP
    · exact hP2.isSurfaceValid validP


-- @@ L72-81 verbatim
/-- Every directed step preserves face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isConnected connectedP
  · rcases hrest with hP1 | hP2
    · exact hP1.isConnected connectedP
    · exact hP2.isConnected connectedP


-- @@ L83-92 verbatim
/-- Every directed step preserves the packed Gallier--Xu validity predicate. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isGallierValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isGallierValid validP
    · exact hP2.isGallierValid validP


-- @@ L94-94 verbatim
end SubdivisionStep


-- @@ L96-98 verbatim
/-- Directed finite subdivision by signed isomorphisms, P1, and P2. -/
def Subdivides (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.ReflTransGen SubdivisionStep P Q


-- @@ L100-100 verbatim
namespace Subdivides


-- @@ L102-103 verbatim
theorem refl (P : FiniteCyclicPresentation) : Subdivides P P :=
  Relation.ReflTransGen.refl


-- @@ L105-107 verbatim
theorem single {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : Subdivides P Q :=
  Relation.ReflTransGen.single h


-- @@ L109-111 verbatim
theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : Subdivides P Q :=
  single (SubdivisionStep.signedIso e)


-- @@ L113-115 verbatim
theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p1 h)


-- @@ L117-119 verbatim
theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p2 h)


-- @@ L121-124 verbatim
theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (hQR : Subdivides Q R) :
    Subdivides P R :=
  Relation.ReflTransGen.trans hPQ hQR


-- @@ L126-134 verbatim
/-- Directed subdivision chains preserve ordinary surface incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isSurfaceValid ih


-- @@ L136-144 verbatim
/-- Directed subdivision chains preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  induction hPQ with
  | refl =>
      exact connectedP
  | tail _ hstep ih =>
      exact hstep.isConnected ih


-- @@ L146-154 verbatim
/-- Directed subdivision chains preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isGallierValid ih


-- @@ L156-156 verbatim
end Subdivides


-- @@ L158-160 verbatim
/-- Two presentations have a common directed subdivision. -/
def HasCommonSubdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ R : FiniteCyclicPresentation, Subdivides P R ∧ Subdivides Q R


-- @@ L162-162 verbatim
namespace HasCommonSubdivision


-- @@ L164-165 verbatim
theorem refl (P : FiniteCyclicPresentation) : HasCommonSubdivision P P :=
  ⟨P, Subdivides.refl P, Subdivides.refl P⟩


-- @@ L167-171 verbatim
theorem symm {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) :
    HasCommonSubdivision Q P := by
  rcases h with ⟨R, hPR, hQR⟩
  exact ⟨R, hQR, hPR⟩


-- @@ L173-173 verbatim
end HasCommonSubdivision


-- @@ L175-177 verbatim
/-- Purely syntactic equivalence generated by signed isomorphisms, P1, and P2. -/
def MoveEquivalent (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.EqvGen SubdivisionStep P Q


-- @@ L179-179 verbatim
namespace MoveEquivalent


-- @@ L181-182 verbatim
theorem refl (P : FiniteCyclicPresentation) : MoveEquivalent P P :=
  Relation.EqvGen.refl P


-- @@ L184-186 verbatim
theorem ofStep {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : MoveEquivalent P Q :=
  Relation.EqvGen.rel P Q h


-- @@ L188-190 verbatim
theorem symm {P Q : FiniteCyclicPresentation}
    (h : MoveEquivalent P Q) : MoveEquivalent Q P :=
  Relation.EqvGen.symm P Q h


-- @@ L192-195 verbatim
theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : MoveEquivalent P Q) (hQR : MoveEquivalent Q R) :
    MoveEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR


-- @@ L197-197 verbatim
end MoveEquivalent


-- @@ L199-207 verbatim
/-- Every directed subdivision chain is a syntactic move equivalence. -/
theorem Subdivides.moveEquivalent {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) :
    MoveEquivalent P Q := by
  induction hPQ with
  | refl =>
      exact MoveEquivalent.refl P
  | @tail Q R _ hstep ih =>
      exact ih.trans (MoveEquivalent.ofStep hstep)


-- @@ L209-214 verbatim
/-- A common directed subdivision is in particular a syntactic move equivalence. -/
theorem HasCommonSubdivision.moveEquivalent
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q) :
    MoveEquivalent P Q := by
  rcases h with ⟨R, hPR, hQR⟩
  exact hPR.moveEquivalent.trans hQR.moveEquivalent.symm


-- @@ L216-216 verbatim
namespace PolygonallyEquivalent


-- @@ L218-220 verbatim
theorem refl (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent P validP validP :=
  ⟨Homeomorph.refl _⟩


-- @@ L222-227 verbatim
theorem symm {P Q : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    (h : P.PolygonallyEquivalent Q validP validQ) :
    Q.PolygonallyEquivalent P validQ validP := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩


-- @@ L229-237 verbatim
theorem trans {P Q R : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    {validR : R.IsSurfaceValid}
    (hPQ : P.PolygonallyEquivalent Q validP validQ)
    (hQR : Q.PolygonallyEquivalent R validQ validR) :
    P.PolygonallyEquivalent R validP validR := by
  rcases hPQ with ⟨ePQ⟩
  rcases hQR with ⟨eQR⟩
  exact ⟨ePQ.trans eQR⟩


-- @@ L239-239 verbatim
end PolygonallyEquivalent


-- @@ L241-248 verbatim
/-- The stable proof obligation for primitive realization invariance.

The P1 and P2 realization files discharge the corresponding disjuncts; signed isomorphisms are
already implemented by `SignedPresentationIso.polygonallyEquivalent`. -/
def SubdivisionStep.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, SubdivisionStep P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ


-- @@ L250-254 verbatim
/-- The realization-invariance obligation isolated to P1 subdivisions. -/
def P1Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P1Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ


-- @@ L256-260 verbatim
/-- The realization-invariance obligation isolated to P2 subdivisions. -/
def P2Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P2Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ


-- @@ L262-274 verbatim
/-- Signed-isomorphism invariance plus the two primitive geometric obligations supplies invariance
for every directed elementary step. -/
theorem SubdivisionStep.preservesPolygonalRealization
    (hP1 : P1Subdivision.PreservesPolygonalRealization)
    (hP2 : P2Subdivision.PreservesPolygonalRealization) :
    SubdivisionStep.PreservesPolygonalRealization := by
  intro P Q hstep validP validQ
  rcases hstep with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.polygonallyEquivalent validP validQ
  · rcases hrest with hP1Step | hP2Step
    · exact hP1 hP1Step validP validQ
    · exact hP2 hP2Step validP validQ


-- @@ L276-289 verbatim
/-- If every primitive directed step preserves the faithful polygonal quotient, so does every
directed subdivision chain. -/
theorem Subdivides.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  induction hPQ with
  | refl =>
      exact PolygonallyEquivalent.refl P validP
  | @tail R Q hPR hstep ih =>
      let validR : R.IsSurfaceValid :=
        Subdivides.isSurfaceValid hPR validP
      exact (ih validR).trans (hprimitive hstep validR validQ)


-- @@ L291-303 verbatim
/-- Primitive realization invariance promotes a common-subdivision certificate to a
homeomorphism of faithful polygonal quotients. -/
theorem HasCommonSubdivision.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  rcases h with ⟨R, hPR, hQR⟩
  let validR : R.IsSurfaceValid :=
    Subdivides.isSurfaceValid hPR validP
  exact
    (hPR.polygonallyEquivalent hprimitive validP validR).trans
      (hQR.polygonallyEquivalent hprimitive validQ validR).symm


-- @@ L305-305 verbatim
end FiniteCyclicPresentation


-- @@ L307-307 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
