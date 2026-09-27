/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonical
public import LeanPool.ClassificationOfSurfaces.FiniteCyclicCancellation
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L15-21 verbatim
/-!
# Canonical output of finite-cyclic normalization

This file fixes the output type of the Gallier--Xu recursion before that recursion is assembled.
A result lands only at the existing `NormalForm.canonicalPresentation`; it cannot introduce a
second project-owned spelling of the Eval representatives.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L27-27 verbatim
namespace FiniteCyclicPresentation


-- @@ L29-29 verbatim
open SurfaceCellComplex


-- @@ L31-35 verbatim
/-- The validity-bundled canonical presentation selected by an admissible normal form. -/
noncomputable def canonicalValidPresentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    ValidPresentation :=
  ⟨N.canonicalPresentation, N.canonicalPresentation_isSurfaceValid hN⟩


-- @@ L37-42 verbatim
@[simp]
theorem canonicalValidPresentation_presentation
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    (canonicalValidPresentation N hN).presentation =
      N.canonicalPresentation :=
  rfl


-- @@ L44-54 verbatim
/-- Certified output of the finite-cyclic Gallier--Xu normalization.

The dependent admissibility field supplies ordinary validity for the canonical endpoint, and the
equivalence field records the entire validity-safe move chain. -/
structure NormalizationResult (P : ValidPresentation) where
  /-- The `normalForm` declaration. -/
  normalForm : NormalForm
  admissible : normalForm.IsEvalAdmissible
  equivalent :
    NormalizationEquivalent P
      (canonicalValidPresentation normalForm admissible)


-- @@ L56-56 verbatim
namespace NormalizationResult


-- @@ L58-64 verbatim
/-- A canonical presentation is already normalized. -/
noncomputable def canonical
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    NormalizationResult (canonicalValidPresentation N hN) where
  normalForm := N
  admissible := hN
  equivalent := NormalizationEquivalent.refl _


-- @@ L66-74 verbatim
/-- Transport a normalization result backward through a normalization equivalence. -/
noncomputable def ofEquivalent
    {P Q : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q)
    (result : NormalizationResult Q) :
    NormalizationResult P where
  normalForm := result.normalForm
  admissible := result.admissible
  equivalent := hPQ.trans result.equivalent


-- @@ L76-82 verbatim
/-- Transport a normalization result across a signed presentation isomorphism. -/
noncomputable def ofSignedIso
    {P Q : ValidPresentation}
    (e : SignedPresentationIso P.presentation Q.presentation)
    (result : NormalizationResult Q) :
    NormalizationResult P :=
  result.ofEquivalent (NormalizationEquivalent.ofSignedIso e)


-- @@ L84-94 verbatim
/-- A normalization result gives the faithful polygonal realization equivalence to its exact
canonical finite-cyclic endpoint. -/
theorem polygonallyEquivalent
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonallyEquivalent
      result.normalForm.canonicalPresentation
      P.valid
      (result.normalForm.canonicalPresentation_isSurfaceValid
        result.admissible) :=
  result.equivalent.polygonallyEquivalent


-- @@ L96-105 verbatim
/-- Homeomorphism from a normalized input's faithful polygonal realization to the exact canonical
finite-cyclic realization. -/
noncomputable def realizationHomeomorph
    {P : ValidPresentation}
    (result : NormalizationResult P) :
    P.presentation.PolygonalRealization P.valid ≃ₜ
      result.normalForm.canonicalPresentation.PolygonalRealization
        (result.normalForm.canonicalPresentation_isSurfaceValid
          result.admissible) :=
  Classical.choice result.polygonallyEquivalent


-- @@ L107-107 verbatim
end NormalizationResult


-- @@ L109-109 verbatim
namespace Cancellation


-- @@ L111-131 verbatim
/-- The terminal inverse-pair cancellation with no remaining darts yields the agreed canonical
sphere presentation. -/
noncomputable def sphereNormalizationResult
    (validSource :
      (source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid) :
    NormalizationResult
      ⟨source ([] : List (SignedDart (Fin 0))), validSource⟩ := by
  let hcanonical :=
    sphereNormalizationEquivalent validSource
  let canonicalSphere :=
    canonicalValidPresentation NormalForm.sphere trivial
  have hnode :
      (⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ :
        ValidPresentation) = canonicalSphere := by
    apply ValidPresentation.ext
    rfl
  rw [hnode] at hcanonical
  exact
    { normalForm := .sphere
      admissible := trivial
      equivalent := hcanonical }


-- @@ L133-133 verbatim
end Cancellation


-- @@ L135-135 verbatim
end FiniteCyclicPresentation


-- @@ L137-137 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
