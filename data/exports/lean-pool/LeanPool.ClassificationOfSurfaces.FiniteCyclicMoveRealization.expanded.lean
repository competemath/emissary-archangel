/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoves
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1Realization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2Realization
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L16-23 verbatim
/-!
# Realization invariance for finite cyclic move closures

This file closes the geometric proof obligations parameterizing `FiniteCyclicMoves`. Signed
presentation isomorphisms, P1 subdivisions, and genuine P2 face subdivisions all preserve the
faithful polygonal quotient. Consequently, clients of directed chains and common-subdivision
certificates do not need to pass the primitive invariance proofs explicitly.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces


-- @@ L29-29 verbatim
namespace FiniteCyclicPresentation


-- @@ L31-36 verbatim
/-- Every elementary directed subdivision step preserves the faithful polygonal realization. -/
theorem subdivisionStep_preservesPolygonalRealization :
    SubdivisionStep.PreservesPolygonalRealization :=
  SubdivisionStep.preservesPolygonalRealization
    P1Subdivision.preservesPolygonalRealization
    P2Subdivision.preservesPolygonalRealization


-- @@ L38-45 verbatim
/-- A directed chain of signed isomorphisms and P1/P2 subdivisions preserves the faithful
polygonal realization. -/
theorem Subdivides.toPolygonallyEquivalent
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  hPQ.polygonallyEquivalent
    subdivisionStep_preservesPolygonalRealization validP validQ


-- @@ L47-54 verbatim
/-- A common directed subdivision gives a homeomorphism of the two faithful polygonal
realizations. -/
theorem HasCommonSubdivision.toPolygonallyEquivalent
    {P Q : FiniteCyclicPresentation} (hPQ : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  hPQ.polygonallyEquivalent
    subdivisionStep_preservesPolygonalRealization validP validQ


-- @@ L56-56 verbatim
end FiniteCyclicPresentation


-- @@ L58-58 verbatim
end LeanEval.Topology.ClassificationOfSurfaces
