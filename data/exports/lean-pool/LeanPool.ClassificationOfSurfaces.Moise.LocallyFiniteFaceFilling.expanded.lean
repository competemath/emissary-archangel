/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteFaceExtension
public import LeanPool.ClassificationOfSurfaces.Moise.FinitePLHomeomorph
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation
import Mathlib.CategoryTheory.Category.Init


-- @@ L13-19 verbatim
/-!
# PL fillings of locally finite polygonal face boundaries

The globally coherent graph replacement gives every maximal face a PL map from the standard
triangular frontier onto a simple polygonal circle. Polygonal Schoenflies fills that map by a
finite PL homeomorphism without changing its shared-edge boundary values.
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
namespace LocallyFiniteTriangleComplex


-- @@ L30-31 verbatim
variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization}


-- @@ L33-46 verbatim
/-- A certified finite PL filling of the canonical polygonal boundary of one locally finite
face. -/
structure FacePLFilling (f : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map (K.faceBoundaryMap (G := G) f)
    (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion =
    (K.facePolygonalCircle (G := G) f).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (K.facePolygonalCircle (G := G) f).closedRegion)


-- @@ L48-66 verbatim
/-- Polygonal Schoenflies fills the canonical face boundary by a finite PL homeomorphism. -/
theorem exists_facePLFilling (f : K.Face) :
    Nonempty (K.FacePLFilling (G := G) f) := by
  let J := K.facePolygonalCircle (G := G) f
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle J
      (K.faceBoundaryMap_isPLOnSet (G := G) f)
      (K.faceBoundaryMap_injectiveOn (G := G) f)
      (K.faceBoundaryMap_image_polygon (G := G) f)
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert
  }⟩


-- @@ L68-71 verbatim
/-- A fixed certified PL filling for downstream locally finite gluing. -/
noncomputable def facePLFilling (f : K.Face) :
    K.FacePLFilling (G := G) f :=
  Classical.choice (K.exists_facePLFilling (G := G) f)


-- @@ L73-83 verbatim
/-- Fillings of neighboring faces agree whenever their boundary lifts name the same global
one-skeleton point. -/
theorem facePLFilling_eq_of_boundaryLift_eq
    {f g : K.Face} {p q : StandardFaceBoundary}
    (hpq : K.faceBoundaryLift f p = K.faceBoundaryLift g q) :
    (K.facePLFilling (G := G) f).map p.1 =
      (K.facePLFilling (G := G) g).map q.1 := by
  rw [(K.facePLFilling (G := G) f).eqOn_boundary p.2,
    (K.facePLFilling (G := G) g).eqOn_boundary q.2,
    K.faceBoundaryMap_apply (G := G) f p,
    K.faceBoundaryMap_apply (G := G) g q, hpq]


-- @@ L85-85 verbatim
end LocallyFiniteTriangleComplex


-- @@ L87-87 verbatim
end Moise

-- @@ L88-88 verbatim
end ClassificationOfSurfaces

-- @@ L89-89 verbatim
end Topology

-- @@ L90-90 verbatim
end LeanEval
