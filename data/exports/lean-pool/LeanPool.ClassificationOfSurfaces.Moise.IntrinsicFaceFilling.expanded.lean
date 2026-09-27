/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceExtension
public import LeanPool.ClassificationOfSurfaces.Moise.FinitePLHomeomorph
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation
import Mathlib.CategoryTheory.Category.Init


-- @@ L13-20 verbatim
/-!
# PL fillings of intrinsic polygonal face boundaries

The simultaneous intrinsic graph replacement gives every maximal face a canonical map from the
standard triangular frontier onto a simple polygonal circle.  `IntrinsicFaceExtension` proves
that this map is genuinely PL on one named finite subdivision.  Polygonal Schoenflies now fills
it by a finite PL homeomorphism, without changing any shared-edge boundary values.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace LeanEval

-- @@ L25-25 verbatim
namespace Topology

-- @@ L26-26 verbatim
namespace ClassificationOfSurfaces

-- @@ L27-27 verbatim
namespace Moise


-- @@ L29-29 verbatim
namespace IntrinsicTwoComplex


-- @@ L31-33 verbatim
variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}


-- @@ L35-50 verbatim
/-- A certified finite PL filling of the canonical polygonal boundary of one intrinsic face. -/
structure FacePLFilling (t : K.Face) where
  /-- The `map` declaration. -/
  map : Plane → Plane
  eqOn_boundary : Set.EqOn map
    (K.faceBoundaryMap (hcont := hcont) (hinj := hinj) (D := D) (C := C) t)
    (frontier standardFaceRegion)
  continuousOn : ContinuousOn map standardFaceRegion
  injectiveOn : Set.InjOn map standardFaceRegion
  image_eq : map '' standardFaceRegion =
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion
  isPLOnSet : IsPLOnSet standardFaceRegion map
  certificate : Nonempty (FinitePLHomeomorphBetween map standardFaceRegion
    (K.facePolygonalCircle
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).closedRegion)


-- @@ L52-72 verbatim
/-- Polygonal Schoenflies fills the canonical face boundary by a finite PL homeomorphism. -/
theorem exists_facePLFilling (t : K.Face) :
    Nonempty (K.FacePLFilling
      (hcont := hcont) (hinj := hinj) (D := D) (C := C) t) := by
  let J := K.facePolygonalCircle
    (hcont := hcont) (hinj := hinj) (D := D) (C := C) t
  obtain ⟨F, hboundary, hcontinuous, hFinj, himage, hpl, hcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary
      standardTrianglePlaneComplex_isTriangle J
      (K.faceBoundaryMap_isPLOnSet t)
      (K.faceBoundaryMap_injectiveOn t)
      (K.faceBoundaryMap_image_polygon t)
  exact ⟨{
    map := F
    eqOn_boundary := hboundary
    continuousOn := hcontinuous
    injectiveOn := hFinj
    image_eq := himage
    isPLOnSet := hpl
    certificate := hcert
  }⟩


-- @@ L74-77 verbatim
/-- A fixed choice of the certified PL filling for downstream finite gluing. -/
noncomputable def facePLFilling (t : K.Face) :
    K.FacePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t :=
  Classical.choice (K.exists_facePLFilling t)


-- @@ L79-89 verbatim
/-- Fillings of neighboring faces agree wherever their standard boundary lifts name the same
intrinsic one-skeleton point.  The equality is pointwise because both restrictions are the same
global graph replacement map. -/
theorem facePLFilling_eq_of_boundaryLift_eq
    {t u : K.Face} {p q : StandardFaceBoundary}
    (hpq : (K.faceBoundaryLift t p).1 = (K.faceBoundaryLift u q).1) :
    (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) t).map p.1 =
      (K.facePLFilling (hcont := hcont) (hinj := hinj) (D := D) (C := C) u).map q.1 := by
  rw [(K.facePLFilling t).eqOn_boundary p.2,
    (K.facePLFilling u).eqOn_boundary q.2,
    K.faceBoundaryMap_apply t p, K.faceBoundaryMap_apply u q, hpq]


-- @@ L91-91 verbatim
end IntrinsicTwoComplex


-- @@ L93-93 verbatim
end Moise

-- @@ L94-94 verbatim
end ClassificationOfSurfaces

-- @@ L95-95 verbatim
end Topology

-- @@ L96-96 verbatim
end LeanEval
