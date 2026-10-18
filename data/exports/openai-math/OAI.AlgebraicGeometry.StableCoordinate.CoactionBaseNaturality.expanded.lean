import OAI.AlgebraicGeometry.StableCoordinate.CoactionLND


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-12 verbatim
/-!
# Coassociativity on the image of an equivariant base algebra

An arbitrary polynomial family extending a genuine additive action on a base
algebra already satisfies the action law on that base image.  This lemma is
used before the determinant-frame uniqueness argument: it supplies equality
of the three base products of the two candidate composite frames.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace StableCoordinate.CoactionLND


-- @@ L18-18 verbatim
open Polynomial


-- @@ L20-21 verbatim
variable {k B A : Type*} [CommRing k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A]


-- @@ L23-35 verbatim
/-- Universal Taylor translation commutes with change of coefficient ring. -/
theorem universal_translate_map (p : B[X]) (i : B →+* A) :
    (taylor (X : B[X]) (p.map (C : B →+* B[X]))).map (mapRingHom i) =
      taylor (X : A[X]) ((p.map i).map (C : A →+* A[X])) := by
  rw [map_taylor]
  have hX : mapRingHom i (X : B[X]) = (X : A[X]) := map_X i
  rw [hX]
  congr 1
  rw [map_map, map_map]
  congr 1
  apply RingHom.ext
  intro b
  simp


-- @@ L37-59 verbatim
/-- Coassociativity transfers to the image of the base under any polynomial
family extending an actual base action.  No group law or normalization for
`β` is assumed. -/
theorem coassoc_on_image_of_extension
    (α : PolynomialAdditiveAction k B) (β : A →ₐ[k] A[X]) (i : B →ₐ[k] A)
    (hβ : ∀ b, β (i b) = (α.toAlgHom b).map i.toRingHom) (b : B) :
    (β (i b)).map β.toRingHom =
      taylor (X : A[X]) ((β (i b)).map (C : A →+* A[X])) := by
  have hmaps : β.toRingHom.comp i.toRingHom =
      (mapRingHom i.toRingHom).comp α.toAlgHom.toRingHom := by
    apply RingHom.ext
    intro b
    exact hβ b
  calc
    (β (i b)).map β.toRingHom =
        ((α.toAlgHom b).map i.toRingHom).map β.toRingHom := by rw [hβ]
    _ = ((α.toAlgHom b).map α.toAlgHom.toRingHom).map (mapRingHom i.toRingHom) := by
      rw [map_map, map_map, hmaps]
    _ = (taylor (X : B[X]) ((α.toAlgHom b).map (C : B →+* B[X]))).map
        (mapRingHom i.toRingHom) := by rw [α.coassoc]
    _ = taylor (X : A[X]) (((α.toAlgHom b).map i.toRingHom).map
        (C : A →+* A[X])) := universal_translate_map _ _
    _ = taylor (X : A[X]) ((β (i b)).map (C : A →+* A[X])) := by rw [hβ]


-- @@ L61-61 verbatim
end StableCoordinate.CoactionLND


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end OAI
