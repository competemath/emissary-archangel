module

/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
public import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
public import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Category.Basic


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
open scoped Simplicial


-- @@ L17-27 verbatim
/-!
# The point cotensor `Δ[0] ⋔ B ≅ B`

Cotensoring an object `B` of an ∞-cosmos with the point `Δ[0]` recovers `B`. This file builds the
explicit comparison isomorphism `cotensorPointIso : Δ[0] ⋔ B ≅ B`. The map `cotensorPointMap`
names an ordinary morphism inside the point cotensor, `cotensorPointIsoHom` is the comparison in
the reverse direction, and the two are mutually inverse.

This infrastructure is shared by the Brown factorization construction, where it identifies the
right endpoint of a coherent-isomorphism path with the original object.
-/


-- @@ L29-29 verbatim
namespace InfinityCosmos


-- @@ L31-31 verbatim
universe u v


-- @@ L33-33 verbatim
open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos

-- @@ L34-34 verbatim
open HasConicalTerminal


-- @@ L36-36 verbatim
variable {K : Type u} [Category.{v} K] [InfinityCosmos K]


-- @@ L38-42 expanded
/-- The map into the point cotensor corresponding to an ordinary morphism. -/
noncomputable def cotensorPointMap {A B : K} (f : A ⟶ B) : A ⟶ cotensor.obj (Δ[0] : SSet.{v}) B :=
  (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A).symm
    (SSet.pointIsUnit.hom ≫ (eHomEquiv SSet f : MonoidalCategoryStruct.tensorUnit SSet ⟶ sHom A B))


-- @@ L44-46 expanded
/-- The map from the point cotensor to the object, inverse to `cotensorPointMap (𝟙 B)`. -/
noncomputable def cotensorPointIsoHom (B : K) : cotensor.obj (Δ[0] : SSet.{v}) B ⟶ B :=
  (eHomEquiv SSet).symm (SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B)


-- @@ L48-52 verbatim
/-- The enriched morphism corresponding to `cotensorPointIsoHom`. -/
lemma cotensorPointIsoHom_homEquiv (B : K) :
    eHomEquiv SSet (cotensorPointIsoHom B) =
      SSet.pointIsUnit.inv ≫ cotensor.cone (Δ[0] : SSet.{v}) B := by
  simp [cotensorPointIsoHom]


-- @@ L54-58 verbatim
/-- The underlying map represented by `cotensorPointMap`. -/
lemma cotensorPointMap_underlying {A B : K} (f : A ⟶ B) :
    (cotensor.iso.underlying (Δ[0] : SSet.{v}) B A) (cotensorPointMap f) =
      SSet.pointIsUnit.hom ≫ eHomEquiv SSet f := by
  simp [cotensorPointMap]


-- @@ L60-74 verbatim
/-- Composing a point-cotensor map with the point-cotensor comparison recovers the original map. -/
lemma cotensorPointMap_comp_cotensorPointIsoHom {A B : K} (f : A ⟶ B) :
    cotensorPointMap f ≫ cotensorPointIsoHom B = f := by
  apply (eHomEquiv SSet).injective
  rw [← eHomEquiv_comp_eHomWhiskerRight]
  rw [cotensorPointIsoHom_homEquiv]
  rw [Category.assoc]
  have hmap := cotensorPointMap_underlying f
  rw [cotensor_iso_underlying_eq_cone] at hmap
  change SSet.pointIsUnit.inv ≫
      ((getCotensor (Δ[0] : SSet.{v}) B).cone ≫
        eHomWhiskerRight SSet (cotensorPointMap f) B) =
    (eHomEquiv SSet) f
  rw [hmap]
  rw [← Category.assoc, SSet.pointIsUnit.inv_hom_id, Category.id_comp]


-- @@ L76-96 expanded
/-- One inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_hom_inv_id (B : K) :
    cotensorPointIsoHom B ≫ cotensorPointMap (𝟙 B) = 𝟙 (cotensor.obj (Δ[0] : SSet.{v}) B) :=
  by
  apply (cotensor.iso.underlying (Δ[0] : SSet.{v}) B (cotensor.obj (Δ[0] : SSet.{v}) B)).injective
  rw [cotensor_iso_underlying_eq_cone]
  rw [cotensor_iso_underlying_eq_cone]
  rw [eHomWhiskerRight_comp]
  change
    (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
        (eHomWhiskerRight SSet (cotensorPointMap (𝟙 B)) B ≫
          eHomWhiskerRight SSet (cotensorPointIsoHom B) B) =
      (getCotensor (Δ[0] : SSet.{v}) B).cone ≫
        eHomWhiskerRight SSet (𝟙 (cotensor.obj (Δ[0] : SSet.{v}) B)) B
  rw [← Category.assoc]
  have hmap := cotensorPointMap_underlying (𝟙 B)
  rw [cotensor_iso_underlying_eq_cone] at hmap
  rw [hmap, Category.assoc, eHomEquiv_comp_eHomWhiskerRight, Category.comp_id,
    cotensorPointIsoHom_homEquiv]
  rw [← Category.assoc, SSet.pointIsUnit.hom_inv_id, Category.id_comp, eHomWhiskerRight_id]
  change (getCotensor (Δ[0] : SSet.{v}) B).cone = (getCotensor (Δ[0] : SSet.{v}) B).cone ≫ 𝟙 _
  rw [Category.comp_id]


-- @@ L98-101 verbatim
/-- The other inverse identity for the point-cotensor comparison. -/
lemma cotensorPointIso_inv_hom_id (B : K) :
    cotensorPointMap (𝟙 B) ≫ cotensorPointIsoHom B = 𝟙 B :=
  cotensorPointMap_comp_cotensorPointIsoHom (𝟙 B)


-- @@ L103-108 expanded
/-- The point cotensor is isomorphic to the original object. -/
noncomputable def cotensorPointIso (B : K) : cotensor.obj (Δ[0] : SSet.{v}) B ≅ B
    where
  hom := cotensorPointIsoHom B
  inv := cotensorPointMap (𝟙 B)
  hom_inv_id := cotensorPointIso_hom_inv_id B
  inv_hom_id := cotensorPointIso_inv_hom_id B


-- @@ L110-110 verbatim
end InfinityCosmos
