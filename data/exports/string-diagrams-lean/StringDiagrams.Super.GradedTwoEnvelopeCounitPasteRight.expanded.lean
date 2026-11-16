import StringDiagrams.Super.GradedTwoEnvelopeCounitPasteLeft


-- @@ L3-10 verbatim
/-!
# Postcomposition of the chosen density transformation

This bounded slice constructs the genuine postcomposition-density bridge.
The unit constraint of the postcomposing functor is an invertible
supermodification, not an equality of transformation records. Both compositor
factors in `TwoNatTrans.postcompose` remain present.
-/


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
namespace StringDiagrams

-- @@ L14-14 verbatim
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

-- @@ L15-15 verbatim
universe w w₁ v₁ u₁

-- @@ L16-16 verbatim
variable {R : Type w} [CommRing R]

-- @@ L17-17 verbatim
namespace QPiTwoEnvelope

-- @@ L18-18 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L19-22 verbatim
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) (hT : T.IsGraded)
  (G : C ⟶ D)

-- @@ L23-24 verbatim
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

-- @@ L25-26 verbatim
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b


-- @@ L28-32 verbatim
/-- The density cell after mapping its middle factor, with target unitors. -/
def postcomposeDensityX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    G.1.map ((extend (restrict T)).map f) ≫ 𝟙 (G.1.obj (T.obj b)) ⟶
      𝟙 (G.1.obj (T.obj a)) ≫ G.1.map (T.map f) :=
  (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictApp T hT f) ≫ (leftUnitor _).inv


-- @@ L34-39 verbatim
theorem postcomposeDensityX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    postcomposeDensityX T hT G f ∈ parity (R := R) _ _ 0 := by
  simpa only [postcomposeDensityX, zero_add] using! comp_mem
    (rightUnitor_hom_mem (R := R) _)
    (comp_mem (G.1.map₂_mem (extendRestrictApp_mem T hT f))
      (inv_mem _ (leftUnitor_hom_mem (R := R) _)))


-- @@ L41-51 verbatim
/-- Naturality includes odd and nonzero-degree input 2-morphisms. -/
theorem postcomposeDensityX_naturality {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    G.1.map₂ ((extend (restrict T)).map₂ η) ▷ 𝟙 (G.1.obj (T.obj b)) ≫
        postcomposeDensityX T hT G g =
      postcomposeDensityX T hT G f ≫ 𝟙 (G.1.obj (T.obj a)) ◁ G.1.map₂ (T.map₂ η) := by
  unfold postcomposeDensityX
  erw [rightUnitor_naturality_assoc R, ← reassoc_of% G.1.map₂_comp,
    extendRestrictApp_naturality, G.1.map₂_comp]
  simp only [Category.assoc]
  erw [leftUnitor_inv_naturality R (G.1.map₂ (T.map₂ η))]


-- @@ L53-91 verbatim
/-- The actual mapped density, normalized by the unit constraint of `G`. -/
def postcomposeDensity :
    TwoNatTrans ((extend (restrict T)).comp G.1) (T.comp G.1) where
  X a := 𝟙 (G.1.obj (T.obj a))
  x f := postcomposeDensityX T hT G f
  x_mem f := postcomposeDensityX_mem T hT G f
  naturality η := postcomposeDensityX_naturality T hT G η
  x_comp f g := xcomp_of_J (F' := (extend (restrict T)).comp G.1) (G' := T.comp G.1)
    (fun a => 𝟙 (G.1.obj (T.obj a))) (fun f => postcomposeDensityX T hT G f)
    (fun f => postcomposeDensityX_mem T hT G f)
    (fun η => postcomposeDensityX_naturality T hT G η)
    (fun {a b c} f g => by
      have h₁ : (((extend (restrict T)).comp G.1).mapComp (Jm (R := R) f) (Jm g)).hom =
          ((T.comp G.1).mapComp (Jm f) (Jm g)).hom := by
        simp only [TwoSuperfunctor.comp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
          extendComp_J, restrict_mapComp]
        rfl
      have h₂ := extendRestrictApp_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) (f ≫ g)
      have h₃ := extendRestrictApp_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B)) f
      have h₄ := extendRestrictApp_J T hT (a := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) g
      simp only [xcompL, xcompR, postcomposeDensityX]
      erw [h₂, h₃, h₄, G.1.map₂_id, G.1.map₂_id, G.1.map₂_id]
      simp only [Category.id_comp]
      erw [h₁]
      exact TwoEnvelope.unit_coherence R (G.1.map (T.map (Jm f)))
        (G.1.map (T.map (Jm g))) ((T.comp G.1).mapComp (Jm f) (Jm g)).hom) f g
  x_id a := by
    have h : extendRestrictApp T hT (𝟙 a) = 𝟙 _ := extendRestrictApp_J T hT (𝟙 a.as.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictApp T hT (𝟙 a)) ≫
      (leftUnitor _).inv = _
    erw [h, G.1.map₂_id, Category.id_comp, rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    erw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    erw [Iso.hom_inv_id_assoc]
    rfl


-- @@ L93-98 verbatim
theorem postcomposeDensity_isGraded : (postcomposeDensity T hT G).IsGraded := by
  intro a b f
  simpa only [postcomposeDensity, postcomposeDensityX, zero_add] using! comp_mem_degree
    (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _)
    (comp_mem_degree (G.2.map₂_mem_degree (extendRestrictApp_mem_degree T hT f))
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) _))


-- @@ L100-131 verbatim
/-- Mapping the density transformation is isomorphic, not equal, to its unit
normalization. The components are precisely the inverses of `G.mapId`. -/
def postcomposeDensityIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTrans T hT) ≅
      postcomposeDensity T hT G :=
  TwoEnvelope.supermodificationIso (fun a => (G.1.mapId (T.obj a)).symm) (by
    intro a b f
    change ((G.1.mapComp _ _).hom ≫
      G.1.map₂ ((rightUnitor _).hom ≫ extendRestrictApp T hT f ≫ (leftUnitor _).inv) ≫
      (G.1.mapComp _ _).inv) ≫ (G.1.mapId _).inv ▷ _ =
        _ ◁ (G.1.mapId _).inv ≫ (rightUnitor _).hom ≫
          G.1.map₂ (extendRestrictApp T hT f) ≫ (leftUnitor _).inv
    simp only [G.1.map₂_comp, Category.assoc]
    rw [← cancel_mono (whiskerRightIso (R := R) (G.1.mapId (T.obj a))
      (G.1.map (T.map f))).hom]
    dsimp only [whiskerRightIso]
    simp only [Category.assoc]
    erw [inv_hom_whiskerRight R]
    rw [← cancel_epi (whiskerLeftIso (R := R)
      (G.1.map ((extend (restrict T)).map f)) (G.1.mapId (T.obj b))).hom]
    dsimp only [whiskerLeftIso]
    erw [whiskerLeft_hom_inv_assoc R]
    erw [reassoc_of% G.1.map₂_rightUnitor]
    rw [← cancel_mono (G.1.mapComp (𝟙 (T.obj a)) (T.map f)).hom]
    simp only [Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id]
    rw [← cancel_mono (G.1.map₂Iso (leftUnitor (T.map f))).hom]
    dsimp only [TwoSuperfunctor.map₂Iso]
    simp only [Category.assoc]
    erw [G.1.map₂_leftUnitor]
    simp only [Iso.inv_hom_id, Category.comp_id]
    erw [Category.id_comp, ← G.1.map₂_comp, Iso.inv_hom_id, G.1.map₂_id, Category.comp_id])


-- @@ L133-137 verbatim
theorem postcomposeDensityIso_hom_isHomogeneous :
    (postcomposeDensityIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨inv_mem _ (G.1.mapId_hom_mem (T.obj a)), by
    simpa using! inv_mem_degree _ (G.2.mapId_hom_mem_degree (T.obj a))⟩


-- @@ L139-141 verbatim
theorem postcomposeDensityIso_inv_isHomogeneous :
    (postcomposeDensityIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (postcomposeDensityIso_hom_isHomogeneous T hT G)


-- @@ L143-153 verbatim
/-- The normalized mapped density remains strong for arbitrary graded `G`. -/
theorem postcomposeDensity_isStrong : (postcomposeDensity T hT G).IsStrong := by
  intro a b f
  change IsIso ((rightUnitor _).hom ≫ G.1.map₂ (extendRestrictApp T hT f) ≫
    (leftUnitor _).inv)
  have := hT.isGradedSuperfunctor a b
  have : IsIso (extendRestrictApp T hT f) :=
    inferInstanceAs (IsIso ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f).hom)
  have : IsIso (G.1.map₂ (extendRestrictApp T hT f)) :=
    (G.1.mapFunctor _ _).map_isIso _
  infer_instance


-- @@ L155-161 verbatim
/-- The actual bridge from postcomposition of the common extension to the
chosen extension of the postcomposed restriction. No strict preservation of
chosen shifts by `G` is assumed. -/
def postcomposeDensityBridge :
    TwoNatTrans ((extend (restrict T)).comp G.1) (extend (restrict (T.comp G.1))) :=
  TwoNatTrans.vcomp (postcomposeDensity T hT G)
    (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))


-- @@ L163-165 verbatim
theorem postcomposeDensityBridge_isGraded : (postcomposeDensityBridge T hT G).IsGraded :=
  TwoNatTrans.IsGraded.vcomp (postcomposeDensity_isGraded T hT G)
    (extendRestrictNatTransInv_isGraded _ _)


-- @@ L167-169 verbatim
theorem postcomposeDensityBridge_isStrong : (postcomposeDensityBridge T hT G).IsStrong :=
  TwoNatTrans.vcomp_isStrong (postcomposeDensity_isStrong T hT G)
    (extendRestrictNatTransInv_isStrong _ _)


-- @@ L171-183 verbatim
/-- Cancel the chosen density pair after the bridge, retaining associators. -/
def postcomposeDensityBridgeCollapseIso :
    TwoNatTrans.vcomp (postcomposeDensityBridge T hT G)
      (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2)) ≅ postcomposeDensity T hT G :=
  associator (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
      (postcomposeDensity T hT G)
      (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
      (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2)) ≪≫
    TwoSupercategory.whiskerLeftIso (R := R)
      (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
      (postcomposeDensity T hT G) (extendRestrictUnitIso (T.comp G.1) (hT.comp G.2)) ≪≫
    rightUnitor (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
      (postcomposeDensity T hT G)


-- @@ L185-199 verbatim
theorem postcomposeDensityBridgeCollapseIso_hom_isHomogeneous :
    (postcomposeDensityBridgeCollapseIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  constructor
  · simpa only [zero_add] using! comp_mem
      (associator_hom_mem (R := R) ((postcomposeDensity T hT G).X a) _ _)
      (comp_mem (whiskerLeft_mem _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).1)
        (rightUnitor_hom_mem (R := R) _))
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.associator_hom_mem_degree (R := R)
        ((postcomposeDensity T hT G).X a) _ _)
      (comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).2)
        (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _))


-- @@ L201-207 verbatim
/-- Genuine even invertible supermodification factoring the actual
postcomposed density through the matching chosen density of `T.comp G`. -/
def postcomposeDensityFactorizationIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTrans T hT) ≅
      TwoNatTrans.vcomp (postcomposeDensityBridge T hT G)
        (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2)) :=
  postcomposeDensityIso T hT G ≪≫ (postcomposeDensityBridgeCollapseIso T hT G).symm


-- @@ L209-217 verbatim
theorem postcomposeDensityFactorizationIso_hom_isHomogeneous :
    (postcomposeDensityFactorizationIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  have h := TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeDensityBridgeCollapseIso_hom_isHomogeneous T hT G) a
  exact ⟨by simpa only [zero_add] using!
      comp_mem (postcomposeDensityIso_hom_isHomogeneous T hT G a).1 h.1,
    by simpa only [zero_add] using!
      comp_mem_degree (postcomposeDensityIso_hom_isHomogeneous T hT G a).2 h.2⟩


-- @@ L219-222 verbatim
theorem postcomposeDensityFactorizationIso_inv_isHomogeneous :
    (postcomposeDensityFactorizationIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeDensityFactorizationIso_hom_isHomogeneous T hT G)


-- @@ L224-233 verbatim
/-- Naturality of the factorization as a modification, at every shifted 1-cell. -/
theorem postcomposeDensityFactorizationIso_naturality
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.postcompose G.1 (extendRestrictNatTrans T hT)).x f ≫
        (postcomposeDensityFactorizationIso T hT G).hom.app a ▷ (T.comp G.1).map f =
      ((extend (restrict T)).comp G.1).map f ◁
        (postcomposeDensityFactorizationIso T hT G).hom.app b ≫
          (TwoNatTrans.vcomp (postcomposeDensityBridge T hT G)
            (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))).x f :=
  (postcomposeDensityFactorizationIso T hT G).hom.naturality f


-- @@ L235-237 verbatim
/-- The unit normalization really uses `G.mapId.inv`, not an identity. -/
theorem postcomposeDensityIso_hom_app (a : QPiTwoEnvelope R B) :
    (postcomposeDensityIso T hT G).hom.app a = (G.1.mapId (T.obj a)).inv := rfl


-- @@ L239-243 verbatim
theorem postcomposeDensityFactorizationIso_hom_inv_id :
    (postcomposeDensityFactorizationIso T hT G).hom ≫
      (postcomposeDensityFactorizationIso T hT G).inv =
        𝟙 (TwoNatTrans.postcompose G.1 (extendRestrictNatTrans T hT)) :=
  (postcomposeDensityFactorizationIso T hT G).hom_inv_id


-- @@ L245-250 verbatim
theorem postcomposeDensityFactorizationIso_inv_hom_id :
    (postcomposeDensityFactorizationIso T hT G).inv ≫
      (postcomposeDensityFactorizationIso T hT G).hom =
        𝟙 (TwoNatTrans.vcomp (postcomposeDensityBridge T hT G)
          (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))) :=
  (postcomposeDensityFactorizationIso T hT G).inv_hom_id


-- @@ L252-252 verbatim
section RightLegBoundary

-- @@ L253-253 verbatim
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R}


-- @@ L255-261 verbatim
/-- Restriction equality for exactly the transported right-leg endpoints. -/
theorem counitPasteRight_restrict (F : A ⟶ C) (G : C ⟶ D) :
    restrict ((mapQPi F.1).comp ((counit C).comp G.1)) =
      restrict ((counit A).comp (F ≫ G).1) := by
  rw [← counitPaste_middle F G, ← counitPaste_target F G]
  simpa only [restrict_eq_comp, TwoSuperfunctor.comp_assoc] using
    congrArg (fun H => H.comp G.1) (counit_naturality_restrict F)


-- @@ L263-270 verbatim
/-- The matching chosen density comparison, with both actual normalized
right-leg boundaries. The isomorphism from `counitPasteRight` is not yet asserted. -/
def counitPasteRightComparison (F : A ⟶ C) (G : C ⟶ D) : TwoNatTrans
    ((mapQPi F.1).comp ((counit C).comp G.1))
    ((counit A).comp (F ≫ G).1) :=
  comparison (B := A.toGTwoSCat) _ _
    ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))
    ((counit_isGraded A).comp (F.2.comp G.2)) (counitPasteRight_restrict F G)

-- @@ L271-271 verbatim
end RightLegBoundary


-- @@ L273-282 verbatim
/-!
Remaining right-leg obligation: construct an even degree-zero isomorphism
`counitPasteRight F G ≅ counitPasteRightComparison F G`. The bridge above is
proved separately for each envelope functor `T`. To finish that obligation,
identify the bridges for `S = (mapQPi F.1).comp (counit C)` and
`T = (counit A).comp F.1` along `counit_naturality_restrict F`, supply the
inverse-density factorization and the compositor modification for
postcomposition of their vertical composite, then transport both boundaries.
None of these are replaced by equality of postcomposed transformation records.
-/


-- @@ L284-284 verbatim
end QPiTwoEnvelope

-- @@ L285-285 verbatim
end StringDiagrams
