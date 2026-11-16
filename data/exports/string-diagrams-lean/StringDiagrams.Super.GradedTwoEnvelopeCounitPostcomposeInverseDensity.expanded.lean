import StringDiagrams.Super.GradedTwoEnvelopeCounitPostcomposeComposition


-- @@ L3-9 verbatim
/-!
# Actual postcomposition of inverse density

The inverse-density prerequisite for right counit-paste. This module keeps the
original inverse transformation, arbitrary postcomposition constraints, and the
coherent inverse bridge. It does not assert the full right-paste comparison.
-/

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace StringDiagrams

-- @@ L12-12 verbatim
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

-- @@ L13-13 verbatim
universe w w₁ v₁ u₁

-- @@ L14-14 verbatim
variable {R : Type w} [CommRing R]

-- @@ L15-15 verbatim
namespace QPiTwoEnvelope

-- @@ L16-16 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L17-20 verbatim
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R}
  {C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  (T : TwoSuperfunctor R (QPiTwoEnvelope R B) C) (hT : T.IsGraded)
  (G : C ⟶ D)

-- @@ L21-22 verbatim
local instance : ∀ a b : C, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

-- @@ L23-24 verbatim
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b


-- @@ L26-30 verbatim
/-- The density cell after mapping its middle factor, with target unitors. -/
def postcomposeInverseDensityX {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    G.1.map (T.map f) ≫ 𝟙 (G.1.obj (T.obj b)) ⟶
      𝟙 (G.1.obj (T.obj a)) ≫ G.1.map ((extend (restrict T)).map f) :=
  (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT f) ≫ (leftUnitor _).inv


-- @@ L32-37 verbatim
theorem postcomposeInverseDensityX_mem {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    postcomposeInverseDensityX T hT G f ∈ parity (R := R) _ _ 0 := by
  simpa only [postcomposeInverseDensityX, zero_add] using! comp_mem
    (rightUnitor_hom_mem (R := R) _)
    (comp_mem (G.1.map₂_mem (extendRestrictAppInv_mem T hT f))
      (inv_mem _ (leftUnitor_hom_mem (R := R) _)))


-- @@ L39-50 verbatim
/-- Naturality includes odd and nonzero-degree input 2-morphisms. -/
theorem postcomposeInverseDensityX_naturality {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    G.1.map₂ (T.map₂ η) ▷ 𝟙 (G.1.obj (T.obj b)) ≫
        postcomposeInverseDensityX T hT G g =
      postcomposeInverseDensityX T hT G f ≫ 𝟙 (G.1.obj (T.obj a)) ◁ G.1.map₂ ((extend (restrict T)).map₂ η) := by
  unfold postcomposeInverseDensityX
  erw [rightUnitor_naturality_assoc R, ← reassoc_of% G.1.map₂_comp,
    extendRestrictAppInv_naturality, G.1.map₂_comp]
  simp only [Category.assoc]
  erw [leftUnitor_inv_naturality R (G.1.map₂ ((extend (restrict T)).map₂ η))]
  rfl


-- @@ L52-90 verbatim
/-- The actual mapped inverse density, normalized by the unit constraint of `G`. -/
def postcomposeInverseDensity :
    TwoNatTrans (T.comp G.1) ((extend (restrict T)).comp G.1) where
  X a := 𝟙 (G.1.obj (T.obj a))
  x f := postcomposeInverseDensityX T hT G f
  x_mem f := postcomposeInverseDensityX_mem T hT G f
  naturality η := postcomposeInverseDensityX_naturality T hT G η
  x_comp f g := xcomp_of_J (F' := T.comp G.1) (G' := (extend (restrict T)).comp G.1)
    (fun a => 𝟙 (G.1.obj (T.obj a))) (fun f => postcomposeInverseDensityX T hT G f)
    (fun f => postcomposeInverseDensityX_mem T hT G f)
    (fun η => postcomposeInverseDensityX_naturality T hT G η)
    (fun {a b c} f g => by
      have h₁ : ((T.comp G.1).mapComp (Jm (R := R) f) (Jm g)).hom =
          (((extend (restrict T)).comp G.1).mapComp (Jm f) (Jm g)).hom := by
        simp only [TwoSuperfunctor.comp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom,
          extendComp_J, restrict_mapComp]
        rfl
      have h₂ := extendRestrictAppInv_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) (f ≫ g)
      have h₃ := extendRestrictAppInv_J T hT (a := (⟨⟨a⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B)) f
      have h₄ := extendRestrictAppInv_J T hT (a := (⟨⟨b⟩⟩ : QPiTwoEnvelope R B))
        (b := (⟨⟨c⟩⟩ : QPiTwoEnvelope R B)) g
      simp only [xcompL, xcompR, postcomposeInverseDensityX]
      erw [h₂, h₃, h₄, G.1.map₂_id, G.1.map₂_id, G.1.map₂_id]
      simp only [Category.id_comp]
      erw [h₁]
      exact TwoEnvelope.unit_coherence R (G.1.map (T.map (Jm f)))
        (G.1.map (T.map (Jm g))) (((extend (restrict T)).comp G.1).mapComp (Jm f) (Jm g)).hom) f g
  x_id a := by
    have h : extendRestrictAppInv T hT (𝟙 a) = 𝟙 _ := extendRestrictAppInv_J T hT (𝟙 a.as.as)
    show _ ≫ _ ≫ _ ≫ (rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT (𝟙 a)) ≫
      (leftUnitor _).inv = _
    erw [h, G.1.map₂_id, Category.id_comp, rightUnitor_naturality_assoc R]
    erw [leftUnitor_inv_naturality R]
    erw [unitors_inv_equal R]
    simp only [Iso.hom_inv_id_assoc]
    erw [Iso.hom_inv_id_assoc]
    rfl


-- @@ L92-97 verbatim
theorem postcomposeInverseDensity_isGraded : (postcomposeInverseDensity T hT G).IsGraded := by
  intro a b f
  simpa only [postcomposeInverseDensity, postcomposeInverseDensityX, zero_add] using! comp_mem_degree
    (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) _)
    (comp_mem_degree (G.2.map₂_mem_degree (extendRestrictAppInv_mem_degree T hT f))
      (GradedTwoSupercategory.leftUnitor_inv_mem_degree (R := R) _))


-- @@ L99-109 verbatim
/-- Invertibility of all normalized inverse-density cells, for arbitrary graded `G`. -/
theorem postcomposeInverseDensity_isStrong : (postcomposeInverseDensity T hT G).IsStrong := by
  intro a b f
  change IsIso ((rightUnitor _).hom ≫ G.1.map₂ (extendRestrictAppInv T hT f) ≫
    (leftUnitor _).inv)
  have := hT.isGradedSuperfunctor a b
  have : IsIso (extendRestrictAppInv T hT f) :=
    inferInstanceAs (IsIso ((QPiEnvelope.extendRestrictIso (homFunctor T a b)).app f).inv)
  have : IsIso (G.1.map₂ (extendRestrictAppInv T hT f)) :=
    (G.1.mapFunctor _ _).map_isIso _
  infer_instance


-- @@ L111-142 verbatim
/-- Mapping the inverse density transformation is isomorphic, not equal, to its unit
normalization. The components are precisely the inverses of `G.mapId`. -/
def postcomposeInverseDensityIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT) ≅
      postcomposeInverseDensity T hT G :=
  TwoEnvelope.supermodificationIso (fun a => (G.1.mapId (T.obj a)).symm) (by
    intro a b f
    change ((G.1.mapComp _ _).hom ≫
      G.1.map₂ ((rightUnitor _).hom ≫ extendRestrictAppInv T hT f ≫ (leftUnitor _).inv) ≫
      (G.1.mapComp _ _).inv) ≫ (G.1.mapId _).inv ▷ _ =
        _ ◁ (G.1.mapId _).inv ≫ (rightUnitor _).hom ≫
          G.1.map₂ (extendRestrictAppInv T hT f) ≫ (leftUnitor _).inv
    simp only [G.1.map₂_comp, Category.assoc]
    rw [← cancel_mono (whiskerRightIso (R := R) (G.1.mapId (T.obj a))
      (G.1.map ((extend (restrict T)).map f))).hom]
    dsimp only [whiskerRightIso]
    simp only [Category.assoc]
    erw [inv_hom_whiskerRight R]
    rw [← cancel_epi (whiskerLeftIso (R := R)
      (G.1.map (T.map f)) (G.1.mapId (T.obj b))).hom]
    dsimp only [whiskerLeftIso]
    erw [whiskerLeft_hom_inv_assoc R]
    erw [reassoc_of% G.1.map₂_rightUnitor]
    rw [← cancel_mono (G.1.mapComp (𝟙 (T.obj a)) ((extend (restrict T)).map f)).hom]
    simp only [Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id]
    rw [← cancel_mono (G.1.map₂Iso (leftUnitor ((extend (restrict T)).map f))).hom]
    dsimp only [TwoSuperfunctor.map₂Iso]
    simp only [Category.assoc]
    erw [G.1.map₂_leftUnitor]
    simp only [Iso.inv_hom_id, Category.comp_id]
    erw [Category.id_comp, ← G.1.map₂_comp, Iso.inv_hom_id, G.1.map₂_id, Category.comp_id])


-- @@ L144-148 verbatim
theorem postcomposeInverseDensityIso_hom_isHomogeneous :
    (postcomposeInverseDensityIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨inv_mem _ (G.1.mapId_hom_mem (T.obj a)), by
    simpa using! inv_mem_degree _ (G.2.mapId_hom_mem_degree (T.obj a))⟩


-- @@ L150-152 verbatim
theorem postcomposeInverseDensityIso_inv_isHomogeneous :
    (postcomposeInverseDensityIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (postcomposeInverseDensityIso_hom_isHomogeneous T hT G)


-- @@ L154-161 verbatim
/-- Both normalized transformations use the original mutually inverse density cells. -/
def postcomposeDensityCounitIso :
    TwoNatTrans.vcomp (postcomposeDensity T hT G) (postcomposeInverseDensity T hT G) ≅
      TwoNatTrans.id ((extend (restrict T)).comp G.1) :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (G.1.obj (T.obj a)))) fun f =>
    vcomp_unitors_naturality R _ _ (by
      rw [← G.1.map₂_comp, extendRestrictApp_comp_inv, G.1.map₂_id]
      rfl)


-- @@ L163-169 verbatim
def postcomposeDensityUnitIso :
    TwoNatTrans.vcomp (postcomposeInverseDensity T hT G) (postcomposeDensity T hT G) ≅
      TwoNatTrans.id (T.comp G.1) :=
  TwoEnvelope.supermodificationIso (fun a => leftUnitor (𝟙 (G.1.obj (T.obj a)))) fun f =>
    vcomp_unitors_naturality R _ _ (by
      rw [← G.1.map₂_comp, extendRestrictAppInv_comp, G.1.map₂_id]
      rfl)


-- @@ L171-173 verbatim
theorem postcomposeDensityCounitIso_hom_isHomogeneous :
    (postcomposeDensityCounitIso T hT G).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩


-- @@ L175-177 verbatim
theorem postcomposeDensityUnitIso_hom_isHomogeneous :
    (postcomposeDensityUnitIso T hT G).hom.IsHomogeneous 0 0 := fun _ =>
  ⟨leftUnitor_hom_mem (R := R) _, GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _⟩


-- @@ L179-185 verbatim
/-- The reverse bridge: chosen forward density, then the actual normalized inverse.
The order is forced by its endpoints; the following two isomorphisms verify that
it is a coherent inverse of the pre-existing `postcomposeDensityBridge`. -/
def postcomposeDensityBridgeInv :
    TwoNatTrans (extend (restrict (T.comp G.1))) ((extend (restrict T)).comp G.1) :=
  TwoNatTrans.vcomp (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeInverseDensity T hT G)


-- @@ L187-190 verbatim
theorem postcomposeDensityBridgeInv_isGraded :
    (postcomposeDensityBridgeInv T hT G).IsGraded :=
  TwoNatTrans.IsGraded.vcomp (extendRestrictNatTrans_isGraded _ _)
    (postcomposeInverseDensity_isGraded T hT G)


-- @@ L192-197 verbatim
/-- The original forward bridge followed by the inverse bridge cancels coherently. -/
def postcomposeDensityBridgeCounitIso :
    TwoNatTrans.vcomp (postcomposeDensityBridge T hT G) (postcomposeDensityBridgeInv T hT G) ≅
      TwoNatTrans.id ((extend (restrict T)).comp G.1) :=
  TwoNatTrans.cancelComparison _ _ _ _ (postcomposeDensityCounitIso T hT G)
    (extendRestrictUnitIso (T.comp G.1) (hT.comp G.2))


-- @@ L199-204 verbatim
/-- The reverse order also cancels, without strictifying any constraint. -/
def postcomposeDensityBridgeUnitIso :
    TwoNatTrans.vcomp (postcomposeDensityBridgeInv T hT G) (postcomposeDensityBridge T hT G) ≅
      TwoNatTrans.id (extend (restrict (T.comp G.1))) :=
  TwoNatTrans.cancelComparison _ _ _ _
    (extendRestrictCounitIso (T.comp G.1) (hT.comp G.2)) (postcomposeDensityUnitIso T hT G)


-- @@ L206-210 verbatim
theorem postcomposeDensityBridgeCounitIso_hom_isHomogeneous :
    (postcomposeDensityBridgeCounitIso T hT G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.cancelComparison_hom_isHomogeneous _ _ _ _ _ _
    (postcomposeDensityCounitIso_hom_isHomogeneous T hT G)
    (extendRestrictUnitIso_hom_isHomogeneous _ _)


-- @@ L212-216 verbatim
theorem postcomposeDensityBridgeUnitIso_hom_isHomogeneous :
    (postcomposeDensityBridgeUnitIso T hT G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.cancelComparison_hom_isHomogeneous _ _ _ _ _ _
    (extendRestrictCounitIso_hom_isHomogeneous _ _)
    (postcomposeDensityUnitIso_hom_isHomogeneous T hT G)


-- @@ L218-229 verbatim
/-- Cancel inverse density followed by forward density before the reverse bridge. -/
def postcomposeInverseDensityBridgeCollapseIso :
    TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
      (postcomposeDensityBridgeInv T hT G) ≅ postcomposeInverseDensity T hT G :=
  (associator (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
    (extendRestrictNatTrans (T.comp G.1) (hT.comp G.2))
    (postcomposeInverseDensity T hT G)).symm ≪≫
  TwoSupercategory.whiskerRightIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (extendRestrictUnitIso (T.comp G.1) (hT.comp G.2)) (postcomposeInverseDensity T hT G) ≪≫
  leftUnitor (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D) (postcomposeInverseDensity T hT G)


-- @@ L231-245 verbatim
theorem postcomposeInverseDensityBridgeCollapseIso_hom_isHomogeneous :
    (postcomposeInverseDensityBridgeCollapseIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  constructor
  · simpa only [zero_add] using! comp_mem
      (inv_mem _ (associator_hom_mem (R := R) _ _ ((postcomposeInverseDensity T hT G).X a)))
      (comp_mem (whiskerRight_mem _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).1)
        (leftUnitor_hom_mem (R := R) _))
  · simpa only [zero_add] using! comp_mem_degree
      (GradedTwoSupercategory.associator_inv_mem_degree (R := R) _ _
        ((postcomposeInverseDensity T hT G).X a))
      (comp_mem_degree (GradedTwoSupercategory.whiskerRight_mem_degree _
        (extendRestrictUnitIso_hom_isHomogeneous (T.comp G.1) (hT.comp G.2) a).2)
        (GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) _))


-- @@ L247-253 verbatim
/-- Factor the original postcomposed inverse density, not a replacement:
first inverse density of `T.comp G`, then the coherent inverse bridge. -/
def postcomposeInverseDensityFactorizationIso :
    TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT) ≅
      TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
        (postcomposeDensityBridgeInv T hT G) :=
  postcomposeInverseDensityIso T hT G ≪≫ (postcomposeInverseDensityBridgeCollapseIso T hT G).symm


-- @@ L255-263 verbatim
theorem postcomposeInverseDensityFactorizationIso_hom_isHomogeneous :
    (postcomposeInverseDensityFactorizationIso T hT G).hom.IsHomogeneous 0 0 := by
  intro a
  have h := TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeInverseDensityBridgeCollapseIso_hom_isHomogeneous T hT G) a
  exact ⟨by simpa only [zero_add] using!
      comp_mem (postcomposeInverseDensityIso_hom_isHomogeneous T hT G a).1 h.1,
    by simpa only [zero_add] using!
      comp_mem_degree (postcomposeInverseDensityIso_hom_isHomogeneous T hT G a).2 h.2⟩


-- @@ L265-268 verbatim
theorem postcomposeInverseDensityFactorizationIso_inv_isHomogeneous :
    (postcomposeInverseDensityFactorizationIso T hT G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous T hT G)


-- @@ L270-272 verbatim
/-- The unit constraint is not silently replaced by an identity. -/
theorem postcomposeInverseDensityIso_hom_app (a : QPiTwoEnvelope R B) :
    (postcomposeInverseDensityIso T hT G).hom.app a = (G.1.mapId (T.obj a)).inv := rfl


-- @@ L274-283 verbatim
/-- Both arbitrary shifted cells and the full postcomposition compositor survive. -/
theorem postcomposeInverseDensityFactorizationIso_hom_naturality
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f ≫
        (postcomposeInverseDensityFactorizationIso T hT G).hom.app a ▷
          ((extend (restrict T)).comp G.1).map f =
      (T.comp G.1).map f ◁ (postcomposeInverseDensityFactorizationIso T hT G).hom.app b ≫
        (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
          (postcomposeDensityBridgeInv T hT G)).x f :=
  (postcomposeInverseDensityFactorizationIso T hT G).hom.naturality f


-- @@ L285-293 verbatim
theorem postcomposeInverseDensityFactorizationIso_inv_naturality
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
        (postcomposeDensityBridgeInv T hT G)).x f ≫
        (postcomposeInverseDensityFactorizationIso T hT G).inv.app a ▷
          ((extend (restrict T)).comp G.1).map f =
      (T.comp G.1).map f ◁ (postcomposeInverseDensityFactorizationIso T hT G).inv.app b ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f :=
  (postcomposeInverseDensityFactorizationIso T hT G).inv.naturality f


-- @@ L295-299 verbatim
theorem postcomposeInverseDensityFactorizationIso_hom_inv_id :
    (postcomposeInverseDensityFactorizationIso T hT G).hom ≫
      (postcomposeInverseDensityFactorizationIso T hT G).inv =
        𝟙 (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)) :=
  (postcomposeInverseDensityFactorizationIso T hT G).hom_inv_id


-- @@ L301-306 verbatim
theorem postcomposeInverseDensityFactorizationIso_inv_hom_id :
    (postcomposeInverseDensityFactorizationIso T hT G).inv ≫
      (postcomposeInverseDensityFactorizationIso T hT G).hom =
        𝟙 (TwoNatTrans.vcomp (extendRestrictNatTransInv (T.comp G.1) (hT.comp G.2))
          (postcomposeDensityBridgeInv T hT G)) :=
  (postcomposeInverseDensityFactorizationIso T hT G).inv_hom_id


-- @@ L308-316 verbatim
/-- Naturality of the original transformation for every 2-morphism, including odd ones. -/
theorem postcomposeActualInverseDensity_naturality
    {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (T.comp G.1).map₂ η ▷ (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).X b ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x g =
      (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).x f ≫
        (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).X a ◁
          ((extend (restrict T)).comp G.1).map₂ η :=
  (TwoNatTrans.postcompose G.1 (extendRestrictNatTransInv T hT)).naturality η


-- @@ L318-318 verbatim
section ComparisonConsumer

-- @@ L319-320 verbatim
variable (S : TwoSuperfunctor R (QPiTwoEnvelope R B) C)
  (hS : S.IsGraded) (h : restrict S = restrict T)


-- @@ L322-329 verbatim
/-- The original density pair with only its inverse-density leg factored.
The forward leg's actual source transport is deliberately retained. -/
def postcomposeComparisonInverseFactoredPair : TwoNatTrans (S.comp G.1) (T.comp G.1) :=
  TwoNatTrans.vcomp
    (TwoNatTrans.vcomp (extendRestrictNatTransInv (S.comp G.1) (hS.comp G.2))
      (postcomposeDensityBridgeInv S hS G))
    (TwoNatTrans.postcompose G.1
      (TwoNatTrans.transportSource (congrArg extend h.symm) (extendRestrictNatTrans T hT)))


-- @@ L331-337 verbatim
/-- Apply the inverse-density factorization to the existing, actual separated pair. -/
def postcomposeComparisonDensityPairInverseIso :
    postcomposeComparisonDensityPair S T hS hT h G ≅
      postcomposeComparisonInverseFactoredPair T hT G S hS h :=
  TwoSupercategory.whiskerRightIso (R := R)
    (B := TwoSuperfunctor R (QPiTwoEnvelope R B) D)
    (postcomposeInverseDensityFactorizationIso S hS G) _


-- @@ L339-344 verbatim
theorem postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous :
    (postcomposeComparisonDensityPairInverseIso T hT G S hS h).hom.IsHomogeneous 0 0 := by
  intro a
  exact ⟨whiskerRight_mem _ (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous S hS G a).1,
    GradedTwoSupercategory.whiskerRight_mem_degree _
      (postcomposeInverseDensityFactorizationIso_hom_isHomogeneous S hS G a).2⟩


-- @@ L346-349 verbatim
theorem postcomposeComparisonDensityPairInverseIso_inv_isHomogeneous :
    (postcomposeComparisonDensityPairInverseIso T hT G S hS h).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous T hT G S hS h)

-- @@ L350-350 verbatim
end ComparisonConsumer


-- @@ L352-352 verbatim
section CounitConsumer

-- @@ L353-353 verbatim
variable {A : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : A ⟶ C)


-- @@ L355-360 verbatim
/-- Consumer at exactly `S = mapQPi F ⋙ counit C`, `T = counit A ⋙ F`
and the actual `counit_naturality_restrict F`, with no invented equality. -/
def counitNaturalityPostcomposeInverseFactoredPair : TwoNatTrans
    (((mapQPi F.1).comp (counit C)).comp G.1) (((counit A).comp F.1).comp G.1) :=
  postcomposeComparisonInverseFactoredPair _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F)


-- @@ L362-367 verbatim
/-- Factor the actual inverse-density leg of the actual counit density pair. -/
def counitNaturalityPostcomposeDensityPairInverseIso :
    counitNaturalityPostcomposeDensityPair G F ≅
      counitNaturalityPostcomposeInverseFactoredPair G F :=
  postcomposeComparisonDensityPairInverseIso _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F)


-- @@ L369-373 verbatim
/-- The resulting isomorphism starts at the original postcomposed counit transformation. -/
def counitNaturalityPostcomposeInverseFactorizationIso :
    TwoNatTrans.postcompose G.1 (counitNaturality F) ≅
      counitNaturalityPostcomposeInverseFactoredPair G F :=
  counitNaturalityPostcomposeIso G F ≪≫ counitNaturalityPostcomposeDensityPairInverseIso G F


-- @@ L375-384 verbatim
theorem counitNaturalityPostcomposeInverseFactorizationIso_hom_isHomogeneous :
    (counitNaturalityPostcomposeInverseFactorizationIso G F).hom.IsHomogeneous 0 0 := by
  intro a
  have h := postcomposeComparisonDensityPairInverseIso_hom_isHomogeneous
    _ ((counit_isGraded A).comp F.2) G
    _ ((mapQPi_isGraded F.2).comp (counit_isGraded C)) (counit_naturality_restrict F) a
  exact ⟨by simpa only [zero_add] using!
      comp_mem (counitNaturalityPostcomposeIso_hom_isHomogeneous G F a).1 h.1,
    by simpa only [zero_add] using!
      comp_mem_degree (counitNaturalityPostcomposeIso_hom_isHomogeneous G F a).2 h.2⟩


-- @@ L386-389 verbatim
theorem counitNaturalityPostcomposeInverseFactorizationIso_inv_isHomogeneous :
    (counitNaturalityPostcomposeInverseFactorizationIso G F).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _
    (counitNaturalityPostcomposeInverseFactorizationIso_hom_isHomogeneous G F)

-- @@ L390-390 verbatim
end CounitConsumer


-- @@ L392-392 verbatim
end QPiTwoEnvelope

-- @@ L393-393 verbatim
end StringDiagrams
