import ModularCurves.Picard.DualPullback.PullbackSection


-- @@ L3-8 verbatim
/-!
# Pullback sections over open subschemes

Component formulas comparing the local and global adjunction units and transporting a
module section to the corresponding open subscheme.
-/


-- @@ L10-10 verbatim
universe u


-- @@ L12-12 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L15-15 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L17-17 verbatim
variable {X Y : Scheme.{u}}


-- @@ L19-62 verbatim
theorem openPullbackSquareExplicitIso_unit_homT
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    let localAdj := (restrictAdjunction U.ι).comp
      (pullbackPushforwardAdjunction (f ∣_ U))
    let globalAdj := (pullbackPushforwardAdjunction f).comp
      (restrictAdjunction (f ⁻¹ᵁ U).ι)
    let r := openPushforwardSquareIsoT f U
    let e := openPullbackSquareExplicitIsoT f U
    localAdj.unit.app M ≫ r.hom.app
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M) ≫
        (pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).map (e.hom.app M) =
      globalAdj.unit.app M := by
  dsimp only
  let localAdj := (restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let globalAdj := (pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)
  let r := openPushforwardSquareIsoT f U
  let e := openPullbackSquareExplicitIsoT f U
  have h := unit_conjugateEquiv localAdj globalAdj e.inv M
  have hconj : conjugateEquiv localAdj globalAdj e.inv = r.hom :=
    conjugateEquiv_openPullbackSquareExplicitIso_invT f U
  rw [hconj] at h
  let G := pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f
  have hmap : G.map (e.inv.app M) ≫
      G.map (e.hom.app M) = CategoryStruct.id _ := by
    rw [← G.map_comp, e.inv_hom_id_app, G.map_id]
  calc
    localAdj.unit.app M ≫ r.hom.app
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M) ≫
          G.map (e.hom.app M) =
        (localAdj.unit.app M ≫ r.hom.app
          ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)) ≫
            G.map (e.hom.app M) := (Category.assoc _ _ _).symm
    _ =
        (globalAdj.unit.app M ≫
          G.map (e.inv.app M)) ≫ G.map (e.hom.app M) := by
      exact congrArg (fun q ↦ q ≫ G.map (e.hom.app M)) h
    _ = globalAdj.unit.app M ≫
        (G.map (e.inv.app M) ≫ G.map (e.hom.app M)) :=
      Category.assoc _ _ _
    _ = globalAdj.unit.app M ≫ CategoryStruct.id _ :=
      congrArg (fun q ↦ globalAdj.unit.app M ≫ q) hmap
    _ = globalAdj.unit.app M := Category.comp_id _


-- @@ L64-64 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L66-66 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L69-69 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L71-71 verbatim
variable {X Y : Scheme.{u}}


-- @@ L73-78 verbatim
noncomputable def openUnitLocalT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) : M ⟶
      ((pushforward (f ∣_ U) ⋙ pushforward U.ι).obj
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)) :=
  ((restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))).unit.app M


-- @@ L80-87 verbatim
noncomputable def openUnitSquareT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) :
    ((pushforward (f ∣_ U) ⋙ pushforward U.ι).obj
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)) ⟶
      ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)) :=
  (openPushforwardSquareIsoT f U).hom.app
    ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)


-- @@ L89-96 verbatim
noncomputable def openUnitComparisonT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)) ⟶
      ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj
        ((pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) :=
  (pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).map
    ((openPullbackSquareExplicitIsoT f U).hom.app M)


-- @@ L98-103 verbatim
noncomputable def openUnitGlobalT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) : M ⟶
      ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj
        ((pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) :=
  ((pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)).unit.app M


-- @@ L105-110 verbatim
theorem openUnitStages_eqT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) :
    openUnitLocalT f M U ≫ openUnitSquareT f M U ≫
        openUnitComparisonT f M U =
      openUnitGlobalT f M U :=
  openPullbackSquareExplicitIso_unit_homT f M U


-- @@ L112-121 verbatim
theorem openUnitLocal_eqT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) :
    openUnitLocalT f M U =
      (restrictAdjunction U.ι).unit.app M ≫
        (pushforward U.ι).map
          ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj M)) := by
  exact Adjunction.comp_unit_app
    (restrictAdjunction U.ι)
    (pullbackPushforwardAdjunction (f ∣_ U)) M


-- @@ L123-132 verbatim
theorem openUnitGlobal_eqT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) :
    openUnitGlobalT f M U =
      (pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map
          ((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app
            ((pullback f).obj M)) := by
  exact Adjunction.comp_unit_app
    (pullbackPushforwardAdjunction f)
    (restrictAdjunction (f ⁻¹ᵁ U).ι) M


-- @@ L134-139 verbatim
theorem three_comp_app_applyT
    {A B C D : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (W : Opposite X.Opens) (x : A.val.obj W) :
    (a ≫ b ≫ c).val.app W x =
      c.val.app W (b.val.app W (a.val.app W x)) := by
  rfl


-- @@ L141-150 verbatim
theorem openUnitStages_app_applyT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    (openUnitComparisonT f M U).val.app (.op U)
        ((openUnitSquareT f M U).val.app (.op U)
          ((openUnitLocalT f M U).val.app (.op U) x)) =
      (openUnitGlobalT f M U).val.app (.op U) x := by
  have h := congrArg (fun q ↦ q.val.app (.op U) x)
    (openUnitStages_eqT f M U)
  rw [three_comp_app_applyT] at h
  exact h


-- @@ L152-152 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L154-154 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L157-157 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L159-159 verbatim
variable {X Y : Scheme.{u}}


-- @@ L161-165 verbatim
local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b


-- @@ L167-175 verbatim
theorem pushforwardCongr_hom_app_applyQ
    {A B : Scheme.{u}} {g h : A ⟶ B} (hg : g = h)
    (N : A.Modules) (W : B.Opens)
    (x : ((pushforward g).obj N).val.obj (.op W)) :
    (((pushforwardCongr hg).hom.app N).val.app (.op W)) x =
      N.presheaf.map
        (eqToHom (show h ⁻¹ᵁ W = g ⁻¹ᵁ W from hg ▸ rfl)).op x := by
  have hc := pushforwardCongr_hom_app_app (M := N) hg W
  exact ConcreteCategory.congr_hom hc x


-- @@ L177-183 verbatim
noncomputable def openPushforwardSquareIsoQ (f : Y ⟶ X)
    (U : X.Opens) :
    pushforward (f ∣_ U) ⋙ pushforward U.ι ≅
      pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f :=
  pushforwardComp (f ∣_ U) U.ι ≪≫
    pushforwardCongr (morphismRestrict_ι f U) ≪≫
    (pushforwardComp (f ⁻¹ᵁ U).ι f).symm


-- @@ L185-196 verbatim
theorem openPushforwardSquareIsoQ_hom_app_app
    (f : Y ⟶ X) (U : X.Opens)
    (N : (f ⁻¹ᵁ U).toScheme.Modules) (W : X.Opens) :
    ((openPushforwardSquareIsoQ f U).hom.app N).val.app (.op W) =
      ((pushforwardCongr (morphismRestrict_ι f U)).hom.app N).val.app
        (.op W) := by
  simp only [openPushforwardSquareIsoQ, Iso.trans_hom,
    NatTrans.comp_app]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  erw [sheafOfModules_comp_app_apply]


-- @@ L198-205 verbatim
theorem dualObj_presheaf_map_applyQ (M : X.Modules)
    {V W : Opposite X.Opens} (i : V ⟶ W)
    (alpha : M.over V.unop ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over V.unop)) :
    ((dualObj M).presheaf.map i) alpha =
      ModularCurves.SheafOfModules.dualRestrict
        X.ringCatSheaf M i alpha := by
  rfl


-- @@ L207-243 verbatim
theorem openPushforwardSquareIsoQ_dual_app_apply
    (f : Y ⟶ X) (U : X.Opens)
    (N : (f ⁻¹ᵁ U).toScheme.Modules) (W : X.Opens)
    (x : (dualObj N).val.obj
      (.op ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W)))) :
    let hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ W)
        (morphismRestrict_ι f U).symm
    (((openPushforwardSquareIsoQ f U).hom.app (dualObj N)).val.app
      (.op W)) x =
        ModularCurves.SheafOfModules.dualRestrict
          (f ⁻¹ᵁ U).toScheme.ringCatSheaf N
          (eqToHom hpre).op x := by
  dsimp only
  have hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ W)
      (morphismRestrict_ι f U).symm
  have hopen := ConcreteCategory.congr_hom
    (openPushforwardSquareIsoQ_hom_app_app f U (dualObj N) W) x
  have hcongr :
      (((pushforwardCongr (morphismRestrict_ι f U)).hom.app
        (dualObj N)).val.app (.op W)) x =
        (dualObj N).presheaf.map (eqToHom hpre).op x :=
    pushforwardCongr_hom_app_applyQ
      (morphismRestrict_ι f U) (dualObj N) W x
  have hdual :
      (dualObj N).presheaf.map (eqToHom hpre).op x =
        ModularCurves.SheafOfModules.dualRestrict
          (f ⁻¹ᵁ U).toScheme.ringCatSheaf N
          (eqToHom hpre).op x :=
    dualObj_presheaf_map_applyQ
      (X := (f ⁻¹ᵁ U).toScheme) N (eqToHom hpre).op x
  exact Eq.trans hopen (Eq.trans hcongr hdual)


-- @@ L245-245 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L247-247 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L250-250 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L252-252 verbatim
variable {X Y : Scheme.{u}}


-- @@ L254-262 verbatim
theorem openUnitLocal_app_applyT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    (openUnitLocalT f M U).val.app (.op U) x =
      ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((restrictFunctor U.ι).obj M)).val.app
          (.op (U.ι ⁻¹ᵁ U))
            (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x) := by
  rw [openUnitLocal_eqT]
  erw [sheafOfModules_comp_app_apply]


-- @@ L264-272 verbatim
theorem openUnitGlobal_app_applyT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (x : M.val.obj (.op U)) :
    (openUnitGlobalT f M U).val.app (.op U) x =
      ((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app
        ((pullback f).obj M)).val.app (.op (f ⁻¹ᵁ U))
          (((pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op U) x) := by
  rw [openUnitGlobal_eqT]
  erw [sheafOfModules_comp_app_apply]


-- @@ L274-281 verbatim
theorem openUnitComparison_app_applyT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (x : ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).val.obj
      (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)))) :
    (openUnitComparisonT f M U).val.app (.op U) x =
      (localPullbackRestrictIso f M U).hom.val.app
        (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) x := by
  rfl


-- @@ L283-315 verbatim
theorem openUnitSquare_app_applyT (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens)
    (x : ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).val.obj
      (.op ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U)))) :
    let hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg
        (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    (openUnitSquareT f M U).val.app (.op U) x =
      ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).presheaf.map
        (eqToHom hpre).op x := by
  dsimp only
  have hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg
      (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  have hopen := ConcreteCategory.congr_hom
    (openPushforwardSquareIsoQ_hom_app_app f U
      ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M) U) x
  have hcongr :
      (((pushforwardCongr (morphismRestrict_ι f U)).hom.app
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M)).val.app
          (.op U)) x =
        ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).presheaf.map
          (eqToHom hpre).op x :=
    pushforwardCongr_hom_app_applyQ
      (morphismRestrict_ι f U)
      ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M) U x
  exact Eq.trans hopen hcongr


-- @@ L317-381 verbatim
theorem localPullbackRestrictIso_unit_appT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    let hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg
        (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι f U).symm
    (localPullbackRestrictIso f M U).hom.val.app
        (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)))
      (((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).presheaf.map
        (eqToHom hpre).op
          (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj M)).val.app
              (.op (U.ι ⁻¹ᵁ U))
                (((restrictAdjunction U.ι).unit.app M).val.app
                  (.op U) x))) =
      ((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app
        ((pullback f).obj M)).val.app (.op (f ⁻¹ᵁ U))
          (((pullbackPushforwardAdjunction f).unit.app M).val.app
            (.op U) x) := by
  dsimp only
  have hpre : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg
      (fun q : (f ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ U)
      (morphismRestrict_ι f U).symm
  let localValue :
      ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).val.obj
        (.op ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))) :=
    ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((restrictFunctor U.ι).obj M)).val.app
        (.op (U.ι ⁻¹ᵁ U))
          (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x)
  let squareValue :
      ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).val.obj
        (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) :=
    ((restrictFunctor U.ι ⋙ pullback (f ∣_ U)).obj M).presheaf.map
      (eqToHom hpre).op localValue
  have hlocal :
      (openUnitLocalT f M U).val.app (.op U) x = localValue :=
    openUnitLocal_app_applyT f M U x
  have hstages := openUnitStages_app_applyT f M U x
  have hlocalNested := congrArg
    (fun y ↦ (openUnitComparisonT f M U).val.app (.op U)
      ((openUnitSquareT f M U).val.app (.op U) y)) hlocal
  have hstagesLocal :
      (openUnitComparisonT f M U).val.app (.op U)
          ((openUnitSquareT f M U).val.app (.op U) localValue) =
        (openUnitGlobalT f M U).val.app (.op U) x :=
    Eq.trans hlocalNested.symm hstages
  have hsquare :
      (openUnitSquareT f M U).val.app (.op U) localValue = squareValue :=
    openUnitSquare_app_applyT f M U localValue
  have hsquareNested := congrArg
    (fun y ↦ (openUnitComparisonT f M U).val.app (.op U) y) hsquare
  have hcomparison :
      (openUnitComparisonT f M U).val.app (.op U) squareValue =
        (localPullbackRestrictIso f M U).hom.val.app
          (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) squareValue :=
    openUnitComparison_app_applyT f M U squareValue
  have hglobal := openUnitGlobal_app_applyT f M U x
  exact Eq.trans hcomparison.symm
    (Eq.trans hsquareNested.symm (Eq.trans hstagesLocal hglobal))


-- @@ L383-383 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L385-385 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L388-388 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L390-390 verbatim
variable {X : Scheme.{u}}


-- @@ L392-397 verbatim
noncomputable def localModuleSection (M : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) (x : M.val.obj (.op U)) :
    ((overEquiv U).functor.obj (M.over U)).val.obj (.op W) :=
  ((overFunctorEquiv U).app M).inv.val.app (.op W)
    ((M.restrictAppIso U.ι W).inv
      (M.val.map (homOfLE (U.ι_image_le W)).op x))


-- @@ L399-406 verbatim
theorem overFunctorEquiv_hom_localModuleSectionT
    (M : X.Modules) (U : X.Opens) (W : U.toScheme.Opens)
    (x : M.val.obj (.op U)) :
    ((overFunctorEquiv U).app M).hom.val.app (.op W)
        (localModuleSection M U W x) =
      (M.restrictAppIso U.ι W).inv
        (M.val.map (homOfLE (U.ι_image_le W)).op x) := by
  exact iso_inv_hom_app_applyT ((overFunctorEquiv U).app M) (.op W) _


-- @@ L408-416 verbatim
theorem overFunctorEquiv_hom_localModuleSection_preimageT
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((overFunctorEquiv U).app M).hom.val.app (.op (U.ι ⁻¹ᵁ U))
        (localModuleSection M U (U.ι ⁻¹ᵁ U) x) =
      ((restrictAdjunction U.ι).unit.app M).val.app (.op U) x := by
  rw [overFunctorEquiv_hom_localModuleSectionT]
  change M.val.map (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ U))).op x =
    M.val.map (homOfLE (U.ι.image_preimage_le U)).op x
  exact M.val.congr_map_apply (Subsingleton.elim _ _) x


-- @@ L418-425 verbatim
theorem overFunctorEquiv_inv_restrictUnitT
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    ((overFunctorEquiv U).app M).inv.val.app (.op (U.ι ⁻¹ᵁ U))
        (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x) =
      localModuleSection M U (U.ι ⁻¹ᵁ U) x := by
  rw [← overFunctorEquiv_hom_localModuleSection_preimageT]
  exact iso_hom_inv_app_applyT ((overFunctorEquiv U).app M)
    (.op (U.ι ⁻¹ᵁ U)) _


-- @@ L427-427 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L429-429 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L432-432 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L434-434 verbatim
variable {X Y : Scheme.{u}}


-- @@ L436-472 verbatim
theorem localPullbackUnit_overFunctorT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (x : M.val.obj (.op U)) :
    let W := U.ι ⁻¹ᵁ U
    let g := f ∣_ U
    let q := ((overFunctorEquiv U).app M).hom
    ((pullback g).map q).val.app (.op (g ⁻¹ᵁ W))
        (((pullbackPushforwardAdjunction g).unit.app
          ((overEquiv U).functor.obj (M.over U))).val.app (.op W)
            (localModuleSection M U W x)) =
      ((pullbackPushforwardAdjunction g).unit.app
        ((restrictFunctor U.ι).obj M)).val.app (.op W)
          (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x) := by
  dsimp only
  let g := f ∣_ U
  let A := (overEquiv U).functor.obj (M.over U)
  let B := (restrictFunctor U.ι).obj M
  let q := ((overFunctorEquiv U).app M).hom
  have hnat := (pullbackPushforwardAdjunction g).unit.naturality q
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have happ := congrArg
    (fun r ↦ r.val.app (.op (U.ι ⁻¹ᵁ U))
      (localModuleSection M U (U.ι ⁻¹ᵁ U) x)) hnat
  conv_lhs at happ => erw [sheafOfModules_comp_app_apply]
  conv_rhs at happ => erw [sheafOfModules_comp_app_apply]
  have hsource := overFunctorEquiv_hom_localModuleSection_preimageT M U x
  let k := ((pullbackPushforwardAdjunction g).unit.app B).val.app
    (.op (U.ι ⁻¹ᵁ U))
  have hk := congrArg (fun z ↦ k z) hsource
  have hleft :
      ((pullbackPushforwardAdjunction g).unit.app B).val.app
          (.op (U.ι ⁻¹ᵁ U))
            (q.val.app (.op (U.ι ⁻¹ᵁ U))
              (localModuleSection M U (U.ι ⁻¹ᵁ U) x)) =
        ((pullbackPushforwardAdjunction g).unit.app B).val.app
          (.op (U.ι ⁻¹ᵁ U))
            (((restrictAdjunction U.ι).unit.app M).val.app (.op U) x) := hk
  exact Eq.trans happ.symm hleft


-- @@ L474-474 verbatim
end AlgebraicGeometry.Scheme.Modules
