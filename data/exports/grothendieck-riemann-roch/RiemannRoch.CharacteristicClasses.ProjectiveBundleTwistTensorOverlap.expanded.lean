/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.CharacteristicClasses.ProjectiveBundleTwistUnitFace


-- @@ L9-26 verbatim
/-!
# Chart-overlap independence of the glued twist tensor isomorphism

On a positive-rank projective bundle, the chartwise tensor-addition isomorphisms
`canonicalTwistingSheafTensorChartOverIso` agree on every overlap of chart ranges
(`canonicalTwistingSheafTensorChartRestrictionIndependence`). Consequently the conditional gluing
API of `ProjectiveBundleTwistTensorGlobal` applies unconditionally, giving the multiplication law
`canonicalTwistingSheafK0Class_mul : [O(d)] * [O(e)] = [O(d + e)]` in `K₀`.

The overlap is covered by common basic opens; on each, the equation is the composite of three
squares: cross-scheme tensor naturality of the twist restriction data
(`twistingSheafRestrictionData_tensorNaturality`) for the left and right legs, cross-scheme
naturality of `canonicalTwistingSheafRestrictionIso` derived from the descent-kernel lift, and the
basis-change tensor naturality in the middle. A general compatibility of
`restrictFunctorObjTensorSheafIso` with composite restrictions is proved along the way.
Two private range-restriction transports of `ProjectiveBundleTwistTensorGlobal` are re-derived
here and identified with the originals definitionally.
-/


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite


-- @@ L32-32 verbatim
universe u


-- @@ L34-34 verbatim
namespace SchemeProjectiveBundle

-- @@ L35-35 verbatim
namespace AffineFrameCover


-- @@ L37-37 verbatim
local notation "𝐑[" f "]" => Scheme.Modules.restrictFunctor f


-- @@ L39-39 verbatim
/-! ## Generic restriction plumbing -/


-- @@ L41-52 verbatim
/-- Copy of the private range-restriction transport of `ProjectiveBundleTwistTensorGlobal`. -/
private noncomputable def tensorOverlap_rangeRestrictIso
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules) :
    (Scheme.Modules.pullback f.isoOpensRange.inv).obj
        ((Scheme.Modules.restrictFunctor f).obj M) ≅
      (Scheme.Modules.restrictFunctor f.opensRange.ι).obj M :=
  (Scheme.Modules.pullback f.isoOpensRange.inv).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app M) ≪≫
    (Scheme.Modules.pullbackComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.pullbackCongr f.isoOpensRange_inv_comp).app M ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback f.opensRange.ι).app M).symm


-- @@ L54-72 verbatim
/-- Copy of the private over-iso constructor of `ProjectiveBundleTwistTensorGlobal`. -/
noncomputable def tensorOverlap_OI
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules}
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅
      (Scheme.Modules.restrictFunctor f).obj N) :
    M.over f.opensRange ≅ N.over f.opensRange := by
  let U := f.opensRange
  let F := Scheme.Modules.overEquiv U
  let eF : F.functor.obj (M.over U) ≅ F.functor.obj (N.over U) :=
    (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (tensorOverlap_rangeRestrictIso f M).symm ≪≫
      (Scheme.Modules.pullback f.isoOpensRange.inv).mapIso e ≪≫
      tensorOverlap_rangeRestrictIso f N ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app N).symm
  exact
    F.unitIso.app (M.over U) ≪≫
      F.inverse.mapIso eF ≪≫
      F.unitIso.symm.app (N.over U)


-- @@ L74-80 verbatim
/-- Transport of a restricted morphism along a factorization `r ≫ q = s`. -/
noncomputable def tensorOverlap_tr {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s)
    {M N : Y.Modules} (φ : 𝐑[q].obj M ⟶ 𝐑[q].obj N) :
    𝐑[s].obj M ⟶ 𝐑[s].obj N :=
  (restrictCompPrefixIso' s q r h M).hom ≫ 𝐑[r].map φ ≫
    (restrictCompPrefixIso' s q r h N).inv



-- @@ L83-87 verbatim
/-- Composition comparison with an explicit (non-`⋙`) type. -/
private noncomputable def tensorOverlap_cH {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    𝐑[f ≫ g].obj M ⟶ 𝐑[f].obj (𝐑[g].obj M) :=
  (Scheme.Modules.restrictFunctorComp f g).hom.app M


-- @@ L89-93 verbatim
/-- Composition comparison with an explicit (non-`⋙`) type. -/
private noncomputable def tensorOverlap_cI {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    𝐑[f].obj (𝐑[g].obj M) ⟶ 𝐑[f ≫ g].obj M :=
  (Scheme.Modules.restrictFunctorComp f g).inv.app M


-- @@ L95-99 verbatim
@[reassoc (attr := simp)]
private theorem tensorOverlap_cH_cI {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    tensorOverlap_cH f g M ≫ tensorOverlap_cI f g M = 𝟙 _ :=
  (Scheme.Modules.restrictFunctorComp f g).hom_inv_id_app M


-- @@ L101-105 verbatim
@[reassoc (attr := simp)]
private theorem tensorOverlap_cI_cH {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    tensorOverlap_cI f g M ≫ tensorOverlap_cH f g M = 𝟙 _ :=
  (Scheme.Modules.restrictFunctorComp f g).inv_hom_id_app M


-- @@ L107-111 verbatim
@[reassoc]
private theorem tensorOverlap_cH_nat {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules} (φ : M ⟶ N) :
    𝐑[f ≫ g].map φ ≫ tensorOverlap_cH f g N = tensorOverlap_cH f g M ≫ 𝐑[f].map (𝐑[g].map φ) :=
  (Scheme.Modules.restrictFunctorComp f g).hom.naturality φ


-- @@ L113-116 verbatim
private theorem tensorOverlap_comp_nat {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules} (φ : M ⟶ N) :
    𝐑[f ≫ g].map φ = tensorOverlap_cH f g M ≫ 𝐑[f].map (𝐑[g].map φ) ≫ tensorOverlap_cI f g N := by
  rw [← tensorOverlap_cH_nat_assoc, tensorOverlap_cH_cI, Category.comp_id]


-- @@ L118-121 verbatim
private theorem tensorOverlap_comp_nat' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules} (φ : M ⟶ N) :
    𝐑[f].map (𝐑[g].map φ) = tensorOverlap_cI f g M ≫ 𝐑[f ≫ g].map φ ≫ tensorOverlap_cH f g N := by
  rw [tensorOverlap_cH_nat, tensorOverlap_cI_cH_assoc]


-- @@ L123-131 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    ModulesHomAppHEqId ((Scheme.Modules.restrictFunctorComp f g).hom.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictFunctorComp f g).hom.app M).app U x) x
  rw [Scheme.Modules.restrictFunctorComp_hom_app_app]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L133-141 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    ModulesHomAppHEqId ((Scheme.Modules.restrictFunctorComp f g).inv.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictFunctorComp f g).inv.app M).app U x) x
  rw [Scheme.Modules.restrictFunctorComp_inv_app_app]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L143-145 verbatim
private theorem tensorOverlap_heq_cH {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    ModulesHomAppHEqId (tensorOverlap_cH f g M) := tensorOverlap_heq_comp_hom f g M


-- @@ L147-149 verbatim
private theorem tensorOverlap_heq_cI {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    ModulesHomAppHEqId (tensorOverlap_cI f g M) := tensorOverlap_heq_comp_inv f g M


-- @@ L151-159 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    ModulesHomAppHEqId ((Scheme.Modules.restrictFunctorCongr hfg).hom.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictFunctorCongr hfg).hom.app M).app U x) x
  rw [Scheme.Modules.restrictFunctorCongr_hom_app_app]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L161-169 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_congr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    ModulesHomAppHEqId ((Scheme.Modules.restrictFunctorCongr hfg).inv.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictFunctorCongr hfg).inv.app M).app U x) x
  rw [Scheme.Modules.restrictFunctorCongr_inv_app_app]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L171-175 verbatim
private theorem tensorOverlap_heq_pre_hom {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r]
    (h : r ≫ q = s) (M : Y.Modules) :
    ModulesHomAppHEqId (restrictCompPrefixIso' s q r h M).hom :=
  fun U x ↦ restrictCompPrefixIso'_hom_app_heq s q r h M U x


-- @@ L177-181 verbatim
private theorem tensorOverlap_heq_pre_inv {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r]
    (h : r ≫ q = s) (M : Y.Modules) :
    ModulesHomAppHEqId (restrictCompPrefixIso' s q r h M).inv :=
  fun U x ↦ restrictCompPrefixIso'_inv_app_heq s q r h M U x


-- @@ L183-185 verbatim
private theorem tensorOverlap_heq_openComp_hom {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (M : Y.Modules) :
    ModulesHomAppHEqId (restrictFunctorOpenCompIso' h M).hom :=
  fun W x ↦ restrictFunctorOpenCompIso'_hom_app_heq h M W x


-- @@ L187-189 verbatim
private theorem tensorOverlap_heq_openComp_inv {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) (M : Y.Modules) :
    ModulesHomAppHEqId (restrictFunctorOpenCompIso' h M).inv :=
  fun W x ↦ restrictFunctorOpenCompIso'_inv_app_heq h M W x



-- @@ L192-200 verbatim
private theorem tensorOverlap_rfIP_congr {X Y : Scheme.{u}} {s s' : X ⟶ Y} [IsOpenImmersion s]
    [IsOpenImmersion s'] (h : s = s') (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback s).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback s').inv.app M =
      (Scheme.Modules.restrictFunctorCongr h).hom.app M := by
  subst h
  rw [restrictFunctorCongr_refl_hom_app]
  simp [Scheme.Modules.pullbackCongr]


-- @@ L202-246 verbatim
private theorem tensorOverlap_rangeRestrictIso_eq
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (M : Z.Modules) :
    tensorOverlap_rangeRestrictIso f M =
      ((Scheme.Modules.restrictFunctorIsoPullback f.isoOpensRange.inv).app
          (𝐑[f].obj M)).symm ≪≫
        (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp M).symm := by
  apply Iso.ext
  let e := f.isoOpensRange.inv
  have L := CommonBasicOpen.twistPullHomAux_pullbackRestrictionCompFunctorIso_hom_eq f e
  have L2 : (CommonBasicOpen.twistPullHomAux_pullbackRestrictionCompFunctorIso f e).inv =
      (Scheme.Modules.pullbackComp e f).hom := by
    rw [← cancel_epi (CommonBasicOpen.twistPullHomAux_pullbackRestrictionCompFunctorIso f e).hom,
      Iso.hom_inv_id, L, Iso.inv_hom_id]
  have L3 : (Scheme.Modules.restrictFunctorIsoPullback e).inv.app
        ((Scheme.Modules.pullback f).obj M) ≫
      𝐑[e].map ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) ≫
      tensorOverlap_cI e f M ≫ (Scheme.Modules.restrictFunctorIsoPullback (e ≫ f)).hom.app M =
      (Scheme.Modules.pullbackComp e f).hom.app M := by
    rw [← L2]
    simp [CommonBasicOpen.twistPullHomAux_pullbackRestrictionCompFunctorIso, tensorOverlap_cI]
    try rfl
  have hC := tensorOverlap_rfIP_congr f.isoOpensRange_inv_comp M
  have hQ : tensorOverlap_cI e f M ≫
      (Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).hom.app M =
      (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp M).inv :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_cI _ _ _).comp (tensorOverlap_heq_congr_hom _ _)) (tensorOverlap_heq_pre_inv _ _ _ _ _)
  have hN : (Scheme.Modules.pullback e).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback e).inv.app
        ((Scheme.Modules.pullback f).obj M) =
      (Scheme.Modules.restrictFunctorIsoPullback e).inv.app (𝐑[f].obj M) ≫
        𝐑[e].map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) :=
    (Scheme.Modules.restrictFunctorIsoPullback e).inv.naturality _
  unfold tensorOverlap_rangeRestrictIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]
  rw [← L3]
  simp only [Category.assoc]
  have hcancel : 𝐑[e].map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) ≫
      𝐑[e].map ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact 𝐑[e].map_id _
  rw [reassoc_of% hN, reassoc_of% hcancel, ← hQ, ← hC]


-- @@ L248-273 verbatim
theorem tensorOverlap_OI_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] {M N : Z.Modules}
    (φ : 𝐑[f].obj M ≅ 𝐑[f].obj N) :
    tensorOverlap_OI f φ = overIsoOfRestrictIso f.opensRange
      (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp M ≪≫
        𝐑[f.isoOpensRange.inv].mapIso φ ≪≫
        (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp N).symm) := by
  have key : (tensorOverlap_rangeRestrictIso f M).symm ≪≫
      (Scheme.Modules.pullback f.isoOpensRange.inv).mapIso φ ≪≫ tensorOverlap_rangeRestrictIso f N =
      restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp M ≪≫
        𝐑[f.isoOpensRange.inv].mapIso φ ≪≫
        (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp N).symm := by
    rw [tensorOverlap_rangeRestrictIso_eq, tensorOverlap_rangeRestrictIso_eq]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc]
    rw [← (Scheme.Modules.restrictFunctorIsoPullback f.isoOpensRange.inv).hom.naturality_assoc]
    simp only [Iso.hom_inv_id_app_assoc]
  unfold tensorOverlap_OI overIsoOfRestrictIso
  dsimp only
  rw [← key]
  simp only [Iso.trans_assoc]
  rfl


-- @@ L275-281 verbatim
theorem tensorOverlap_restrict_overIso {Y : Scheme.{u}} {M N : Y.Modules} {U V : Y.Opens}
    (h : V ≤ U) (eU : 𝐑[U.ι].obj M ≅ 𝐑[U.ι].obj N) :
    Scheme.Modules.restrictHomOverLE Y h (overIsoOfRestrictIso U eU).hom =
      (overIsoOfRestrictIso V (restrictFunctorOpenCompIso' h M ≪≫
        𝐑[Y.homOfLE h].mapIso eU ≪≫ (restrictFunctorOpenCompIso' h N).symm)).hom := by
  apply restrict_overIsoOfRestrictIso_hom
  simp


-- @@ L283-324 verbatim
/-- The composite transport through the literal range equals direct transport. -/
theorem tensorOverlap_openRange_tr {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules} (φ : 𝐑[f].obj M ≅ 𝐑[f].obj N) {V : Z.Opens}
    (h : V ≤ f.opensRange) :
    (restrictFunctorOpenCompIso' h M ≪≫
        𝐑[Z.homOfLE h].mapIso
          (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
              f.isoOpensRange_inv_comp M ≪≫
            𝐑[f.isoOpensRange.inv].mapIso φ ≪≫
            (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
              f.isoOpensRange_inv_comp N).symm) ≪≫
        (restrictFunctorOpenCompIso' h N).symm).hom =
      tensorOverlap_tr V.ι f (Z.homOfLE h ≫ f.isoOpensRange.inv)
        (by rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι])
        φ.hom := by
  let e := f.isoOpensRange.inv
  have hφ := tensorOverlap_comp_nat' (Z.homOfLE h) e φ.hom
  have h1 : (restrictFunctorOpenCompIso' h M).hom ≫
      𝐑[Z.homOfLE h].map (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp M).hom ≫ tensorOverlap_cI (Z.homOfLE h) e _ =
      (restrictCompPrefixIso' V.ι f (Z.homOfLE h ≫ f.isoOpensRange.inv)
        (by rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι]) M).hom :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_openComp_hom _ _).comp (((tensorOverlap_heq_pre_hom _ _ _ _ _).restrict_map _).comp
        (tensorOverlap_heq_cI _ _ _)))
      (tensorOverlap_heq_pre_hom _ _ _ _ _)
  have h2 : tensorOverlap_cH (Z.homOfLE h) e _ ≫
      𝐑[Z.homOfLE h].map (restrictCompPrefixIso' f.opensRange.ι f f.isoOpensRange.inv
          f.isoOpensRange_inv_comp N).inv ≫
        (restrictFunctorOpenCompIso' h N).inv =
      (restrictCompPrefixIso' V.ι f (Z.homOfLE h ≫ f.isoOpensRange.inv)
        (by rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι]) N).inv :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_cH _ _ _).comp (((tensorOverlap_heq_pre_inv _ _ _ _ _).restrict_map _).comp
        (tensorOverlap_heq_openComp_inv _ _)))
      (tensorOverlap_heq_pre_inv _ _ _ _ _)
  unfold tensorOverlap_tr
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [hφ]
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2]


-- @@ L326-341 verbatim
/-- Transport along two equal factorizations. -/
theorem tensorOverlap_tr_congr {Y Z W : Scheme.{u}} {s s' : W ⟶ Y} (q : Z ⟶ Y) {r r' : W ⟶ Z}
    [IsOpenImmersion s] [IsOpenImmersion s'] [IsOpenImmersion q]
    [IsOpenImmersion r] [IsOpenImmersion r'] (hs : s = s') (hr : r = r')
    (h : r ≫ q = s) (h' : r' ≫ q = s')
    {M N : Y.Modules} (φ : 𝐑[q].obj M ⟶ 𝐑[q].obj N) :
    tensorOverlap_tr s' q r' h' φ =
      (Scheme.Modules.restrictFunctorCongr hs).inv.app M ≫ tensorOverlap_tr s q r h φ ≫
        (Scheme.Modules.restrictFunctorCongr hs).hom.app N := by
  subst hs hr
  have e1 : (Scheme.Modules.restrictFunctorCongr (rfl : s = s)).app M = Iso.refl _ :=
    Iso.ext (restrictFunctorCongr_refl_hom_app s M)
  have e2 : (Scheme.Modules.restrictFunctorCongr (rfl : s = s)).app N = Iso.refl _ :=
    Iso.ext (restrictFunctorCongr_refl_hom_app s N)
  rw [← Iso.app_inv, ← Iso.app_hom, e1, e2]
  simp


-- @@ L343-372 verbatim
/-- Restriction of a transport along a further open immersion. -/
theorem tensorOverlap_tr_restrict {Y Z W W' : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    (k : W' ⟶ W)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] [IsOpenImmersion k]
    (h : r ≫ q = s) {M N : Y.Modules} (φ : 𝐑[q].obj M ⟶ 𝐑[q].obj N) :
    𝐑[k].map (tensorOverlap_tr s q r h φ) =
      (restrictCompPrefixIso' (k ≫ s) s k rfl M).inv ≫
        tensorOverlap_tr (k ≫ s) q (k ≫ r) (by rw [Category.assoc, h]) φ ≫
        (restrictCompPrefixIso' (k ≫ s) s k rfl N).hom := by
  have hφ := tensorOverlap_comp_nat k r φ
  have h1 : (restrictCompPrefixIso' (k ≫ s) s k rfl M).inv ≫
      (restrictCompPrefixIso' (k ≫ s) q (k ≫ r) (by rw [Category.assoc, h]) M).hom ≫
        tensorOverlap_cH k r _ =
      𝐑[k].map (restrictCompPrefixIso' s q r h M).hom :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_pre_inv _ _ _ _ _).comp ((tensorOverlap_heq_pre_hom _ _ _ _ _).comp
        (tensorOverlap_heq_cH _ _ _)))
      ((tensorOverlap_heq_pre_hom _ _ _ _ _).restrict_map k)
  have h2 : tensorOverlap_cI k r _ ≫
      (restrictCompPrefixIso' (k ≫ s) q (k ≫ r) (by rw [Category.assoc, h]) N).inv ≫
        (restrictCompPrefixIso' (k ≫ s) s k rfl N).hom =
      𝐑[k].map (restrictCompPrefixIso' s q r h N).inv :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_cI _ _ _).comp ((tensorOverlap_heq_pre_inv _ _ _ _ _).comp
        (tensorOverlap_heq_pre_hom _ _ _ _ _)))
      ((tensorOverlap_heq_pre_inv _ _ _ _ _).restrict_map k)
  unfold tensorOverlap_tr
  rw [hφ, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2]



-- @@ L375-382 verbatim
private theorem tensorOverlap_heq_inv {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (h : ModulesHomAppHEqId e.hom) : ModulesHomAppHEqId e.inv := by
  intro W x
  have hx := h W (e.inv.val.app (op W) x)
  have hc : e.hom.val.app (op W) (e.inv.val.app (op W) x) = x :=
    congrArg (fun φ : B ⟶ B ↦ φ.val.app (op W) x) e.inv_hom_id
  rw [hc] at hx
  exact hx.symm


-- @@ L384-391 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_counit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules) :
    ModulesHomAppHEqId ((Scheme.Modules.restrictAdjunction f).counit.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictAdjunction f).counit.app M).app U x) x
  rw [Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L393-403 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_heq_bc_hom {W X Y Z : Scheme.{u}}
    (i : X ⟶ Z) (j : Y ⟶ Z) (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion g] (hp : IsPullback f g i j) (M : Y.Modules) :
    ModulesHomAppHEqId
      ((Scheme.Modules.restrictPushforwardBaseChangeIso i j f g hp).hom.app M) := by
  intro U x
  change HEq (((Scheme.Modules.restrictPushforwardBaseChangeIso i j f g hp).hom.app M).app U x) x
  rw [Scheme.Modules.restrictPushforwardBaseChangeIso_hom_app_apply]
  simp only [eqToHom_op]
  exact functor_map_eqToHom_heq (M.presheaf ⋙ forget Ab) _ x


-- @@ L405-420 verbatim
/-- Base change identity for the restricted pushforward/restriction square. -/
private theorem tensorOverlap_bc_counit {W X Y Z : Scheme.{u}}
    (i : X ⟶ Z) (j : Y ⟶ Z) (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion f] [IsOpenImmersion g]
    (hp : IsPullback f g i j) (M : Y.Modules) :
    𝐑[f].map ((Scheme.Modules.restrictPushforwardBaseChangeIso i j f g hp).inv.app M) ≫
        (restrictRestrictionSquareIso f i g j hp.w
          ((Scheme.Modules.pushforward j).obj M)).hom ≫
        𝐑[g].map ((Scheme.Modules.restrictAdjunction j).counit.app M) =
      (Scheme.Modules.restrictAdjunction f).counit.app (𝐑[g].obj M) :=
  modulesHom_ext_of_app_heq_id
    (((tensorOverlap_heq_inv ((Scheme.Modules.restrictPushforwardBaseChangeIso i j f g hp).app M)
        (tensorOverlap_heq_bc_hom i j f g hp M)).restrict_map f).comp
      ((restrictRestrictionSquareIso_hom_app_heq _ _ _ _ _ _).comp
        ((tensorOverlap_heq_counit j M).restrict_map g)))
    (tensorOverlap_heq_counit f _)


-- @@ L422-422 verbatim
/-! ## Tensor comparisons along composite restrictions -/


-- @@ L424-441 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The composite-restriction prefix acts on sections by a restriction map. -/
theorem tensorOverlap_pre_app {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s)
    (F : Y.Modules) (V : W.Opensᵒᵖ) :
    ∃ f : s.opensFunctor.op.obj V ⟶ q.opensFunctor.op.obj (r.opensFunctor.op.obj V),
      ∀ x : F.val.obj (s.opensFunctor.op.obj V),
        ((restrictCompPrefixIso' s q r h F).hom.val.app V).hom x = (F.val.map f).hom x := by
  refine ⟨eqToHom (by subst h; simp), fun x ↦ ?_⟩
  unfold restrictCompPrefixIso'
  rw [Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app]
  change ((Scheme.Modules.restrictFunctorComp r q).hom.app F).app V.unop
      (((Scheme.Modules.restrictFunctorCongr h.symm).hom.app F).app V.unop x) = _
  rw [Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change (F.presheaf.map _ ≫ F.presheaf.map _) x = _
  rw [← Functor.map_comp]
  rfl


-- @@ L443-469 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise unit formula for the open-restriction tensor comparison. -/
private theorem tensorOverlap_unit_tmul {Z Y : Scheme.{u}} (q : Z ⟶ Y) [IsOpenImmersion q] (M N : Y.Modules)
    (V : Z.Opensᵒᵖ) (a : M.val.obj (q.opensFunctor.op.obj V))
    (b : N.val.obj (q.opensFunctor.op.obj V)) :
    (((SchemeKTheory.underlyingCommPresheafFunctor Z).map
        (SchemeKTheory.restrictFunctorObjTensorSheafIso q M N).hom).app V).hom
      ((((SchemeKTheory.moduleSheafificationAdjunction Y).unit.app (M.val ⊗ N.val)).app
        (q.opensFunctor.op.obj V)).hom (a ⊗ₜ b)) =
    (((SchemeKTheory.moduleSheafificationAdjunction Z).unit.app
        ((𝐑[q].obj M).val ⊗ (𝐑[q].obj N).val)).app V).hom
      ((show (𝐑[q].obj M).val.obj V from a) ⊗ₜ (show (𝐑[q].obj N).val.obj V from b)) := by
  have h := SchemeKTheory.openRestriction_tensorSheafification_unit_app_tmul q M.val N.val V
    (show ((SchemeKTheory.openRestrictionPresheaf q).obj M.val).obj V from a)
    (show ((SchemeKTheory.openRestrictionPresheaf q).obj N.val).obj V from b)
  dsimp only at h
  have heP : ((pushforwardTensorIso q.opensFunctor (SchemeKTheory.openRestrictionRingHom q)
      (fun V ↦ SchemeKTheory.openRestrictionRingHom_app_isIso q V) M.val N.val).inv.app V).hom
      ((show ((SchemeKTheory.openRestrictionPresheaf q).obj M.val).obj V from a) ⊗ₜ
        (show ((SchemeKTheory.openRestrictionPresheaf q).obj N.val).obj V from b)) =
      a ⊗ₜ b := by
    dsimp [pushforwardTensorIso, restrictScalarsTensorIso,
      restrictScalarsTensorIsoInv, restrictScalarsTensorSectionMu]
    erw [ModuleCat.restrictScalars_μ_tmul]
    rfl
  rw [heP] at h
  exact h.symm


-- @@ L471-485 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of a restricted sheaf tensor product are determined on presheaf tensors. -/
private theorem tensorOverlap_char {Y W : Scheme.{u}} (s : W ⟶ Y) [IsOpenImmersion s] (M N : Y.Modules)
    {F : W.Modules} (φ ψ : 𝐑[s].obj (SchemeKTheory.tensorSheaf Y M N) ⟶ F)
    (h : (SchemeKTheory.openRestrictionPresheaf s).map
          ((SchemeKTheory.moduleSheafificationAdjunction Y).unit.app (M.val ⊗ N.val)) ≫
        (SchemeKTheory.underlyingCommPresheafFunctor W).map φ =
      (SchemeKTheory.openRestrictionPresheaf s).map
          ((SchemeKTheory.moduleSheafificationAdjunction Y).unit.app (M.val ⊗ N.val)) ≫
        (SchemeKTheory.underlyingCommPresheafFunctor W).map ψ) : φ = ψ := by
  apply (cancel_epi (SchemeKTheory.openRestrictionSheafificationIso s (M.val ⊗ N.val)).hom).1
  apply ((SchemeKTheory.moduleSheafificationAdjunction W).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  erw [SchemeKTheory.openRestrictionSheafificationComparison_homEquiv]
  exact h


-- @@ L487-547 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_beta_comp {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s)
    (M N : Y.Modules) :
    (restrictCompPrefixIso' s q r h (SchemeKTheory.tensorSheaf Y M N)).hom ≫
        𝐑[r].map (SchemeKTheory.restrictFunctorObjTensorSheafIso q M N).hom ≫
        (SchemeKTheory.restrictFunctorObjTensorSheafIso r (𝐑[q].obj M) (𝐑[q].obj N)).hom =
      (SchemeKTheory.restrictFunctorObjTensorSheafIso s M N).hom ≫
        SchemeKTheory.tensorSheafMap W (restrictCompPrefixIso' s q r h M).hom
          (restrictCompPrefixIso' s q r h N).hom := by
  apply tensorOverlap_char
  let μs := pushforwardTensorIso s.opensFunctor (SchemeKTheory.openRestrictionRingHom s)
      (fun V ↦ SchemeKTheory.openRestrictionRingHom_app_isIso s V) M.val N.val
  rw [← cancel_epi μs.inv]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  have heP : (μs.inv.app V).hom (a ⊗ₜ b) =
      (show M.val.obj (s.opensFunctor.op.obj V) from a) ⊗ₜ
        (show N.val.obj (s.opensFunctor.op.obj V) from b) := by
    dsimp [μs, pushforwardTensorIso, restrictScalarsTensorIso,
      restrictScalarsTensorIsoInv, restrictScalarsTensorSectionMu]
    erw [ModuleCat.restrictScalars_μ_tmul]
    rfl
  simp only [Functor.map_comp, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [heP]
  obtain ⟨f, hf⟩ := tensorOverlap_pre_app s q r h (SchemeKTheory.tensorSheaf Y M N) V
  obtain ⟨fM, hfM⟩ := tensorOverlap_pre_app s q r h M V
  obtain ⟨fN, hfN⟩ := tensorOverlap_pre_app s q r h N V
  obtain rfl : fM = f := Subsingleton.elim _ _
  obtain rfl : fN = fM := Subsingleton.elim _ _
  let ηY := (SchemeKTheory.moduleSheafificationAdjunction Y).unit.app (M.val ⊗ N.val)
  have hnat := congrArg (fun φ ↦ φ.hom ((show M.val.obj (s.opensFunctor.op.obj V) from a) ⊗ₜ
    (show N.val.obj (s.opensFunctor.op.obj V) from b))) (ηY.naturality fN)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at hnat
  erw [hf]
  have hnat' : (ModuleCat.Hom.hom ((SchemeKTheory.tensorSheaf Y M N).val.map fN))
      ((ModuleCat.Hom.hom (((SchemeKTheory.openRestrictionPresheaf s).map
          ((SchemeKTheory.moduleSheafificationAdjunction Y).unit.app (M.val ⊗ N.val))).app V))
        ((show M.val.obj (s.opensFunctor.op.obj V) from a) ⊗ₜ
          (show N.val.obj (s.opensFunctor.op.obj V) from b))) =
      (ModuleCat.Hom.hom (((SchemeKTheory.moduleSheafificationAdjunction Y).unit.app
          (M.val ⊗ N.val)).app (q.opensFunctor.op.obj (r.opensFunctor.op.obj V))))
        ((M.val.map fN).hom a ⊗ₜ (N.val.map fN).hom b) := hnat.symm
  erw [hnat']
  erw [tensorOverlap_unit_tmul q M N (r.opensFunctor.op.obj V) ((M.val.map fN).hom a)
    ((N.val.map fN).hom b)]
  erw [tensorOverlap_unit_tmul r (𝐑[q].obj M) (𝐑[q].obj N) V ((M.val.map fN).hom a)
    ((N.val.map fN).hom b)]
  erw [tensorOverlap_unit_tmul s M N V a b]
  have hT := congrArg (fun φ ↦ (φ.app V).hom ((show (𝐑[s].obj M).val.obj V from a) ⊗ₜ
      (show (𝐑[s].obj N).val.obj V from b)))
    ((SchemeKTheory.moduleSheafificationAdjunction W).unit.naturality
      ((restrictCompPrefixIso' s q r h M).hom.val ⊗ₘ (restrictCompPrefixIso' s q r h N).hom.val))
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hT
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at hT
  erw [hfM a, hfN b] at hT
  exact hT


-- @@ L549-555 verbatim
@[reassoc]
theorem tensorOverlap_pre_nat {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s)
    {M N : Y.Modules} (x : M ⟶ N) :
    𝐑[s].map x ≫ (restrictCompPrefixIso' s q r h N).hom =
      (restrictCompPrefixIso' s q r h M).hom ≫ 𝐑[r].map (𝐑[q].map x) :=
  (restrictCompPrefixNatIso' s q r h).hom.naturality x


-- @@ L557-557 verbatim
section Leg


-- @@ L559-569 verbatim
variable {R S M N ι : Type u}
  [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N]
  [Finite ι]
  {b : Module.Basis ι R M} {c : Module.Basis ι S N}
  {q : space S N ⟶ space R M} [IsOpenImmersion q]
  {Xg Z : Scheme.{u}} (ιg : space R M ⟶ Xg) [IsOpenImmersion ιg]
  (p : Z ⟶ Xg) (g : Z ⟶ space R M) (κ : Z ⟶ space S N)
  [IsOpenImmersion p] [IsOpenImmersion g] [IsOpenImmersion κ]
  (hg : g ≫ ιg = p) (hκ : κ ≫ q = g)


-- @@ L571-578 verbatim
/-- One leg: from the restriction of a global module to the intrinsic twist on the common
chart, through the ambient chart. -/
noncomputable def tensorOverlap_leg {d : ℤ} {O : Xg.Modules}
    (ρ : 𝐑[ιg].obj O ≅ twistingSheafOfBasisIndex R M b d)
    (D : TwistingSheafRestrictionData b c d q) :
    𝐑[p].obj O ≅ 𝐑[κ].obj (twistingSheafOfBasisIndex S N c d) :=
  restrictCompPrefixIso' p ιg g hg O ≪≫ 𝐑[g].mapIso ρ ≪≫
    restrictCompPrefixIso' g q κ hκ _ ≪≫ 𝐑[κ].mapIso D.restrictIso


-- @@ L580-629 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem tensorOverlap_oneSide {d e : ℤ}
    (Dd : TwistingSheafRestrictionData b c d q)
    (De : TwistingSheafRestrictionData b c e q)
    (Ds : TwistingSheafRestrictionData b c (d + e) q)
    (hOpen : ∀ i, q ⁻¹ᵁ linearOpen R M (b i) = linearOpen S N (c i))
    (hDd : Dd.chartIso.hom = (linearChartCochainsRestrictIso b c q hOpen).hom)
    (hDe : De.chartIso.hom = (linearChartCochainsRestrictIso b c q hOpen).hom)
    (hDs : Ds.chartIso.hom = (linearChartCochainsRestrictIso b c q hOpen).hom)
    {Od Oe Os : Xg.Modules}
    (ρd : 𝐑[ιg].obj Od ≅ twistingSheafOfBasisIndex R M b d)
    (ρe : 𝐑[ιg].obj Oe ≅ twistingSheafOfBasisIndex R M b e)
    (ρs : 𝐑[ιg].obj Os ≅ twistingSheafOfBasisIndex R M b (d + e)) :
    tensorOverlap_tr p ιg g hg (SchemeKTheory.restrictFunctorObjTensorSheafIso ιg Od Oe ≪≫
        SchemeKTheory.tensorSheafMapIso (space R M) ρd ρe ≪≫
        intrinsicTwistingTensorIso b d e ≪≫ ρs.symm).hom ≫
        (tensorOverlap_leg ιg p g κ hg hκ ρs Ds).hom =
      (SchemeKTheory.restrictFunctorObjTensorSheafIso p Od Oe).hom ≫
        SchemeKTheory.tensorSheafMap Z (tensorOverlap_leg ιg p g κ hg hκ ρd Dd).hom
          (tensorOverlap_leg ιg p g κ hg hκ ρe De).hom ≫
        (SchemeKTheory.restrictFunctorObjTensorSheafIso κ
          (twistingSheafOfBasisIndex S N c d) (twistingSheafOfBasisIndex S N c e)).inv ≫
        𝐑[κ].map (intrinsicTwistingTensorHom c d e) := by
  have TN := twistingSheafRestrictionData_tensorNaturality Dd De Ds hOpen hDd hDe hDs
  have A1 := tensorOverlap_beta_comp p ιg g hg Od Oe
  have A2 := tensorOverlap_beta_comp g q κ hκ (twistingSheafOfBasisIndex R M b d)
    (twistingSheafOfBasisIndex R M b e)
  have N1 := SchemeKTheory.restrictFunctorObjTensorSheafIso_hom_naturality g ρd.hom ρe.hom
  have N2 := SchemeKTheory.restrictFunctorObjTensorSheafIso_hom_naturality κ
    Dd.restrictIso.hom De.restrictIso.hom
  have Pn := tensorOverlap_pre_nat g q κ hκ (intrinsicTwistingTensorHom b d e)
  have TNκ : 𝐑[κ].map (𝐑[q].map (intrinsicTwistingTensorHom b d e)) ≫
      𝐑[κ].map Ds.restrictIso.hom =
      𝐑[κ].map (SchemeKTheory.restrictFunctorObjTensorSheafIso q
          (twistingSheafOfBasisIndex R M b d) (twistingSheafOfBasisIndex R M b e)).hom ≫
        𝐑[κ].map (SchemeKTheory.tensorSheafMap (space S N) Dd.restrictIso.hom
          De.restrictIso.hom) ≫ 𝐑[κ].map (intrinsicTwistingTensorHom c d e) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, TN]
  have hρ : 𝐑[g].map ρs.inv ≫ (restrictCompPrefixIso' p ιg g hg Os).inv ≫
      (restrictCompPrefixIso' p ιg g hg Os).hom ≫ 𝐑[g].map ρs.hom = 𝟙 _ := by
    rw [Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
    exact 𝐑[g].map_id _
  unfold tensorOverlap_tr tensorOverlap_leg
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    SchemeKTheory.tensorSheafMapIso_hom, Functor.map_comp, Category.assoc]
  have hI : (intrinsicTwistingTensorIso b d e).hom = intrinsicTwistingTensorHom b d e := rfl
  rw [reassoc_of% hρ, hI, reassoc_of% Pn, TNκ]
  simp only [← SchemeKTheory.tensorSheafMap_comp, Category.assoc]
  rw [← reassoc_of% A1, ← reassoc_of% N1, ← reassoc_of% A2, ← reassoc_of% N2,
    Iso.hom_inv_id_assoc]


-- @@ L631-631 verbatim
end Leg


-- @@ L633-651 verbatim
private theorem tensorOverlap_basisChange_tensor {S N ι₁ ι₂ : Type u} [CommRing S]
    [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N]
    [Finite ι₁] [Finite ι₂]
    (c₁ : Module.Basis ι₁ S N) (c₂ : Module.Basis ι₂ S N) (d e : ℤ)
    {Z : Scheme.{u}} (κ : Z ⟶ space S N) [IsOpenImmersion κ] :
    SchemeKTheory.tensorSheafMap Z (𝐑[κ].map (twistingSheafBasisChangeIso S N c₁ c₂ d).hom)
        (𝐑[κ].map (twistingSheafBasisChangeIso S N c₁ c₂ e).hom) ≫
      (SchemeKTheory.restrictFunctorObjTensorSheafIso κ
          (twistingSheafOfBasisIndex S N c₂ d) (twistingSheafOfBasisIndex S N c₂ e)).inv ≫
      𝐑[κ].map (intrinsicTwistingTensorHom c₂ d e) =
    (SchemeKTheory.restrictFunctorObjTensorSheafIso κ
          (twistingSheafOfBasisIndex S N c₁ d) (twistingSheafOfBasisIndex S N c₁ e)).inv ≫
      𝐑[κ].map (intrinsicTwistingTensorHom c₁ d e) ≫
      𝐑[κ].map (twistingSheafBasisChangeIso S N c₁ c₂ (d + e)).hom := by
  have hN := SchemeKTheory.restrictFunctorObjTensorSheafIso_hom_naturality κ
    (twistingSheafBasisChangeIso S N c₁ c₂ d).hom (twistingSheafBasisChangeIso S N c₁ c₂ e).hom
  have hB := intrinsicTwistingTensorHom_basisChange_naturality c₁ c₂ d e
  rw [Iso.eq_inv_comp, ← reassoc_of% hN, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    ← Functor.map_comp, hB]


-- @@ L653-653 verbatim
end AffineFrameCover

-- @@ L654-654 verbatim
end SchemeProjectiveBundle


-- @@ L656-656 verbatim
namespace SchemeProjectiveBundle

-- @@ L657-657 verbatim
namespace AffineFrameCover


-- @@ L659-659 verbatim
local notation "𝐑[" f "]" => Scheme.Modules.restrictFunctor f


-- @@ L661-661 verbatim
variable {X : Scheme.{u}} {E : X.Modules} (C : AffineFrameCover X E)


-- @@ L663-663 verbatim
attribute [local instance] transition_isOpenImmersion'


-- @@ L665-667 verbatim
instance tensorOverlap_chartι_space (i : C.I) :
    @IsOpenImmersion (space Γ(X, C.U i) (E.val.obj (op (C.U i)))) C.scheme (C.chartι i) :=
  C.chartι_isOpenImmersion i


-- @@ L669-672 verbatim
instance tensorOverlap_overlapToChart_space (i j : C.I) :
    @IsOpenImmersion (C.overlap i j) (space Γ(X, C.U i) (E.val.obj (op (C.U i))))
      (C.overlapToChart i j) :=
  C.overlapToChart_isOpenImmersion i j


-- @@ L674-675 verbatim
/-- Chart inclusion typed on the literal intrinsic space. -/
abbrev tensorOverlap_ιs (i : C.I) : space Γ(X, C.U i) (E.val.obj (op (C.U i))) ⟶ C.scheme := C.chartι i


-- @@ L677-680 verbatim
/-- Left overlap leg on a common basic open, typed on the literal space. -/
abbrev tensorOverlap_gL (i j : C.I) (c : C.CommonBasicOpen i j) :
    (C.twistComparisonOpen i j c).toScheme ⟶ space Γ(X, C.U i) (E.val.obj (op (C.U i))) :=
  (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j


-- @@ L682-685 verbatim
/-- Right overlap leg on a common basic open, typed on the literal space. -/
abbrev tensorOverlap_gR (i j : C.I) (c : C.CommonBasicOpen i j) :
    (C.twistComparisonOpen i j c).toScheme ⟶ space Γ(X, C.U j) (E.val.obj (op (C.U j))) :=
  (C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i


-- @@ L687-690 verbatim
/-- The common open immersion of a common basic open into the glued bundle. -/
abbrev tensorOverlap_p (i j : C.I) (c : C.CommonBasicOpen i j) :
    (C.twistComparisonOpen i j c).toScheme ⟶ C.scheme :=
  (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i


-- @@ L692-693 verbatim
instance tensorOverlap_ιs_isOpenImmersion (i : C.I) : IsOpenImmersion (C.tensorOverlap_ιs i) :=
  C.chartι_isOpenImmersion i


-- @@ L695-697 verbatim
instance tensorOverlap_gL_isOpenImmersion (i j : C.I) (c : C.CommonBasicOpen i j) :
    IsOpenImmersion (C.tensorOverlap_gL i j c) :=
  IsOpenImmersion.comp _ _


-- @@ L699-703 verbatim
instance tensorOverlap_gR_isOpenImmersion (i j : C.I) (c : C.CommonBasicOpen i j) :
    IsOpenImmersion (C.tensorOverlap_gR i j c) := by
  change IsOpenImmersion ((C.twistComparisonOpen i j c).ι ≫
    (C.transition i j ≫ C.overlapToChart j i))
  infer_instance


-- @@ L705-709 verbatim
instance tensorOverlap_p_isOpenImmersion (i j : C.I) (c : C.CommonBasicOpen i j) :
    IsOpenImmersion (C.tensorOverlap_p i j c) := by
  change IsOpenImmersion ((C.twistComparisonOpen i j c).ι ≫
    (C.overlapToChart i j ≫ C.chartι i))
  infer_instance


-- @@ L711-713 verbatim
theorem tensorOverlap_hL (i j : C.I) (c : C.CommonBasicOpen i j) :
    C.tensorOverlap_gL i j c ≫ C.tensorOverlap_ιs i = C.tensorOverlap_p i j c := by
  simp only [Category.assoc]; rfl


-- @@ L715-719 verbatim
theorem tensorOverlap_hR (i j : C.I) (c : C.CommonBasicOpen i j) :
    C.tensorOverlap_gR i j c ≫ C.tensorOverlap_ιs j = C.tensorOverlap_p i j c := by
  show ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i) ≫
    C.chartι j = (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i
  simp only [Category.assoc]; rw [C.overlapToChart_chartι_eq i j]


-- @@ L721-723 verbatim
theorem tensorOverlap_hκL (i j : C.I) (c : C.CommonBasicOpen i j) :
    (C.commonBasicOpenChartIsoOver i j c).hom ≫ c.chartToLeft = C.tensorOverlap_gL i j c :=
  C.commonBasicOpenChartIsoOver_hom_chartToLeft i j c


-- @@ L725-727 verbatim
theorem tensorOverlap_hκR (i j : C.I) (c : C.CommonBasicOpen i j) :
    (C.commonBasicOpenChartIsoOver i j c).hom ≫ c.chartToRight = C.tensorOverlap_gR i j c :=
  C.commonBasicOpenChartIsoOver_hom_chartToRight i j c


-- @@ L729-731 verbatim
private theorem tensorOverlap_chartOverIso_eq (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) (i : C.I) :
    C.canonicalTwistingSheafTensorChartOverIso hpos d e i =
      tensorOverlap_OI (C.chartι i) (C.canonicalTwistingSheafTensorChartIso hpos d e i) := rfl



-- @@ L734-736 verbatim
/-- The overlap common-basic open as a scheme, and its maps. -/
private abbrev tensorOverlap_W (i j : C.I) (c : C.CommonBasicOpen i j) : Scheme.{u} :=
  (C.twistComparisonOpen i j c).toScheme



-- @@ L739-799 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The canonical transition of the global twist on an ordered overlap, in restriction form. -/
private theorem tensorOverlap_DIY (d : ℤ) (i j : C.I) :
    𝐑[C.overlapToChart i j].map (C.canonicalTwistingSheafRestrictionIso d i).hom ≫
        (C.twistRestrictTransitionIso (C.canonicalTwistTransitionSystem d) i j).hom =
      (restrictRestrictionSquareIso (C.overlapToChart i j) (C.chartι i)
          (C.transition i j ≫ C.overlapToChart j i) (C.chartι j)
          (by rw [Category.assoc]; exact C.overlapToChart_chartι_eq i j)
          (C.canonicalTwistingSheaf d)).hom ≫
        𝐑[C.transition i j ≫ C.overlapToChart j i].map
          (C.canonicalTwistingSheafRestrictionIso d j).hom := by
  let T := C.canonicalTwistTransitionSystem d
  let hT := C.canonicalTwistTransitionLaws d
  let D := C.twistingSheafDescentData d T
  let fL := C.overlapToChart i j
  let fR := C.transition i j ≫ C.overlapToChart j i
  let ρi := C.canonicalTwistingSheafRestrictionIso d i
  let ρj := C.canonicalTwistingSheafRestrictionIso d j
  let 𝒯 := C.twistRestrictTransitionIso T i j
  let comp : C.canonicalTwistingSheaf d ⟶ D.chartTerm j := D.component j
  have hcomp : ρi.inv ≫ 𝐑[C.chartι i].map comp =
      C.twistLocalChartComponent T i j := by
    change C.twistLocalChartKernelLift T hT i ≫ 𝐑[C.chartι i].map
      (kernel.ι (D.descentLeft - D.descentRight) ≫ Pi.π D.chartTerm j) = _
    rw [Functor.map_comp, ← Category.assoc, C.twistLocalChartKernelLift_ι T hT i,
      C.twistLocalChartCochain_π T i j]
  have hρj : ρj.hom = 𝐑[C.chartι j].map comp ≫
      (Scheme.Modules.restrictAdjunction (C.chartι j)).counit.app
        (C.chartTwistingSheaf d j) := rfl
  have hsq := restrictRestrictionSquareIso_naturality fL (C.chartι i) fR (C.chartι j)
    (by rw [Category.assoc]; exact C.overlapToChart_chartι_eq i j) comp
  have hbc := tensorOverlap_bc_counit (C.chartι i) (C.chartι j) fL fR
    (C.glueData.chosenPullback i j).isPullback (C.chartTwistingSheaf d j)
  have hnat := (Scheme.Modules.restrictAdjunction fL).counit.naturality 𝒯.hom
  have htri := (Scheme.Modules.restrictAdjunction fL).left_triangle_components
    (C.chartTwistingSheaf d i)
  have hH : 𝒯.hom = 𝐑[fL].map ρi.inv ≫
      (restrictRestrictionSquareIso (C.overlapToChart i j) (C.chartι i)
          (C.transition i j ≫ C.overlapToChart j i) (C.chartι j)
          (by rw [Category.assoc]; exact C.overlapToChart_chartι_eq i j)
          (C.canonicalTwistingSheaf d)).hom ≫ 𝐑[fR].map ρj.hom := by
    rw [hρj, Functor.map_comp, ← reassoc_of% hsq, ← Functor.map_comp_assoc, hcomp]
    unfold twistLocalChartComponent
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    have hbc' : 𝐑[fL].map ((Scheme.Modules.restrictPushforwardBaseChangeIso (C.chartι i)
          (C.chartι j) (C.overlapToChart i j) (C.transition i j ≫ C.overlapToChart j i)
          (C.glueData.chosenPullback i j).isPullback).inv.app (C.chartTwistingSheaf d j)) ≫
        (restrictRestrictionSquareIso fL (C.chartι i) fR (C.chartι j)
          (by rw [Category.assoc]; exact C.overlapToChart_chartι_eq i j) (D.chartTerm j)).hom ≫
        𝐑[fR].map ((Scheme.Modules.restrictAdjunction (C.chartι j)).counit.app
          (C.chartTwistingSheaf d j)) =
      (Scheme.Modules.restrictAdjunction fL).counit.app (𝐑[fR].obj (C.chartTwistingSheaf d j)) :=
      hbc
    rw [hbc']
    simp only [Functor.comp_map, Functor.id_map] at hnat
    rw [hnat, ← Category.assoc, htri, Category.id_comp]
  rw [hH]
  have hcancel : 𝐑[fL].map ρi.hom ≫ 𝐑[fL].map ρi.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id]
    exact 𝐑[fL].map_id _
  rw [reassoc_of% hcancel]


-- @@ L801-898 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Left/right legs of the descent comparison on a common basic open. -/
theorem tensorOverlap_descent (d : ℤ) (i j : C.I) (c : C.CommonBasicOpen i j) :
    letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
    letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
    letI : Finite (C.basisIndex i) := C.basisIndex_finite i
    letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
    letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
    letI : Finite (C.basisIndex j) := C.basisIndex_finite j
    (tensorOverlap_leg (C.tensorOverlap_ιs i) (C.tensorOverlap_p i j c) (C.tensorOverlap_gL i j c)
        (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hL i j c) (C.tensorOverlap_hκL i j c)
        (C.canonicalTwistingSheafRestrictionIso d i) (c.leftTwistRestrictionData d)).hom ≫
      𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map (c.twistingSheafBasisIso d).hom =
    (tensorOverlap_leg (C.tensorOverlap_ιs j) (C.tensorOverlap_p i j c) (C.tensorOverlap_gR i j c)
        (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hR i j c) (C.tensorOverlap_hκR i j c)
        (C.canonicalTwistingSheafRestrictionIso d j) (c.rightTwistRestrictionData d)).hom := by
  letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
  letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  let w := (C.twistComparisonOpen i j c).ι
  let hind := C.twistOverlapRestrictLocalRestrictionIndependence_of_mul d i j
    (C.canonicalTwistOverlapRestrictMulRestrictionCompatibility d i j)
  have hglue : (C.twistRestrictTransitionIso (C.canonicalTwistTransitionSystem d) i j).hom =
      C.twistOverlapRestrictHomOfLocalCompatibility d i j hind := by
    have h0 := C.twistPullHomAux_canonicalTwistTransitionSystem_iso_hom d i j
    simp only [twistRestrictTransitionIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, h0, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hloc : 𝐑[w].map (C.twistRestrictTransitionIso (C.canonicalTwistTransitionSystem d) i j).hom =
      (C.twistOverlapRestrictLocalSchemeIso d i j c).hom := by
    rw [hglue]
    exact C.twistOverlapRestrictHomOfLocalCompatibility_restrict d i j hind c
  have hDIY := congrArg (fun t ↦ 𝐑[w].map t) (C.tensorOverlap_DIY d i j)
  simp only [Functor.map_comp, hloc] at hDIY
  unfold twistOverlapRestrictLocalSchemeIso transitionCanonicalTwistComparisonRestrictIso at hDIY
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp] at hDIY
  have hcR : ∀ {Q : (C.twistComparisonOpen i j c).toScheme.Modules}
      (h : 𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].obj (twistingSheafOfBasisIndex Γ(X, c.affineOpen.1)
        (E.val.obj (op c.affineOpen.1)) c.rightSectionBasis d) ⟶ Q),
      𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map (c.rightTwistRestrictionData d).restrictIso.inv ≫
        𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map (c.rightTwistRestrictionData d).restrictIso.hom ≫ h = h := by
    intro Q h
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hD2 := congrArg (· ≫ (C.twistOverlapTargetRestrictLocalSchemeIso d i j c).hom ≫
    𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map (c.rightTwistRestrictionData d).restrictIso.hom) hDIY
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hD2
  have hcR0 : 𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
        (c.rightTwistRestrictionData d).restrictIso.inv ≫
      𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
        (c.rightTwistRestrictionData d).restrictIso.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [hcR0] at hD2
  erw [Category.comp_id] at hD2
  have h1 : tensorOverlap_cI w (C.overlapToChart i j) (C.chartTwistingSheaf d i) ≫
      (restrictCompPrefixIso' (C.tensorOverlap_gL i j c) c.chartToLeft (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hκL i j c)
        (C.chartTwistingSheaf d i)).hom =
      (C.twistOverlapSourceRestrictLocalSchemeIso d i j c).hom :=
    modulesHom_ext_of_app_heq_id ((tensorOverlap_heq_cI _ _ _).comp (tensorOverlap_heq_pre_hom _ _ _ _ _))
      (C.twistOverlapSourceRestrictLocalSchemeIso_hom_app_heq d i j c)
  have h2 : tensorOverlap_cI w (C.transition i j ≫ C.overlapToChart j i) (C.chartTwistingSheaf d j) ≫
      (restrictCompPrefixIso' (C.tensorOverlap_gR i j c) c.chartToRight (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hκR i j c)
        (C.chartTwistingSheaf d j)).hom =
      (C.twistOverlapTargetRestrictLocalSchemeIso d i j c).hom :=
    modulesHom_ext_of_app_heq_id ((tensorOverlap_heq_cI _ _ _).comp (tensorOverlap_heq_pre_hom _ _ _ _ _))
      (C.twistOverlapTargetRestrictLocalSchemeIso_hom_app_heq d i j c)
  have h3 : (restrictCompPrefixIso' (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs i) (C.tensorOverlap_gL i j c)
        (C.tensorOverlap_hL i j c) (C.canonicalTwistingSheaf d)).hom ≫
      tensorOverlap_cH w (C.overlapToChart i j) (𝐑[C.chartι i].obj (C.canonicalTwistingSheaf d)) ≫
      𝐑[w].map (restrictRestrictionSquareIso (C.overlapToChart i j) (C.chartι i)
          (C.transition i j ≫ C.overlapToChart j i) (C.chartι j)
          (by rw [Category.assoc]; exact C.overlapToChart_chartι_eq i j)
          (C.canonicalTwistingSheaf d)).hom =
      (restrictCompPrefixIso' (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs j) (C.tensorOverlap_gR i j c)
        (C.tensorOverlap_hR i j c) (C.canonicalTwistingSheaf d)).hom ≫
      tensorOverlap_cH w (C.transition i j ≫ C.overlapToChart j i)
        (𝐑[C.chartι j].obj (C.canonicalTwistingSheaf d)) :=
    modulesHom_ext_of_app_heq_id
      ((tensorOverlap_heq_pre_hom _ _ _ _ _).comp ((tensorOverlap_heq_cH _ _ _).comp
        ((restrictRestrictionSquareIso_hom_app_heq _ _ _ _ _ _).restrict_map _)))
      ((tensorOverlap_heq_pre_hom _ _ _ _ _).comp (tensorOverlap_heq_cH _ _ _))
  unfold tensorOverlap_leg
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [tensorOverlap_comp_nat w (C.overlapToChart i j) (C.canonicalTwistingSheafRestrictionIso d i).hom,
    tensorOverlap_comp_nat w (C.transition i j ≫ C.overlapToChart j i)
      (C.canonicalTwistingSheafRestrictionIso d j).hom]
  simp only [Category.assoc]
  erw [reassoc_of% h1]
  rw [hD2]
  rw [reassoc_of% h3]
  have h2' := congrArg (· ≫ 𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
    (c.rightTwistRestrictionData d).restrictIso.hom) h2
  simp only [Category.assoc] at h2'
  rw [← h2']
  rfl


-- @@ L900-947 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The local comparison on one common basic open of the overlap. -/
private theorem tensorOverlap_localS (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) (i j : C.I)
    (c : C.CommonBasicOpen i j) :
    tensorOverlap_tr (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs i) (C.tensorOverlap_gL i j c) (C.tensorOverlap_hL i j c)
        (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom =
      tensorOverlap_tr (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs j) (C.tensorOverlap_gR i j c) (C.tensorOverlap_hR i j c)
        (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom := by
  letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
  letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  have OSi := tensorOverlap_oneSide (C.tensorOverlap_ιs i) (C.tensorOverlap_p i j c) (C.tensorOverlap_gL i j c)
    (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hL i j c) (C.tensorOverlap_hκL i j c)
    (c.leftTwistRestrictionData d) (c.leftTwistRestrictionData e)
    (c.leftTwistRestrictionData (d + e)) c.chartToLeft_preimage_linearOpen rfl rfl rfl
    (C.canonicalTwistingSheafRestrictionIso d i) (C.canonicalTwistingSheafRestrictionIso e i)
    (C.canonicalTwistingSheafRestrictionIso (d + e) i)
  have OSj := tensorOverlap_oneSide (C.tensorOverlap_ιs j) (C.tensorOverlap_p i j c) (C.tensorOverlap_gR i j c)
    (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hR i j c) (C.tensorOverlap_hκR i j c)
    (c.rightTwistRestrictionData d) (c.rightTwistRestrictionData e)
    (c.rightTwistRestrictionData (d + e)) c.chartToRight_preimage_linearOpen rfl rfl rfl
    (C.canonicalTwistingSheafRestrictionIso d j) (C.canonicalTwistingSheafRestrictionIso e j)
    (C.canonicalTwistingSheafRestrictionIso (d + e) j)
  have DId := C.tensorOverlap_descent d i j c
  have DIe := C.tensorOverlap_descent e i j c
  have DIs := C.tensorOverlap_descent (d + e) i j c
  have BC := tensorOverlap_basisChange_tensor c.leftSectionBasis c.rightSectionBasis d e
    (C.commonBasicOpenChartIsoOver i j c).hom
  have hB : ∀ n : ℤ, c.twistingSheafBasisIso n = twistingSheafBasisChangeIso
      Γ(X, c.affineOpen.1) (E.val.obj (op c.affineOpen.1)) c.leftSectionBasis
      c.rightSectionBasis n := fun n ↦ rfl
  simp only [← hB] at BC
  change tensorOverlap_tr _ (C.tensorOverlap_ιs i) _ _ (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom ≫ _
    = _ at OSi
  change tensorOverlap_tr _ (C.tensorOverlap_ιs j) _ _ (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom ≫ _
    = _ at OSj
  rw [← cancel_mono (tensorOverlap_leg (C.tensorOverlap_ιs j) (C.tensorOverlap_p i j c) (C.tensorOverlap_gR i j c)
    (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hR i j c) (C.tensorOverlap_hκR i j c)
    (C.canonicalTwistingSheafRestrictionIso (d + e) j) (c.rightTwistRestrictionData (d + e))).hom]
  rw [OSj, ← DIs]
  have OSi' := congrArg (· ≫ 𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
    (c.twistingSheafBasisIso (d + e)).hom) OSi
  simp only [Category.assoc] at OSi'
  refine OSi'.trans ?_
  rw [← DId, ← DIe, ← SchemeKTheory.tensorSheafMap_comp_assoc, BC]


-- @@ L949-961 verbatim
/-- The local comparison on one common basic open of the overlap. -/
private theorem tensorOverlap_local (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) (i j : C.I)
    (c : C.CommonBasicOpen i j) :
    tensorOverlap_tr ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i)
        (C.chartι i) ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j)
        (by simp only [Category.assoc])
        (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom =
      tensorOverlap_tr ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i)
        (C.chartι j) ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫
          C.overlapToChart j i)
        (by simp only [Category.assoc]; rw [C.overlapToChart_chartι_eq i j])
        (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom :=
  C.tensorOverlap_localS hpos d e i j c


-- @@ L963-1043 verbatim
/-- Independence of the transported chart tensor isomorphism for any open immersion factoring
through two charts. -/
private theorem tensorOverlap_indep (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) (i j : C.I)
    {W : Scheme.{u}} (s : W ⟶ C.scheme) [IsOpenImmersion s]
    (gi : W ⟶ C.chart i) (gj : W ⟶ C.chart j) [IsOpenImmersion gi] [IsOpenImmersion gj]
    (hi : gi ≫ C.chartι i = s) (hj : gj ≫ C.chartι j = s) :
    tensorOverlap_tr s (C.chartι i) gi hi (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom =
      tensorOverlap_tr s (C.chartι j) gj hj (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom := by
  let p : ∀ c : C.CommonBasicOpen i j, (C.twistComparisonOpen i j c).toScheme ⟶ C.scheme :=
    fun c ↦ (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i
  have hcov : (Opens.grothendieckTopology W).CoversTop
      (fun c : C.CommonBasicOpen i j ↦ s ⁻¹ᵁ (p c).opensRange) := by
    refine (Opens.coversTop_iff (T := W) _).2 ?_
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    have hij : C.glueData.ι i (gi x) = C.glueData.ι j (gj x) := by
      change (C.chartι i) (gi x) = (C.chartι j) (gj x)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hi, hj]
    obtain ⟨z, hz1, hz2⟩ := (C.glueData.ι_eq_iff i j (gi x) (gj x)).1 hij
    have hcovO := (C.basicOpenOverlapCover i j).isOpenCover_opensRange
    rw [TopologicalSpace.IsOpenCover, eq_top_iff] at hcovO
    have hz := hcovO (Set.mem_univ z)
    rw [TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨c, w, hw⟩ := hz
    refine ⟨c, ?_⟩
    change s x ∈ Set.range (p c)
    refine ⟨⟨z, ⟨w, hw⟩⟩, ?_⟩
    simp only [p, Scheme.Hom.comp_apply]
    change (C.chartι i) (C.glueData.f i j z) = s x
    rw [hz1, ← hi, Scheme.Hom.comp_apply]
  apply modulesHom_ext_of_restrict_coversTop _ hcov
  intro c
  let U := s ⁻¹ᵁ (p c).opensRange
  have hrange : Set.range (U.ι ≫ s).base ⊆ Set.range (p c).base := by
    rintro _ ⟨x, rfl⟩
    have hx := x.2
    rw [Scheme.Hom.comp_apply]
    exact hx
  let k := IsOpenImmersion.lift (p c) (U.ι ≫ s) hrange
  have hk : k ≫ p c = U.ι ≫ s := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion k := by
    have : IsOpenImmersion (k ≫ p c) := by rw [hk]; infer_instance
    exact IsOpenImmersion.of_comp k (p c)
  have hki : k ≫ ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j) = U.ι ≫ gi := by
    rw [← cancel_mono (C.chartι i)]
    simp only [Category.assoc, hi]
    exact hk
  have hkj : k ≫ ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫
      C.overlapToChart j i) = U.ι ≫ gj := by
    rw [← cancel_mono (C.chartι j)]
    simp only [Category.assoc, hj, ← C.overlapToChart_chartι_eq i j]
    exact hk
  have hL := C.tensorOverlap_local hpos d e i j c
  have hRi := tensorOverlap_tr_restrict (p c) (C.chartι i)
    ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j) k
    (by simp only [Category.assoc, p]) (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom
  have hRj := tensorOverlap_tr_restrict (p c) (C.chartι j)
    ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i) k
    (by simp only [Category.assoc, p]; rw [C.overlapToChart_chartι_eq i j])
    (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom
  have hCi := tensorOverlap_tr_congr (C.chartι i) hk hki
    (by simp only [Category.assoc]; rfl) (by rw [Category.assoc, hi])
    (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom
  have hCj := tensorOverlap_tr_congr (C.chartι j) hk hkj
    (by simp only [Category.assoc]; rw [← C.overlapToChart_chartι_eq i j])
    (by rw [Category.assoc, hj])
    (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom
  have hkey : tensorOverlap_tr (k ≫ p c) (C.chartι i)
      (k ≫ (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j)
      (by simp only [Category.assoc]; rfl)
      (C.canonicalTwistingSheafTensorChartIso hpos d e i).hom =
    tensorOverlap_tr (k ≫ p c) (C.chartι j)
      (k ≫ (C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i)
      (by simp only [Category.assoc]; rw [← C.overlapToChart_chartι_eq i j])
      (C.canonicalTwistingSheafTensorChartIso hpos d e j).hom := by
    have h1 := hRi
    rw [hL, hRj] at h1
    simp only [Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right] at h1
    exact h1.symm
  rw [tensorOverlap_tr_restrict, tensorOverlap_tr_restrict, hCi, hCj, hkey]


-- @@ L1045-1054 verbatim
theorem canonicalTwistingSheafTensorChartRestrictionIndependence
    (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) :
    C.CanonicalTwistingSheafTensorChartRestrictionIndependence hpos d e := by
  intro i j V hVi hVj
  rw [tensorOverlap_chartOverIso_eq, tensorOverlap_chartOverIso_eq, tensorOverlap_OI_eq, tensorOverlap_OI_eq,
    tensorOverlap_restrict_overIso, tensorOverlap_restrict_overIso]
  congr 2
  apply Iso.ext
  rw [tensorOverlap_openRange_tr, tensorOverlap_openRange_tr]
  exact C.tensorOverlap_indep hpos d e i j V.ι _ _ _ _


-- @@ L1056-1063 verbatim
/-- Unconditional multiplication law for the global intrinsic twist classes in `K₀`. -/
theorem canonicalTwistingSheafK0Class_mul
    (hpos : ∀ i, Nonempty (C.basisIndex i)) (d e : ℤ) :
    C.canonicalTwistingSheafK0Class d * C.canonicalTwistingSheafK0Class e =
      C.canonicalTwistingSheafK0Class (d + e) :=
  C.canonicalTwistingSheafK0Class_mul_of_compatibility hpos d e
    (C.canonicalTwistingSheafTensorChartCompatibility_of_restrictionIndependence hpos d e
      (C.canonicalTwistingSheafTensorChartRestrictionIndependence hpos d e))


-- @@ L1065-1065 verbatim
end AffineFrameCover

-- @@ L1066-1066 verbatim
end SchemeProjectiveBundle

