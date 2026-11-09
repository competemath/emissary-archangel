import ModularCurves.Picard.DualPullback.RestrictComp


-- @@ L3-7 verbatim
/-!
## Local pullback naturality: core stages

The first half of the option-free coherence proof for restricting local pullbacks.
-/


-- @@ L9-9 verbatim
open AlgebraicGeometry CategoryTheory Opposite


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L15-15 verbatim
variable {X Y : Scheme.{u}}


-- @@ L17-21 verbatim
noncomputable def restrictOpenCompIsoF {U V : X.Opens} (i : V ⟶ U) :
    restrictFunctor V.ι ≅
      restrictFunctor U.ι ⋙ restrictFunctor (X.homOfLE (leOfHom i)) :=
  restrictFunctorCongr (X.homOfLE_ι (leOfHom i)).symm ≪≫
    restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι


-- @@ L23-31 verbatim
noncomputable def localPullbackRestrictIsoF (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    (pullback (f ∣_ U)).obj ((restrictFunctor U.ι).obj M) ≅
      (restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M) :=
  (pullback (f ∣_ U)).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
    (pullbackSquareIso (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι f
      (morphismRestrict_ι f U)).app M ≪≫
    ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
      ((pullback f).obj M)).symm


-- @@ L33-47 verbatim
noncomputable def openPullbackRestrictIsoF (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    restrictFunctor (X.homOfLE (leOfHom i)) ⋙ pullback (f ∣_ V) ≅
      pullback (f ∣_ U) ⋙
        restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i))) :=
  Functor.isoWhiskerRight
      (restrictFunctorIsoPullback (X.homOfLE (leOfHom i)))
      (pullback (f ∣_ V)) ≪≫
    pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
      (morphismRestrict_homOfLE f V U (leOfHom i)) ≪≫
    Functor.isoWhiskerLeft (pullback (f ∣_ U))
      (restrictFunctorIsoPullback
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).symm


-- @@ L49-65 verbatim
noncomputable def localPullbackNaturalityMiddle1F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let fu := f ∣_ U
  let fv := f ∣_ V
  (pullback fv).map ((restrictFunctorCongr
      (X.homOfLE_ι (leOfHom i)).symm).hom.app M) ≫
    (pullback fv).map ((restrictFunctorComp x U.ι).hom.app M) ≫
    (pullback fv).map
      ((restrictFunctorIsoPullback x).hom.app ((restrictFunctor U.ι).obj M)) ≫
    (pullbackSquareIso fv x y fu
      (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app
        ((restrictFunctor U.ι).obj M) ≫
    (pullback y).map (localPullbackRestrictIsoF f M U).hom ≫
    (restrictFunctorIsoPullback y).inv.app
      ((restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M))


-- @@ L67-104 verbatim
theorem localPullbackNaturality_left_eq_middle1F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    (pullback (f ∣_ V)).map ((restrictOpenCompIsoF i).hom.app M) ≫
        (openPullbackRestrictIsoF f i).hom.app
          ((restrictFunctor U.ι).obj M) ≫
        (restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
            (localPullbackRestrictIsoF f M U).hom =
      localPullbackNaturalityMiddle1F f M i := by
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let fu := f ∣_ U
  let fv := f ∣_ V
  let a := (pullback fv).map
    ((restrictFunctorIsoPullback x).hom.app ((restrictFunctor U.ι).obj M))
  let s := (pullbackSquareIso fv x y fu
    (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app
      ((restrictFunctor U.ι).obj M)
  let ryi := (restrictFunctorIsoPullback y).inv.app
    ((pullback fu).obj ((restrictFunctor U.ι).obj M))
  let q := (localPullbackRestrictIsoF f M U).hom
  let ryi' := (restrictFunctorIsoPullback y).inv.app
    ((restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M))
  have hmove := (restrictFunctorIsoPullback y).inv.naturality q
  have htail : a ≫ s ≫ ryi ≫ (restrictFunctor y).map q =
      a ≫ s ≫ (pullback y).map q ≫ ryi' :=
    congrArg (fun k => a ≫ s ≫ k) hmove.symm
  simp only [restrictOpenCompIsoF, openPullbackRestrictIsoF,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc]
  let p₁ := (pullback fv).map
    ((restrictFunctorCongr (X.homOfLE_ι (leOfHom i)).symm).hom.app M)
  let p₂ := (pullback fv).map ((restrictFunctorComp x U.ι).hom.app M)
  dsimp only [localPullbackNaturalityMiddle1F]
  have hp := congrArg (fun k => p₁ ≫ p₂ ≫ k) htail
  exact hp


-- @@ L106-112 verbatim
noncomputable def localPullbackNaturalityPrefixF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let fv := f ∣_ V
  (pullback fv).map ((restrictFunctorCongr
      (X.homOfLE_ι (leOfHom i)).symm).hom.app M) ≫
    (pullback fv).map ((restrictFunctorComp x U.ι).hom.app M)


-- @@ L114-121 verbatim
noncomputable def localPullbackNaturalityTargetBeforeF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let fv := f ∣_ V
  let rU := (restrictFunctorIsoPullback U.ι).hom.app M
  (pullback fv).map
      ((restrictFunctorIsoPullback x).hom.app ((restrictFunctor U.ι).obj M)) ≫
    (pullback fv).map ((pullback x).map rU)


-- @@ L123-130 verbatim
noncomputable def localPullbackNaturalityTargetAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let fv := f ∣_ V
  let rU := (restrictFunctorIsoPullback U.ι).hom.app M
  (pullback fv).map ((restrictFunctor x).map rU) ≫
    (pullback fv).map
      ((restrictFunctorIsoPullback x).hom.app ((pullback U.ι).obj M))


-- @@ L132-148 verbatim
noncomputable def localPullbackNaturalityTail2F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  let fu := f ∣_ U
  let fv := f ∣_ V
  (pullbackSquareIso fv x y fu
      (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app
        ((pullback U.ι).obj M) ≫
    (pullback y).map
      ((pullbackSquareIso fu U.ι yu f
        (morphismRestrict_ι f U)).hom.app M) ≫
    (pullback y).map
      ((restrictFunctorIsoPullback yu).inv.app ((pullback f).obj M)) ≫
    (restrictFunctorIsoPullback y).inv.app
      ((restrictFunctor yu).obj ((pullback f).obj M))


-- @@ L150-154 verbatim
noncomputable def localPullbackNaturalityMiddle1aF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityPrefixF f M i ≫
    localPullbackNaturalityTargetBeforeF f M i ≫
    localPullbackNaturalityTail2F f M i


-- @@ L156-160 verbatim
noncomputable def localPullbackNaturalityMiddle2F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityPrefixF f M i ≫
    localPullbackNaturalityTargetAfterF f M i ≫
    localPullbackNaturalityTail2F f M i


-- @@ L162-202 verbatim
theorem localPullbackNaturality_middle1_eq_middle1aF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle1F f M i =
      localPullbackNaturalityMiddle1aF f M i := by
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  let fu := f ∣_ U
  let fv := f ∣_ V
  let hinner := morphismRestrict_homOfLE f V U (leOfHom i)
  let rU := (restrictFunctorIsoPullback U.ι).hom.app M
  let s₁ := (pullbackSquareIso fv x y fu hinner).hom.app
    ((restrictFunctor U.ι).obj M)
  let s₁' := (pullbackSquareIso fv x y fu hinner).hom.app
    ((pullback U.ι).obj M)
  let u₁ := (pullback fu).map rU
  let s₂ := (pullbackSquareIso fu U.ι yu f
    (morphismRestrict_ι f U)).hom.app M
  let rYUi := (restrictFunctorIsoPullback yu).inv.app ((pullback f).obj M)
  let ryi' := (restrictFunctorIsoPullback y).inv.app
    ((restrictFunctor yu).obj ((pullback f).obj M))
  let z₁ := (pullback y).map s₂ ≫ (pullback y).map rYUi ≫ ryi'
  have hinnerNat := (pullbackSquareIso fv x y fu hinner).hom.naturality rU
  have hinnerStep : s₁ ≫ (pullback y).map u₁ =
      (pullback fv).map ((pullback x).map rU) ≫ s₁' :=
    hinnerNat.symm
  have hinnerTail : s₁ ≫ (pullback y).map u₁ ≫ z₁ =
      (pullback fv).map ((pullback x).map rU) ≫ s₁' ≫ z₁ := by
    calc
      s₁ ≫ (pullback y).map u₁ ≫ z₁ =
          (s₁ ≫ (pullback y).map u₁) ≫ z₁ :=
        (Category.assoc _ _ _).symm
      _ = ((pullback fv).map ((pullback x).map rU) ≫ s₁') ≫ z₁ :=
        congrArg (fun k => k ≫ z₁) hinnerStep
      _ = (pullback fv).map ((pullback x).map rU) ≫ s₁' ≫ z₁ :=
        Category.assoc _ _ _
  simp only [localPullbackNaturalityMiddle1F,
    localPullbackNaturalityMiddle1aF, localPullbackRestrictIsoF,
    Iso.trans_hom, Functor.map_comp, Iso.symm_hom]
  erw [hinnerTail]
  rfl


-- @@ L204-229 verbatim
theorem localPullbackNaturality_middle1a_eq_middle2F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle1aF f M i =
      localPullbackNaturalityMiddle2F f M i := by
  let x := X.homOfLE (leOfHom i)
  let fv := f ∣_ V
  let rU := (restrictFunctorIsoPullback U.ι).hom.app M
  let rxU := (restrictFunctorIsoPullback x).hom.app
    ((restrictFunctor U.ι).obj M)
  let rxU' := (restrictFunctorIsoPullback x).hom.app
    ((pullback U.ι).obj M)
  have hrhoX := (restrictFunctorIsoPullback x).hom.naturality rU
  have htargetNat : (pullback fv).map rxU ≫
      (pullback fv).map ((pullback x).map rU) =
        (pullback fv).map ((restrictFunctor x).map rU) ≫
          (pullback fv).map rxU' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (pullback fv).map hrhoX.symm
  unfold localPullbackNaturalityMiddle1aF
    localPullbackNaturalityMiddle2F
    localPullbackNaturalityTargetBeforeF
    localPullbackNaturalityTargetAfterF
  exact congrArg
    (fun k => localPullbackNaturalityPrefixF f M i ≫ k ≫
      localPullbackNaturalityTail2F f M i)
    htargetNat


-- @@ L231-231 verbatim
end AlgebraicGeometry.Scheme.Modules
