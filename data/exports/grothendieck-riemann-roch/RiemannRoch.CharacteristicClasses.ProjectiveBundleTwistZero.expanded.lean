/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.CharacteristicClasses.ProjectiveBundleTwistTensorOverlap
import RiemannRoch.KTheory.GlobalPullbackTensorFree


-- @@ L10-26 verbatim
/-!
# The degree-zero twist of a projective bundle is trivial

For an affine frame cover `C` of a projective bundle `ℙ(E) → X`:

* `SchemeProjectiveBundle.twistZero_zetaIso b : O ≅ O(0)` on an intrinsic chart `Proj (Sym_R M)`
  with a finite basis `b` (the diagonal Čech cochain of the unit is a degree-zero cocycle, since the
  degree-zero transition units are `1`); it is compatible with basis changes and with restriction
  data (`twistZero_zeta_basisChange`, `twistZero_zeta_restrict`).
* `SchemeProjectiveBundle.AffineFrameCover.canonicalTwistingSheafZeroIso :
  C.canonicalTwistingSheaf 0 ≅ O`, glued from the chart isomorphisms along chart ranges, and
* `SchemeProjectiveBundle.AffineFrameCover.canonicalTwistingSheafK0Class_zero : [O(0)] = 1`
  in `K₀(ℙ(E))`.

No positivity hypothesis on the frames is needed. The overlap compatibility reuses the
chart-overlap plumbing of `ProjectiveBundleTwistTensorOverlap` (`tensorOverlap_*`).
-/


-- @@ L28-28 verbatim
set_option autoImplicit false


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory Opposite


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
namespace SchemeProjectiveBundle



-- @@ L39-39 verbatim
section Chart


-- @@ L41-42 verbatim
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]


-- @@ L44-47 verbatim
/-- The canonical map from the structure sheaf to a pushed unit. -/
abbrev twistZero_u {Y : Scheme.{u}} (U : Y.Opens) :
    SchemeKTheory.tensorUnitSheaf Y ⟶ SchemeProjectiveSpace.pushedUnit Y U :=
  SheafOfModules.unitToPushforwardObjUnit U.ι.toRingCatSheafHom


-- @@ L49-54 verbatim
theorem twistZero_unitMul_one {Y : Scheme.{u}} :
    (SchemeProjectiveSpace.unitMulSheafIso (1 : Γ(Y, ⊤)ˣ)).hom = 𝟙 _ := by
  have h := unitMulSheafIso_hom_comp (X := Y) (1 : Γ(Y, ⊤)ˣ) 1
  rw [mul_one] at h
  rw [← cancel_mono (SchemeProjectiveSpace.unitMulSheafIso (1 : Γ(Y, ⊤)ˣ)).hom, h,
    Category.id_comp]


-- @@ L56-64 verbatim
theorem twistZero_transition_zero (e : ℤ) (he : e = 0) (x y : M) :
    pushedLinearOverlapTransition R M e x y = 𝟙 _ := by
  subst he
  have h1 : linearTwistTransitionSectionUnit R M 0 x y = 1 := by
    simp [linearTwistTransitionSectionUnit]
    rfl
  unfold pushedLinearOverlapTransition linearOverlapTransitionIso
  rw [h1, map_one, twistZero_unitMul_one]
  exact (Scheme.Modules.pushforward _).map_id _


-- @@ L66-79 verbatim
theorem twistZero_u_restriction {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) :
    twistZero_u U ≫ SchemeProjectiveSpace.pushedUnitRestriction h = twistZero_u V := by
  ext W x
  have e1 : (Scheme.Modules.Hom.app (twistZero_u U) W) x = U.ι.app W x := rfl
  have e2 : (Scheme.Modules.Hom.app (twistZero_u V) W) x = V.ι.app W x := rfl
  have e3 : ∀ s : Γ(Y, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)),
      (Scheme.Modules.Hom.app (SchemeProjectiveSpace.pushedUnitRestriction h) W) s =
        Y.presheaf.map (homOfLE (SchemeProjectiveSpace.pushedUnitRestrictionOpen h W)).op s :=
    fun s => rfl
  change (Scheme.Modules.Hom.app (SchemeProjectiveSpace.pushedUnitRestriction h) W)
    ((Scheme.Modules.Hom.app (twistZero_u U) W) x) = _
  rw [e1, e2, e3]
  simp only [Scheme.Opens.ι_app]
  exact (Functor.map_comp_apply Y.presheaf _ _ x).symm


-- @@ L81-84 verbatim
theorem twistZero_u_cast {Y : Scheme.{u}} {A B : Y.Opens} (h : A = B) :
    twistZero_u A ≫ eqToHom (congrArg (SchemeProjectiveSpace.pushedUnit Y) h) = twistZero_u B := by
  subst h
  simp


-- @@ L86-86 verbatim
section Basis


-- @@ L88-88 verbatim
variable {ι : Type u} [Finite ι] (b : Module.Basis ι R M)


-- @@ L90-93 verbatim
/-- The diagonal Čech cochain of the structure sheaf. -/
noncomputable def twistZero_delta :
    SchemeKTheory.tensorUnitSheaf (space R M) ⟶ linearChartCochains R M b :=
  Pi.lift fun k : ι ↦ twistZero_u (linearOpen R M (b k))


-- @@ L95-100 verbatim
@[reassoc (attr := simp)]
theorem twistZero_delta_π (k : ι) :
    twistZero_delta b ≫ Pi.π (fun t : ι ↦
      SchemeProjectiveSpace.pushedUnit (space R M) (linearOpen R M (b t))) k =
      twistZero_u (linearOpen R M (b k)) :=
  Pi.lift_π (fun k : ι ↦ twistZero_u (linearOpen R M (b k))) k


-- @@ L102-108 verbatim
theorem twistZero_delta_compat :
    twistZero_delta b ≫ linearDescentLeft R M b = twistZero_delta b ≫ linearDescentRight R M b 0 := by
  apply Pi.hom_ext
  rintro ⟨i, j⟩
  simp only [Category.assoc, linearDescentLeft_π, linearDescentRight_π,
    twistZero_delta_π_assoc, twistZero_transition_zero (R := R) (M := M) 0 rfl, Category.comp_id,
    twistZero_u_restriction]


-- @@ L110-113 verbatim
/-- The degree-zero comparison `O ⟶ O(0)` on an intrinsic basis presentation. -/
noncomputable def twistZero_zeta :
    SchemeKTheory.tensorUnitSheaf (space R M) ⟶ twistingSheafOfBasisIndex R M b 0 :=
  twistingSheafOfBasisIndexLift R M b 0 (twistZero_delta b) (twistZero_delta_compat b)


-- @@ L115-119 verbatim
@[reassoc]
theorem twistZero_zeta_ι :
    twistZero_zeta b ≫ kernel.ι (linearDescentLeft R M b - linearDescentRight R M b 0) =
      twistZero_delta b :=
  twistingSheafOfBasisIndexLift_ι R M b 0 _ _


-- @@ L121-125 verbatim
@[reassoc]
theorem twistZero_zeta_component (i : ι) :
    twistZero_zeta b ≫ twistingSheafBasisComponent R M b 0 i = twistZero_u (linearOpen R M (b i)) := by
  unfold twistingSheafBasisComponent
  rw [twistZero_zeta_ι_assoc, twistZero_delta_π]


-- @@ L127-143 verbatim
theorem twistZero_zeta_isIso : IsIso (twistZero_zeta b) := by
  apply SchemeKTheory.moduleHom_isIso_of_over_cover (twistZero_zeta b)
    (fun i : ι ↦ linearOpen R M (b i)) (intrinsicLinearOpen_coversTop b)
  intro i
  letI : IsIso ((twistingSheafBasisComponent R M b 0 i).over (linearOpen R M (b i))) :=
    twistingSheafBasisComponent_over_isIso_of_le R M b 0 i le_rfl
  have hc : (twistZero_zeta b).over (linearOpen R M (b i)) ≫
      (twistingSheafBasisComponent R M b 0 i).over (linearOpen R M (b i)) =
      (pushedUnitOpenOverIso (space R M) (linearOpen R M (b i))).inv := by
    rw [AffineFrameCover.pushedUnitOpenOverIso_inv_eq_unitToPushforward]
    exact congrArg (fun f ↦ SheafOfModules.Hom.over f (linearOpen R M (b i)))
      (twistZero_zeta_component b i)
  letI : IsIso ((twistZero_zeta b).over (linearOpen R M (b i)) ≫
      (twistingSheafBasisComponent R M b 0 i).over (linearOpen R M (b i))) := by
    rw [hc]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((twistingSheafBasisComponent R M b 0 i).over (linearOpen R M (b i)))


-- @@ L145-145 verbatim
end Basis


-- @@ L147-168 verbatim
theorem twistZero_u_frameChange (e : ℤ) (he : e = 0) (x y : M) (V : (space R M).Opens)
    (hVx : V ≤ linearOpen R M x) (hVy : V ≤ linearOpen R M y) :
    (twistZero_u (linearOpen R M x)).over V ≫ (linearFrameChangeOverIso R M e x y V hVx hVy).hom =
      (twistZero_u (linearOpen R M y)).over V := by
  subst he
  have hOx : linearOverlapOpen R M x y ≤ linearOpen R M x :=
    (linearOverlapOpen_eq_inf R M x y).le.trans inf_le_left
  have hOy : linearOverlapOpen R M x y ≤ linearOpen R M y :=
    (linearOverlapOpen_eq_inf R M x y).le.trans inf_le_right
  have hx := twistZero_u_restriction hOx
  have hy := twistZero_u_restriction hOy
  simp only [linearFrameChangeOverIso, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
  rw [twistZero_transition_zero (R := R) (M := M) 0 rfl]
  have hcomp : (twistZero_u (linearOpen R M x)).over V ≫
      (SchemeProjectiveSpace.pushedUnitRestriction hOx).over V =
      (twistZero_u (linearOpen R M y)).over V ≫
        (SchemeProjectiveSpace.pushedUnitRestriction hOy).over V :=
    congrArg (fun f ↦ SheafOfModules.Hom.over f V) (hx.trans hy.symm)
  have hid : SheafOfModules.Hom.over
      (𝟙 (SchemeProjectiveSpace.pushedUnit (space R M) (linearOverlapOpen R M x y))) V =
      𝟙 _ := rfl
  rw [hid, Category.id_comp, reassoc_of% hcomp, IsIso.hom_inv_id, Category.comp_id]


-- @@ L170-202 verbatim
theorem twistZero_zeta_basisChange {ι κ : Type u} [Finite ι] [Finite κ]
    (b : Module.Basis ι R M) (c : Module.Basis κ R M) :
    twistZero_zeta b ≫ (twistingSheafBasisChangeIso R M b c 0).hom = twistZero_zeta c := by
  apply AffineFrameCover.modulesHom_ext_of_over_coversTop
    (fun ij : ι × κ ↦ basisChangeOpen R M b c ij.1 ij.2) (basisChangeOpen_coversTop R M b c)
  rintro ⟨i, j⟩
  dsimp only
  have hVbi : basisChangeOpen R M b c i j ≤ linearOpen R M (b i) :=
    (linearOverlapOpen_eq_inf R M (b i) (c j)).le.trans inf_le_left
  have hVcj : basisChangeOpen R M b c i j ≤ linearOpen R M (c j) :=
    (linearOverlapOpen_eq_inf R M (b i) (c j)).le.trans inf_le_right
  have hB : ((twistingSheafBasisChangeIso R M b c 0).hom).over (basisChangeOpen R M b c i j) =
      (twistingSheafBasisComponentOverIso R M b 0 i hVbi).hom ≫
        (linearFrameChangeOverIso R M (-0) (b i) (c j) _ hVbi hVcj).hom ≫
        (twistingSheafBasisComponentOverIso R M c 0 j hVcj).inv := by
    have h1 := twistingSheafBasisChangeHom_over R M b c 0 i j
    have h2 := twistingSheafBasisChangeLocalOverIso_restrict_hom R M b c 0 i j (le_refl _)
    rw [← h1] at h2
    exact h2
  have hzb : (twistZero_zeta b).over (basisChangeOpen R M b c i j) ≫
      (twistingSheafBasisComponentOverIso R M b 0 i hVbi).hom =
      (twistZero_u (linearOpen R M (b i))).over (basisChangeOpen R M b c i j) :=
    congrArg (fun f ↦ SheafOfModules.Hom.over f (basisChangeOpen R M b c i j))
      (twistZero_zeta_component b i)
  have hzc : (twistZero_zeta c).over (basisChangeOpen R M b c i j) ≫
      (twistingSheafBasisComponentOverIso R M c 0 j hVcj).hom =
      (twistZero_u (linearOpen R M (c j))).over (basisChangeOpen R M b c i j) :=
    congrArg (fun f ↦ SheafOfModules.Hom.over f (basisChangeOpen R M b c i j))
      (twistZero_zeta_component c j)
  change (twistZero_zeta b).over _ ≫ ((twistingSheafBasisChangeIso R M b c 0).hom).over _ =
    (twistZero_zeta c).over _
  rw [hB, reassoc_of% hzb, reassoc_of% (twistZero_u_frameChange (-0) neg_zero (b i) (c j) _ hVbi hVcj),
    ← hzc, Category.assoc, Iso.hom_inv_id, Category.comp_id]


-- @@ L204-238 verbatim
theorem twistZero_zeta_restrict {R S M N ι : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] [Finite ι]
    {b : Module.Basis ι R M} {c : Module.Basis ι S N}
    {q : space S N ⟶ space R M} [IsOpenImmersion q]
    (D : TwistingSheafRestrictionData b c 0 q)
    (hOpen : ∀ i, q ⁻¹ᵁ linearOpen R M (b i) = linearOpen S N (c i))
    (hD : D.chartIso.hom = (linearChartCochainsRestrictIso b c q hOpen).hom) :
    (Scheme.Modules.restrictFunctor q).map (twistZero_zeta b) ≫ D.restrictIso.hom =
      (Scheme.Modules.restrictUnitIso q).hom ≫ twistZero_zeta c := by
  apply (cancel_mono (kernel.ι (linearDescentLeft S N c - linearDescentRight S N c 0))).1
  have hK : D.restrictIso.hom ≫ kernel.ι (linearDescentLeft S N c - linearDescentRight S N c 0) =
      (Scheme.Modules.restrictFunctor q).map
        (kernel.ι (linearDescentLeft R M b - linearDescentRight R M b 0)) ≫ D.chartIso.hom :=
    AffineFrameCover.restrictKernelComparisonIso_hom_ι q _ _ D.chartIso D.overlapIso D.naturality
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine (congrArg (fun t ↦ (Scheme.Modules.restrictFunctor q).map (twistZero_zeta b) ≫ t) hK).trans ?_
  refine ((Scheme.Modules.restrictFunctor q).map_comp_assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_
    (congrArg (fun t ↦ (Scheme.Modules.restrictUnitIso q).hom ≫ t) (twistZero_zeta_ι c)).symm
  rw [twistZero_zeta_ι, hD]
  apply Pi.hom_ext
  intro k
  have e1 := pushedUnitPiRestrictOpenImmersionIso_hom_π q (fun i ↦ linearOpen R M (b i)) k
  have e2 := AffineFrameCover.restrictUnitToPushforwardOpenImmersion_naturality q
    (linearOpen R M (b k))
  simp only [linearChartCochainsRestrictIso, pushedUnitPiCastIso, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π]
  rw [reassoc_of% e1, ← Functor.map_comp_assoc, twistZero_delta_π]
  refine ((reassoc_of% e2) (eqToHom (congrArg (SchemeProjectiveSpace.pushedUnit (space S N))
    (hOpen k)))).trans ?_
  refine (congrArg (fun t ↦ (Scheme.Modules.restrictUnitIso q).hom ≫ t)
    (twistZero_u_cast (hOpen k))).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg _ (twistZero_delta_π c k))).symm


-- @@ L240-243 verbatim
/-- The degree-zero comparison as an isomorphism. -/
noncomputable def twistZero_zetaIso {ι : Type u} [Finite ι] (b : Module.Basis ι R M) :
    SheafOfModules.unit (space R M).ringCatSheaf ≅ twistingSheafOfBasisIndex R M b 0 :=
  @asIso _ _ _ _ (twistZero_zeta b) (twistZero_zeta_isIso b)


-- @@ L245-245 verbatim
end Chart



-- @@ L248-248 verbatim
end SchemeProjectiveBundle


-- @@ L250-250 verbatim
open MonoidalCategory


-- @@ L252-252 verbatim
namespace SchemeProjectiveBundle

-- @@ L253-253 verbatim
namespace AffineFrameCover


-- @@ L255-255 verbatim
local notation "𝐑[" f "]" => Scheme.Modules.restrictFunctor f



-- @@ L258-258 verbatim
section Leg


-- @@ L260-270 verbatim
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


-- @@ L272-282 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem twistZero_unitPrefix {Y Z W : Scheme.{u}} (s : W ⟶ Y) (q : Z ⟶ Y) (r : W ⟶ Z)
    [IsOpenImmersion s] [IsOpenImmersion q] [IsOpenImmersion r] (h : r ≫ q = s) :
    (restrictCompPrefixIso' s q r h (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
        𝐑[r].map (Scheme.Modules.restrictUnitIso q).hom ≫
        (Scheme.Modules.restrictUnitIso r).hom =
      (Scheme.Modules.restrictUnitIso s).hom := by
  subst h
  unfold restrictCompPrefixIso'
  rw [Iso.trans_hom, Iso.app_hom, Iso.app_hom, restrictFunctorCongr_refl_hom_app, Category.id_comp]
  exact restrictUnitIso_comp_hom q r


-- @@ L284-316 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem twistZero_oneSideZero
    (D : TwistingSheafRestrictionData b c 0 q)
    (hOpen : ∀ i, q ⁻¹ᵁ linearOpen R M (b i) = linearOpen S N (c i))
    (hD : D.chartIso.hom = (linearChartCochainsRestrictIso b c q hOpen).hom)
    {O : Xg.Modules} (ρ : 𝐑[ιg].obj O ≅ twistingSheafOfBasisIndex R M b 0) :
    tensorOverlap_tr p ιg g hg (ρ ≪≫ (twistZero_zetaIso b).symm ≪≫
        (Scheme.Modules.restrictUnitIso ιg).symm).hom =
      (tensorOverlap_leg ιg p g κ hg hκ ρ D).hom ≫ 𝐑[κ].map (twistZero_zetaIso c).inv ≫
        (Scheme.Modules.restrictUnitIso κ).hom ≫ (Scheme.Modules.restrictUnitIso p).inv := by
  have hB : 𝐑[q].map (twistZero_zetaIso b).hom ≫ D.restrictIso.hom =
      (Scheme.Modules.restrictUnitIso q).hom ≫ (twistZero_zetaIso c).hom :=
    twistZero_zeta_restrict D hOpen hD
  have hB' : D.restrictIso.hom ≫ (twistZero_zetaIso c).inv =
      𝐑[q].map (twistZero_zetaIso b).inv ≫ (Scheme.Modules.restrictUnitIso q).hom := by
    rw [← cancel_epi (𝐑[q].map (twistZero_zetaIso b).hom), reassoc_of% hB]
    simp
  have U1 := twistZero_unitPrefix g q κ hκ
  have U2 := twistZero_unitPrefix p ιg g hg
  have Pn := tensorOverlap_pre_nat g q κ hκ (twistZero_zetaIso b).inv
  have U2' : 𝐑[g].map (Scheme.Modules.restrictUnitIso ιg).inv ≫
      (restrictCompPrefixIso' p ιg g hg (SheafOfModules.unit Xg.ringCatSheaf)).inv =
      (Scheme.Modules.restrictUnitIso g).hom ≫ (Scheme.Modules.restrictUnitIso p).inv := by
    rw [Iso.eq_comp_inv, ← U2]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hκB : 𝐑[κ].map D.restrictIso.hom ≫ 𝐑[κ].map (twistZero_zetaIso c).inv =
      𝐑[κ].map (𝐑[q].map (twistZero_zetaIso b).inv) ≫
        𝐑[κ].map (Scheme.Modules.restrictUnitIso q).hom := by
    rw [← Functor.map_comp, hB', Functor.map_comp]
  unfold tensorOverlap_tr tensorOverlap_leg
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [U2', reassoc_of% hκB, ← reassoc_of% Pn, reassoc_of% U1]


-- @@ L318-318 verbatim
end Leg


-- @@ L320-320 verbatim
end AffineFrameCover

-- @@ L321-321 verbatim
end SchemeProjectiveBundle


-- @@ L323-323 verbatim
namespace SchemeProjectiveBundle

-- @@ L324-324 verbatim
namespace AffineFrameCover


-- @@ L326-326 verbatim
local notation "𝐑[" f "]" => Scheme.Modules.restrictFunctor f


-- @@ L328-328 verbatim
variable {X : Scheme.{u}} {E : X.Modules} (C : AffineFrameCover X E)


-- @@ L330-330 verbatim
attribute [local instance] transition_isOpenImmersion'


-- @@ L332-341 verbatim
/-- The chart isomorphism `O(0)|_{chart i} ≅ O|_{chart i}`. -/
private noncomputable def twistZero_chartIso (i : C.I) :
    𝐑[C.chartι i].obj (C.canonicalTwistingSheaf 0) ≅
      𝐑[C.chartι i].obj (SheafOfModules.unit C.scheme.ringCatSheaf) := by
  letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
  letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  exact C.canonicalTwistingSheafRestrictionIso 0 i ≪≫
    (twistZero_zetaIso (C.sectionBasis i)).symm ≪≫
    (Scheme.Modules.restrictUnitIso (C.chartι i)).symm



-- @@ L344-380 verbatim
set_option backward.isDefEq.respectTransparency false in
private theorem twistZero_localS (i j : C.I) (c : C.CommonBasicOpen i j) :
    tensorOverlap_tr (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs i) (C.tensorOverlap_gL i j c)
        (C.tensorOverlap_hL i j c) (C.twistZero_chartIso i).hom =
      tensorOverlap_tr (C.tensorOverlap_p i j c) (C.tensorOverlap_ιs j) (C.tensorOverlap_gR i j c)
        (C.tensorOverlap_hR i j c) (C.twistZero_chartIso j).hom := by
  letI : Module.Free Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_free i
  letI : Module.Finite Γ(X, C.U i) (E.val.obj (op (C.U i))) := C.sectionModule_finite i
  letI : Finite (C.basisIndex i) := C.basisIndex_finite i
  letI : Module.Free Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_free j
  letI : Module.Finite Γ(X, C.U j) (E.val.obj (op (C.U j))) := C.sectionModule_finite j
  letI : Finite (C.basisIndex j) := C.basisIndex_finite j
  have OSi := twistZero_oneSideZero (C.tensorOverlap_ιs i) (C.tensorOverlap_p i j c)
    (C.tensorOverlap_gL i j c) (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hL i j c)
    (C.tensorOverlap_hκL i j c) (c.leftTwistRestrictionData 0) c.chartToLeft_preimage_linearOpen rfl
    (C.canonicalTwistingSheafRestrictionIso 0 i)
  have OSj := twistZero_oneSideZero (C.tensorOverlap_ιs j) (C.tensorOverlap_p i j c)
    (C.tensorOverlap_gR i j c) (C.commonBasicOpenChartIsoOver i j c).hom (C.tensorOverlap_hR i j c)
    (C.tensorOverlap_hκR i j c) (c.rightTwistRestrictionData 0) c.chartToRight_preimage_linearOpen
    rfl (C.canonicalTwistingSheafRestrictionIso 0 j)
  have DI := C.tensorOverlap_descent 0 i j c
  have BC : (twistZero_zetaIso c.leftSectionBasis).hom ≫ (c.twistingSheafBasisIso 0).hom =
      (twistZero_zetaIso c.rightSectionBasis).hom :=
    twistZero_zeta_basisChange c.leftSectionBasis c.rightSectionBasis
  have BC' : (c.twistingSheafBasisIso 0).hom ≫ (twistZero_zetaIso c.rightSectionBasis).inv =
      (twistZero_zetaIso c.leftSectionBasis).inv := by
    rw [← cancel_epi (twistZero_zetaIso c.leftSectionBasis).hom, Iso.hom_inv_id,
      reassoc_of% BC, Iso.hom_inv_id]
  have BCκ : 𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map (c.twistingSheafBasisIso 0).hom ≫
      𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
        (twistZero_zetaIso c.rightSectionBasis).inv =
      𝐑[(C.commonBasicOpenChartIsoOver i j c).hom].map
        (twistZero_zetaIso c.leftSectionBasis).inv := by
    rw [← Functor.map_comp, BC']
  refine OSi.trans ?_
  refine Eq.trans ?_ OSj.symm
  rw [← DI, Category.assoc, reassoc_of% BCκ]


-- @@ L382-394 verbatim
/-- The local comparison on one common basic open of the overlap. -/
private theorem twistZero_local (i j : C.I)
    (c : C.CommonBasicOpen i j) :
    tensorOverlap_tr ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i)
        (C.chartι i) ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j)
        (by simp only [Category.assoc])
        (C.twistZero_chartIso i).hom =
      tensorOverlap_tr ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j ≫ C.chartι i)
        (C.chartι j) ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫
          C.overlapToChart j i)
        (by simp only [Category.assoc]; rw [C.overlapToChart_chartι_eq i j])
        (C.twistZero_chartIso j).hom :=
  C.twistZero_localS i j c


-- @@ L396-476 verbatim
/-- Independence of the transported chart tensor isomorphism for any open immersion factoring
through two charts. -/
private theorem twistZero_indep (i j : C.I)
    {W : Scheme.{u}} (s : W ⟶ C.scheme) [IsOpenImmersion s]
    (gi : W ⟶ C.chart i) (gj : W ⟶ C.chart j) [IsOpenImmersion gi] [IsOpenImmersion gj]
    (hi : gi ≫ C.chartι i = s) (hj : gj ≫ C.chartι j = s) :
    tensorOverlap_tr s (C.chartι i) gi hi (C.twistZero_chartIso i).hom =
      tensorOverlap_tr s (C.chartι j) gj hj (C.twistZero_chartIso j).hom := by
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
  have hL := C.twistZero_local i j c
  have hRi := tensorOverlap_tr_restrict (p c) (C.chartι i)
    ((C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j) k
    (by simp only [Category.assoc, p]) (C.twistZero_chartIso i).hom
  have hRj := tensorOverlap_tr_restrict (p c) (C.chartι j)
    ((C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i) k
    (by simp only [Category.assoc, p]; rw [C.overlapToChart_chartι_eq i j])
    (C.twistZero_chartIso j).hom
  have hCi := tensorOverlap_tr_congr (C.chartι i) hk hki
    (by simp only [Category.assoc]; rfl) (by rw [Category.assoc, hi])
    (C.twistZero_chartIso i).hom
  have hCj := tensorOverlap_tr_congr (C.chartι j) hk hkj
    (by simp only [Category.assoc]; rw [← C.overlapToChart_chartι_eq i j])
    (by rw [Category.assoc, hj])
    (C.twistZero_chartIso j).hom
  have hkey : tensorOverlap_tr (k ≫ p c) (C.chartι i)
      (k ≫ (C.twistComparisonOpen i j c).ι ≫ C.overlapToChart i j)
      (by simp only [Category.assoc]; rfl)
      (C.twistZero_chartIso i).hom =
    tensorOverlap_tr (k ≫ p c) (C.chartι j)
      (k ≫ (C.twistComparisonOpen i j c).ι ≫ C.transition i j ≫ C.overlapToChart j i)
      (by simp only [Category.assoc]; rw [← C.overlapToChart_chartι_eq i j])
      (C.twistZero_chartIso j).hom := by
    have h1 := hRi
    rw [hL, hRj] at h1
    simp only [Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right] at h1
    exact h1.symm
  rw [tensorOverlap_tr_restrict, tensorOverlap_tr_restrict, hCi, hCj, hkey]



-- @@ L479-490 verbatim
private theorem twistZero_restrictionIndependence (i j : C.I) {V : C.scheme.Opens}
    (hVi : V ≤ (C.chartι i).opensRange) (hVj : V ≤ (C.chartι j).opensRange) :
    Scheme.Modules.restrictHomOverLE C.scheme hVi
        (tensorOverlap_OI (C.chartι i) (C.twistZero_chartIso i)).hom =
      Scheme.Modules.restrictHomOverLE C.scheme hVj
        (tensorOverlap_OI (C.chartι j) (C.twistZero_chartIso j)).hom := by
  rw [tensorOverlap_OI_eq, tensorOverlap_OI_eq,
    tensorOverlap_restrict_overIso, tensorOverlap_restrict_overIso]
  congr 2
  apply Iso.ext
  rw [tensorOverlap_openRange_tr, tensorOverlap_openRange_tr]
  exact C.twistZero_indep i j V.ι _ _ _ _


-- @@ L492-506 verbatim
private theorem twistZero_compatible :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (fun i : C.I ↦
        Scheme.Modules.localHomSection C.scheme (C.chartι i).opensRange
          (tensorOverlap_OI (C.chartι i) (C.twistZero_chartIso i)).hom) := by
  intro V i j f g
  have hVi : V ≤ (C.chartι i).opensRange := f.le
  have hVj : V ≤ (C.chartι j).opensRange := g.le
  rw [show f = homOfLE hVi from Subsingleton.elim _ _,
    show g = homOfLE hVj from Subsingleton.elim _ _,
    Scheme.Modules.sheafHom_map_localHomSection,
    Scheme.Modules.sheafHom_map_localHomSection]
  exact congrArg
    (SheafOfModules.toSheaf (C.scheme.ringCatSheaf.over V)).map
    (C.twistZero_restrictionIndependence i j hVi hVj)


-- @@ L508-515 verbatim
/-- The glued global comparison `O(0) ⟶ O`. -/
noncomputable def twistZero_glueHom :
    C.canonicalTwistingSheaf 0 ⟶ SheafOfModules.unit C.scheme.ringCatSheaf :=
  Scheme.Modules.glueHom C.scheme
    (fun i : C.I ↦ (C.chartι i).opensRange)
    C.chartOpens_coversTop
    (fun i : C.I ↦ (tensorOverlap_OI (C.chartι i) (C.twistZero_chartIso i)).hom)
    C.twistZero_compatible


-- @@ L517-522 verbatim
theorem twistZero_glueHom_isIso : IsIso C.twistZero_glueHom :=
  Scheme.Modules.glueHom_isIso C.scheme
    (fun i : C.I ↦ (C.chartι i).opensRange)
    C.chartOpens_coversTop
    (fun i : C.I ↦ (tensorOverlap_OI (C.chartι i) (C.twistZero_chartIso i)).hom)
    C.twistZero_compatible (fun _ ↦ inferInstance)


-- @@ L524-527 verbatim
/-- The degree-zero canonical twist is the structure sheaf: `O(0) ≅ O`. -/
noncomputable def canonicalTwistingSheafZeroIso :
    C.canonicalTwistingSheaf 0 ≅ SheafOfModules.unit C.scheme.ringCatSheaf :=
  @asIso _ _ _ _ C.twistZero_glueHom C.twistZero_glueHom_isIso


-- @@ L529-538 verbatim
/-- `[O(0)] = 1` in `K₀(ℙ(E))`. -/
theorem canonicalTwistingSheafK0Class_zero :
    C.canonicalTwistingSheafK0Class 0 = 1 := by
  change SchemeKTheory.k0ClassOf C.scheme (C.canonicalTwistingSheaf 0)
      (C.canonicalTwistingSheaf_isFiniteLocallyFree 0) = 1
  calc
    _ = SchemeKTheory.k0ClassOf C.scheme (SchemeKTheory.tensorUnitSheaf C.scheme)
          (SchemeKTheory.tensorUnitSheaf_isFiniteLocallyFree C.scheme) :=
      SchemeKTheory.k0ClassOf_iso C.scheme _ _ C.canonicalTwistingSheafZeroIso
    _ = 1 := rfl


-- @@ L540-540 verbatim
end AffineFrameCover

-- @@ L541-541 verbatim
end SchemeProjectiveBundle
