/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.CharacteristicClasses.PencilEGenericCIIL3B
import RiemannRoch.CharacteristicClasses.CartierGysinMonoHsARRHS
import RiemannRoch.CharacteristicClasses.CartierGysinUnitARRHU


-- @@ L11-27 verbatim
/-!
# HbcE for the pencil: explicit fibre datum (route CIIL3B)

Let `σ` be a regular section of a line bundle `L` (rank one) on `Y` (`= M`), `F : W ⟶ Y` finite
and `pr : W ⟶ Z` flat.  The zero scheme `V(σ)` meets `W` in `Wz = W ×_Y V(σ)`.

* `eta_app_pullbackSection_eq_zero`, `ap_pushforward_fst_eq_zero`, `pullback_fst_ap_eq_zero`,
  `isIso_pullback_fst_cokernel_π`: the Koszul map `σ_{W,-}` vanishes on pushforwards from `Wz`,
  so the pullback to `Wz` of the cokernel projection `V → V/σ_W V` is an isomorphism (frames of
  `F^*(L⁻¹)` from `ARRHS`);
* `hbcE_pencil_fibre_bundle` / `hbcE_pencil_fibre`: `ι^* y = s_* x` in `G₀(V(σ))` with
  `s = (pr ∘ η)⁻¹ ≫ snd` (the zero section), for `y ∈ K₀(Y)` with `k0ToG0 y = F_*(pr^* x)`, any
  `x ∈ K₀(Z)`.  The gates are: `hL`, `hreg` (the divisor), `hs : Mono (pullbackSection F (dualEval σ))`
  (discharged for integral `W` by `ARRHS.mono_pullbackSection_of_generic`, see
  `hbcE_pencil_fibre_integral`), `IsIso (η ≫ pr)` (`W ∩ E ≅ Z`) and `K₀(Y) = G₀(Y)`.
  The unit gate is `ARRHU.hunit_ARRHU`.
-/


-- @@ L29-29 verbatim
set_option autoImplicit false

-- @@ L30-30 verbatim
set_option linter.unusedSectionVars false


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-36 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory KSpecialization Opposite
  TopologicalSpace AlgebraicGeometry.Chow.M7.D23 AlgebraicGeometry.Chow.M7
  SchemeKTheory.LineBundleDual KSpecialization.AR7R ExactGrothendieck.CartierGysinAR1


-- @@ L38-38 verbatim
universe u


-- @@ L40-40 verbatim
namespace KSpecialization.CIIL3B



-- @@ L43-43 verbatim
section E1


-- @@ L45-46 verbatim
variable {Y : Scheme.{u}} {L : Y.Modules} [L.IsQuasicoherent] [L.IsFinitePresentation]
  (σ : tensorUnitSheaf Y ⟶ L) {W : Scheme.{u}} (F : W ⟶ Y)


-- @@ L48-52 verbatim
theorem ι_app_dualEval (U : Y.Opens) (g : Γ(lineBundleDual Y L, U)) :
    (sectionEvaluationIdealSheaf σ).subschemeι.app U ((dualEval σ).app U g) = 0 := by
  have h := dualEval_structureMap_zero σ
  have h2 := congrArg (fun φ : lineBundleDual Y L ⟶ _ => φ.app U g) h
  exact h2



-- @@ L55-76 verbatim
theorem eta_app_res_F_app (V : W.Opens) (dU : Y.Opens) (a : Γ(Y, dU))
    (ha : (sectionEvaluationIdealSheaf σ).subschemeι.app dU a = 0) (hV : V ≤ F ⁻¹ᵁ dU) :
    (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app V
      (W.presheaf.map (homOfLE hV).op (F.app dU a)) = 0 := by
  have h1 : (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app (F ⁻¹ᵁ dU)
      (F.app dU a) = 0 := by
    have h2 : ((pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ F).app dU) a = 0 := by
      rw [pullback.condition, Scheme.Hom.comp_app]
      erw [CommRingCat.comp_apply]
      rw [ha, map_zero]
    rw [Scheme.Hom.comp_app] at h2
    erw [CommRingCat.comp_apply] at h2
    exact h2
  have h3 := ConcreteCategory.congr_hom
    (Scheme.Hom.naturality (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)
      (homOfLE hV).op) (F.app dU a)
  erw [CommRingCat.comp_apply] at h3
  refine h3.trans ?_
  change ((pullback F (sectionEvaluationIdealSheaf σ).subschemeι).presheaf.map _).hom
    ((pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app (F ⁻¹ᵁ dU) (F.app dU a)) = 0
  rw [h1]
  exact map_zero _



-- @@ L79-115 verbatim
theorem eta_app_pullbackSection_eq_zero (hL : HasConstantRank Y L 1) (U : W.Opens)
    (l : Γ((Scheme.Modules.pullback F).obj (lineBundleDual Y L), U)) :
    (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app U
      ((pullbackSection F (dualEval σ)).app U l) = 0 := by
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  let d : ∀ w : W, WFrame (lineBundleDual Y L) (F w) := fun w => (exists_wFrame hΛ1 (F w)).some
  let V : U → W.Opens := fun w => (F ⁻¹ᵁ (d w.1).U) ⊓ U
  refine TopCat.Sheaf.eq_of_locally_eq' (pullback F (sectionEvaluationIdealSheaf σ).subschemeι).sheaf
    (fun w : U => (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ (V w))
    ((pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ U)
    (fun w => homOfLE (Scheme.Hom.preimage_mono _ inf_le_right)) ?_ _ _ ?_
  · intro z hz
    have hw : (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) z ∈ U := hz
    refine Opens.mem_iSup.mpr ⟨⟨(pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) z, hw⟩, ?_⟩
    exact ⟨(d _).mem, hw⟩
  · intro w
    have hVU : V w ≤ U := inf_le_right
    have hVe : V w ≤ (WFrame.ofData (pullbackWFrame F (d w.1) w.1 (d w.1).mem)).U := inf_le_left
    obtain ⟨c, hc⟩ := (WFrame.ofData (pullbackWFrame F (d w.1) w.1 (d w.1).mem)).exists_coord
      (V w) hVe (((Scheme.Modules.pullback F).obj (lineBundleDual Y L)).presheaf.map
        (homOfLE hVU).op l)
    have h1 : (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app (V w)
        (W.presheaf.map (homOfLE hVU).op ((pullbackSection F (dualEval σ)).app U l)) = 0 := by
      have h2 : W.presheaf.map (homOfLE hVU).op ((pullbackSection F (dualEval σ)).app U l) =
          (pullbackSection F (dualEval σ)).app (V w)
            (((Scheme.Modules.pullback F).obj (lineBundleDual Y L)).presheaf.map
              (homOfLE hVU).op l) :=
        (AlgebraicGeometry.Chow.C1Cap.app_presheaf_map (pullbackSection F (dualEval σ)) (homOfLE hVU) l).symm
      rw [h2, ← hc, KSpecialization.ARRHS.pullbackSection_wFrameSec σ F (d w.1) w.1 (d w.1).mem (V w) hVe c, map_mul]
      erw [eta_app_res_F_app σ F (V w) (d w.1).U _ (ι_app_dualEval σ _ _) hVe]
      exact mul_zero _
    have h3 := ConcreteCategory.congr_hom
      (Scheme.Hom.naturality (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)
        (homOfLE hVU).op) ((pullbackSection F (dualEval σ)).app U l)
    erw [CommRingCat.comp_apply] at h3
    refine Eq.trans ?_ (map_zero _).symm
    exact h3.symm.trans h1



-- @@ L118-140 verbatim
theorem ap_pushforward_fst_eq_zero (hL : HasConstantRank Y L 1)
    (N : (pullback F (sectionEvaluationIdealSheaf σ).subschemeι).Modules) :
    ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
      (sigmaT _ (pullbackSection F (dualEval σ)))
      ((Scheme.Modules.pushforward (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).obj
        N) = 0 := by
  refine (sigmaT_app_eq_zero_iff (pullbackSection F (dualEval σ)) _).2 ?_
  intro U l m
  have key : ∀ (r : Γ(W, U))
      (m : Γ((Scheme.Modules.pushforward
        (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).obj N, U)),
      r • m = ((pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app U r •
        (@id Γ(N, (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ U) m) :
          Γ(N, (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ U)) :=
    fun _ _ => rfl
  refine (key _ m).trans ?_
  have h0 := eta_app_pullbackSection_eq_zero σ F hL U l
  have h0' : (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι).app U
      ((pullbackSection F (dualEval σ)).val.app (op U) l) = 0 := h0
  erw [h0']
  exact zero_smul Γ(pullback F (sectionEvaluationIdealSheaf σ).subschemeι,
    (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ U)
    (@id Γ(N, (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) ⁻¹ᵁ U) m)



-- @@ L143-161 verbatim
theorem pullback_fst_ap_eq_zero (hL : HasConstantRank Y L 1) (V : W.Modules) :
    (Scheme.Modules.pullback (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).map
      (ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V) = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_zero]
  have hn := (sigmaT _ (pullbackSection F (dualEval σ))).naturality (adj.unit.app V)
  have h0 := ap_pushforward_fst_eq_zero σ F hL
    ((Scheme.Modules.pullback (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).obj V)
  have hu := Adjunction.unit_naturality adj
    (ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
      (sigmaT _ (pullbackSection F (dualEval σ))) V)
  refine hu.trans ?_
  refine Eq.trans ?_ comp_zero.symm
  refine hn.symm.trans ?_
  exact (congrArg (fun z => (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj
    (lineBundleDual Y L))).map (adj.unit.app V) ≫ z) h0).trans comp_zero



-- @@ L164-173 verbatim
theorem isIso_pullback_fst_cokernel_π (hL : HasConstantRank Y L 1) (V : W.Modules) :
    IsIso ((Scheme.Modules.pullback (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).map
      (cokernel.π (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V))) := by
  haveI : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.pullback (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).leftAdjoint_preservesColimits
  exact isIso_map_cokernel_π_of_map_eq_zero _ _ (pullback_fst_ap_eq_zero σ F hL V)



-- @@ L176-176 verbatim
end E1


-- @@ L178-178 verbatim
section E2


-- @@ L180-183 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)
  {W Z : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
  (F : W ⟶ Y) [IsFinite F] (pr : W ⟶ Z) [Flat pr]


-- @@ L185-186 verbatim
set_option quotPrecheck false in
local notation "ιΣ" => (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L187-188 verbatim
set_option quotPrecheck false in
local notation "ηΣ" => pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L189-190 verbatim
set_option quotPrecheck false in
local notation "FzΣ" => pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι


-- @@ L192-268 verbatim
/-- **HbcE for the pencil, one vector bundle, explicit fibre datum.**  The zero scheme of `σ`
meets `W` in `Wz = W ×_Y V(σ)`; if `pr` restricted to `Wz` is an isomorphism onto `Z`, then
`ι^* y = s_* x` with `s = (pr ∘ η)⁻¹ ≫ snd : Z ⟶ V(σ)` (the "zero section"). -/
theorem hbcE_pencil_fibre_bundle (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    (hs : Mono (pullbackSection F (dualEval σ)))
    [IsIso (ηΣ ≫ pr)]
    (E0 : Z.Modules) (hE0 : IsFiniteLocallyFree Z E0) (y : K0 Y)
    (hy : k0ToG0 Y y = finitePushforward F (flatPullbackG0 pr
      (g0ClassOf Z E0 hE0.isFinitePresentation))) :
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme (pullbackK0 ιΣ y) =
      finitePushforward (inv (ηΣ ≫ pr) ≫ FzΣ) (g0ClassOf Z E0 hE0.isFinitePresentation) := by
  have hEc : IsCoherentLike Z E0 := hE0.isFinitePresentation
  letI : E0.IsFinitePresentation := hEc
  have hV₀ : IsCoherentLike W ((Scheme.Modules.pullback pr).obj E0) :=
    pullback_isFinitePresentation_global pr E0
  letI : ((Scheme.Modules.pullback pr).obj E0).IsFinitePresentation := hV₀
  have hVfl : IsFiniteLocallyFree W ((Scheme.Modules.pullback pr).obj E0) :=
    pullback_isFiniteLocallyFree_global pr E0 hE0
  have hy' : k0ToG0 Y y = finitePushforward F
      (g0ClassOf W ((Scheme.Modules.pullback pr).obj E0) hV₀) := by
    rw [hy, flatPullbackG0_classOf]
  haveI : Mono (ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
      (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0)) :=
    hMono_of_mono_pullbackSection σ F pr E0 hE0
  haveI : IsLocallyNoetherian (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) :=
    LocallyOfFiniteType.isLocallyNoetherian ηΣ
  have hT := tensorSheaf_isCoherentLike W _ _
    (SchemeKTheory.hasConstantRank_pullback W F _ 1
      (lineBundleDual_hasConstantRank L hL)).isFiniteLocallyFree hV₀
  have hC : IsCoherentLike W (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0))) :=
    (kerCokerClosed_isCoherentLike (Y := W)).cokernel _ hT hV₀
  letI : (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0))).IsFinitePresentation := hC
  have hunit := KSpecialization.ARRHU.hunit_ARRHU σ hL F ((Scheme.Modules.pullback pr).obj E0) hV₀
  have hG0 : IsCoherentLike (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
      ((Scheme.Modules.pullback ηΣ).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0)))) :=
    pullback_isFinitePresentation_global ηΣ _
  have hG' := (finitePushObject FzΣ ⟨_, hG0⟩).2
  let e : (Scheme.Modules.pushforward ιΣ).obj ((Scheme.Modules.pushforward FzΣ).obj
      ((Scheme.Modules.pullback ηΣ).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0))))) ≅
      (Scheme.Modules.pushforward F).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) ((Scheme.Modules.pullback pr).obj E0))) :=
    (Scheme.Modules.pushforwardComp FzΣ ιΣ).app _ ≪≫
      (Scheme.Modules.pushforwardCongr pullback.condition.symm).app _ ≪≫
      ((Scheme.Modules.pushforwardComp ηΣ F).app _).symm ≪≫
      (Scheme.Modules.pushforward F).mapIso (asIso (SchemeKTheory.ProjectionFormula.adjUnit ηΣ _)).symm
  have h := hbc_cartier_closed σ hL hreg F _ hV₀ y hy' _ hG' e
  rw [h]
  haveI := isIso_pullback_fst_cokernel_π σ F hL ((Scheme.Modules.pullback pr).obj E0)
  have hV₂ : IsCoherentLike (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
      ((Scheme.Modules.pullback ηΣ).obj ((Scheme.Modules.pullback pr).obj E0)) :=
    pullback_isFinitePresentation_global ηΣ _
  have hcls : g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hG0 =
      finitePushforward (inv (ηΣ ≫ pr)) (g0ClassOf Z E0 hEc) := by
    have h1 : g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hG0 =
        g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hV₂ :=
      g0ClassOf_iso _ _ _ (asIso ((Scheme.Modules.pullback ηΣ).map (cokernel.π _))).symm
    have hflat : g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hV₂ =
        flatPullbackG0 (ηΣ ≫ pr) (g0ClassOf Z E0 hEc) := by
      rw [flatPullbackG0_classOf]
      exact g0ClassOf_iso _ _ _ ((Scheme.Modules.pullbackComp ηΣ pr).app E0)
    have hiso := flatPullbackG0_iso_eq_finitePushforward_inv (asIso (ηΣ ≫ pr))
    have h3 : flatPullbackG0 (ηΣ ≫ pr) = finitePushforward (inv (ηΣ ≫ pr)) := hiso
    rw [h1, hflat, h3]
  have hcls' := (finitePushforward_classOf FzΣ _ hG0).symm
  refine hcls'.trans ?_
  rw [hcls]
  exact (congrArg (fun f : _ →+ _ => f (g0ClassOf Z E0 hEc))
    (finitePushforward_comp (inv (ηΣ ≫ pr)) FzΣ)).symm


-- @@ L270-300 verbatim
/-- **HbcE for the pencil, any class `x ∈ K₀(Z)`**, assuming `K₀(Y) = G₀(Y)` (`Resolution`). -/
theorem hbcE_pencil_fibre (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    (hs : Mono (pullbackSection F (dualEval σ)))
    [IsIso (ηΣ ≫ pr)]
    (hres : Function.Bijective (k0ToG0 Y)) (x : K0 Z) (y : K0 Y)
    (hy : k0ToG0 Y y = finitePushforward F (flatPullbackG0 pr (k0ToG0 Z x))) :
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme (pullbackK0 ιΣ y) =
      finitePushforward (inv (ηΣ ≫ pr) ≫ FzΣ) (k0ToG0 Z x) := by
  let Ψ : G0 Y ≃+ K0 Y := (AddEquiv.ofBijective (k0ToG0 Y) hres).symm
  have hΨ : ∀ g, k0ToG0 Y (Ψ g) = g := fun g =>
    (AddEquiv.ofBijective (k0ToG0 Y) hres).apply_symm_apply g
  let L' : K0 Z →+ G0 (sectionEvaluationIdealSheaf σ).subscheme :=
    (k0ToG0 _).comp ((pullbackK0 ιΣ).comp (Ψ.toAddMonoidHom.comp ((finitePushforward F).comp
      ((flatPullbackG0 pr).comp (k0ToG0 Z)))))
  let R : K0 Z →+ G0 (sectionEvaluationIdealSheaf σ).subscheme :=
    (finitePushforward (inv (ηΣ ≫ pr) ≫ FzΣ)).comp (k0ToG0 Z)
  have hLR : L' = R := by
    apply ExactGrothendieck.hom_ext
    intro E
    change k0ToG0 _ (pullbackK0 ιΣ
        (Ψ (finitePushforward F (flatPullbackG0 pr (k0ToG0 Z (k0ClassOf Z E.1 E.2)))))) =
      finitePushforward (inv (ηΣ ≫ pr) ≫ FzΣ) (k0ToG0 Z (k0ClassOf Z E.1 E.2))
    rw [k0ToG0_classOf]
    exact hbcE_pencil_fibre_bundle σ F pr hL hreg hs E.1 E.2 _ (by rw [hΨ])
  have hyΨ : y = Ψ (finitePushforward F (flatPullbackG0 pr (k0ToG0 Z x))) := by
    rw [← hy]; exact ((AddEquiv.ofBijective (k0ToG0 Y) hres).symm_apply_apply y).symm
  have := DFunLike.congr_fun hLR x
  change k0ToG0 _ (pullbackK0 ιΣ
      (Ψ (finitePushforward F (flatPullbackG0 pr (k0ToG0 Z x))))) =
    finitePushforward (inv (ηΣ ≫ pr) ≫ FzΣ) (k0ToG0 Z x) at this
  rw [hyΨ]; exact this


-- @@ L302-302 verbatim
end E2



-- @@ L305-305 verbatim
section Integral


-- @@ L307-310 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)
  {W Z : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
  (F : W ⟶ Y) [IsFinite F] (pr : W ⟶ Z) [Flat pr]


-- @@ L312-324 verbatim
/-- **HbcE for the pencil with `W` integral**: `hs` follows from `F(η_W) ∉ V(σ)` (route ARRHS). -/
theorem hbcE_pencil_fibre_integral (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    [IsIntegral W]
    (hη : F (genericPoint W) ∉ Set.range (sectionEvaluationIdealSheaf σ).subschemeι)
    [IsIso (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr)]
    (hres : Function.Bijective (k0ToG0 Y)) (x : K0 Z) (y : K0 Y)
    (hy : k0ToG0 Y y = finitePushforward F (flatPullbackG0 pr (k0ToG0 Z x))) :
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme
        (pullbackK0 (sectionEvaluationIdealSheaf σ).subschemeι y) =
      finitePushforward (inv (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr) ≫
        pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι) (k0ToG0 Z x) :=
  hbcE_pencil_fibre σ F pr hL hreg
    (KSpecialization.ARRHS.mono_pullbackSection_of_generic σ hL hreg F hη) hres x y hy


-- @@ L326-326 verbatim
end Integral


-- @@ L328-328 verbatim
end KSpecialization.CIIL3B
