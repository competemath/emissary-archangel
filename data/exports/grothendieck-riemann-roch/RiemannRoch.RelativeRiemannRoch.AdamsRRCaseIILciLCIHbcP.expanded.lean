/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.RelativeRiemannRoch.AdamsRRCaseIILciLCI
import RiemannRoch.KTheory.AffineCartesianBaseChange


-- @@ L10-23 verbatim
/-!
# The `K⁰`-level gate `hbcP` of ARR(ii) for lci `Z` (brick E2, G2E2)

`HbcPGate` of `AdamsRRCaseIILciLCI` asks, for every vector bundle `V` on `W = Z × ℙ¹`, that the
Euler-class pushforward `F_![V] ∈ K₀(M)` restricts on the exceptional divisor `E ⊂ M_∞` to
`s_![s_∞^* V] ∈ K₀(E)`.  Both sides are Euler classes (`repK0`), so this is reduced to:

* **sheaf-level base change** for the Cartier divisor `D = V(σ) ⊂ M` and the finite `F : W ⟶ M`
  (`pullbackPushIso`): `ι^*(F_* V) ≅ Fz_*(η^* V)`, `W ×_M D` with projections `η`, `Fz`;
  built from `ι_* ι^* G ≅ G/σG` (killed sheaves), the projection formula and the ARRHU unit;
* the `PerfectRepRestrictBG2` Cartier restriction of Euler classes (B4(ii)), with the needed
  monomorphism `σ_{F_*V}` from `σ_{W,V}` (ARRHS) through the projection formula;
* the transport `D ≅ E` (`kappa`) and `W ×_M D ≅ Z` (`secInf`, zero section).
-/


-- @@ L25-25 verbatim
set_option autoImplicit false

-- @@ L26-26 verbatim
set_option linter.unusedSectionVars false


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory

-- @@ L31-33 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7 KSpecialization KSpecialization.AR7R
  KSpecialization.AR8 ExactGrothendieck.CartierGysinAR1 ExactGrothendieck.CartierGysinAR8
  KSpecialization.AR4 SchemeKTheory.ProjectionFormula


-- @@ L35-35 verbatim
universe u


-- @@ L37-37 verbatim
namespace AdamsRRCaseIILciLCI


-- @@ L39-39 verbatim
section Sheaf


-- @@ L41-43 verbatim
variable {M : Scheme.{u}} [IsLocallyNoetherian M] {L : M.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf M ⟶ L)
  {W : Scheme.{u}} [IsLocallyNoetherian W] (F : W ⟶ M) [IsFinite F]


-- @@ L45-46 verbatim
set_option quotPrecheck false in
local notation "ιΣ" => (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L47-48 verbatim
set_option quotPrecheck false in
local notation "ηΣ" => pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L49-50 verbatim
set_option quotPrecheck false in
local notation "FzΣ" => pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L51-52 verbatim
set_option quotPrecheck false in
local notation "TΣ" => tensorSheafLeftFunctor M (lineBundleDual M L)

-- @@ L53-54 verbatim
set_option quotPrecheck false in
local notation "sΣ" => sigmaT (lineBundleDual M L) (dualEval σ)

-- @@ L55-56 verbatim
set_option quotPrecheck false in
local notation "TW" => tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L))

-- @@ L57-58 verbatim
set_option quotPrecheck false in
local notation "sW" => sigmaT _ (pullbackSection F (dualEval σ))


-- @@ L60-69 verbatim
/-- `ι^* σ_G = 0` on the zero scheme `V(σ)`, for every sheaf `G` on `M`. -/
theorem pullback_ι_ap_eq_zero (hL : HasConstantRank M L 1) (G : M.Modules) :
    (Scheme.Modules.pullback ιΣ).map (ap TΣ sΣ G) = 0 := by
  have hline : IsLocalLineFrame L := isLocalLineFrame_of_hasConstantRank_one hL
  have hΛ1 : HasConstantRank M (lineBundleDual M L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree M (lineBundleDual M L) := hΛ1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ hΛ
  exact map_ap_eq_zero_of_adj (Scheme.Modules.pullbackPushforwardAdjunction ιΣ) G
    ((ar7Bridge σ hline).killed_of_idealKills _ (idealKills_pushforward _ _))


-- @@ L71-123 verbatim
/-- `ι_* ι^* (F_* V) ≅ ι_* Fz_* η^* V` (before descending along the fully faithful `ι_*`). -/
def pushPullPushIso (hL : HasConstantRank M L 1) (V : W.Modules) (hV : IsCoherentLike W V) :
    (Scheme.Modules.pushforward ιΣ).obj ((Scheme.Modules.pullback ιΣ).obj
      ((Scheme.Modules.pushforward F).obj V)) ≅
    (Scheme.Modules.pushforward ιΣ).obj ((Scheme.Modules.pushforward FzΣ).obj
      ((Scheme.Modules.pullback ηΣ).obj V)) := by
  have hline : IsLocalLineFrame L := isLocalLineFrame_of_hasConstantRank_one hL
  have hΛ1 : HasConstantRank M (lineBundleDual M L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree M (lineBundleDual M L) := hΛ1.isFiniteLocallyFree
  have hΛW1 := SchemeKTheory.hasConstantRank_pullback W F _ 1 hΛ1
  have hΛW : IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual M L)) :=
    hΛW1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _ hΛW
  have hT : ∀ E, IsCoherentLike M E → IsCoherentLike M ((TΣ).obj E) := fun E hE =>
    tensorSheaf_isCoherentLike M _ _ hΛ hE
  have hTW : ∀ E, IsCoherentLike W E → IsCoherentLike W ((TW).obj E) := fun E hE =>
    tensorSheaf_isCoherentLike W _ _ hΛW hE
  let G := (Scheme.Modules.pushforward F).obj V
  have hG : IsCoherentLike M G := (finitePushObject F ⟨V, hV⟩).2
  let Q := cokernel (ap TΣ sΣ G)
  have hQ : IsCoherentLike M Q := (kerCokerClosed_isCoherentLike (Y := M)).cokernel _ (hT G hG) hG
  letI : Q.IsFinitePresentation := hQ
  have hQk : IdealKills (sectionEvaluationIdealSheaf σ) Q :=
    (ar7Bridge σ hline).idealKills_of_killed Q hQ (app_cokernel_eq_zero (T := TΣ) (σ := sΣ) G)
  haveI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback ιΣ) :=
    (Scheme.Modules.pullbackPushforwardAdjunction ιΣ).leftAdjoint_preservesColimits
  haveI hπ : IsIso ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ G))) :=
    ExactGrothendieck.CartierGysinAR8.isIso_map_cokernel_π_of_map_eq_zero _ _ (pullback_ι_ap_eq_zero σ hL G)
  haveI hu : IsIso (adjUnit ιΣ Q) :=
    isIso_adjUnit_of_killed (locallyPrincipal_sectionEvaluationIdealSheaf σ hline) Q hQk
  -- the `W` side
  let c := pushCompat F (dualEval σ) hΛ
  let QW := cokernel (ap TW sW V)
  have hQW : IsCoherentLike W QW := (kerCokerClosed_isCoherentLike (Y := W)).cokernel _ (hTW V hV) hV
  haveI : IsIso (cokernelComparison (ap TW sW V) (Scheme.Modules.pushforward F)) :=
    isIso_cokernelComparison_pushforward F _ (hTW V hV) hV
  haveI huW := KSpecialization.ARRHU.hunit_ARRHU σ hL F V hV
  haveI hπW := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL V
  exact (Scheme.Modules.pushforward ιΣ).mapIso
      (asIso ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ G)))) ≪≫
    (asIso (adjUnit ιΣ Q)).symm ≪≫
    cokernelIsoOfEq (c.ap_eq V) ≪≫
    cokernelEpiComp (c.iso V).inv ((Scheme.Modules.pushforward F).map (ap TW sW V)) ≪≫
    asIso (cokernelComparison (ap TW sW V) (Scheme.Modules.pushforward F)) ≪≫
    (Scheme.Modules.pushforward F).mapIso (asIso (adjUnit ηΣ QW)) ≪≫
    (Scheme.Modules.pushforward F).mapIso ((Scheme.Modules.pushforward ηΣ).mapIso
      (asIso ((Scheme.Modules.pullback ηΣ).map (cokernel.π (ap TW sW V)))).symm) ≪≫
    (Scheme.Modules.pushforwardComp ηΣ F).app _ ≪≫
    (Scheme.Modules.pushforwardCongr pullback.condition).app _ ≪≫
    ((Scheme.Modules.pushforwardComp FzΣ ιΣ).app _).symm


-- @@ L125-130 verbatim
/-- **Sheaf-level base change for a Cartier divisor and a finite morphism**:
`ι^*(F_* V) ≅ Fz_*(η^* V)` for coherent `V` on `W` (`W ×_M V(σ)` with projections `η`, `Fz`). -/
def pullbackPushIso (hL : HasConstantRank M L 1) (V : W.Modules) (hV : IsCoherentLike W V) :
    (Scheme.Modules.pullback ιΣ).obj ((Scheme.Modules.pushforward F).obj V) ≅
    (Scheme.Modules.pushforward FzΣ).obj ((Scheme.Modules.pullback ηΣ).obj V) :=
  (pushforwardFullyFaithful ιΣ).preimageIso (pushPullPushIso σ F hL V hV)


-- @@ L132-132 verbatim
end Sheaf


-- @@ L134-134 verbatim
/-! ### `hbcP` on the deformation space -/


-- @@ L136-136 verbatim
section Deformation


-- @@ L138-145 verbatim
open SchemeProjectiveSpace SchemeProjectiveBundle AlgebraicGeometry.Chow.M7.CIICLASS ARRKG
  SchemeNormalCone.AlgebraicGeometry
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalCompletion
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityExceptionalGlobal
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal
  SchemeRelativeRiemannRoch SchemeProjectiveSpace.AdamsRRFinal ARRKG2A


-- @@ L147-150 verbatim
variable {k : Type u} [CommRing k] [IsNoetherianRing k] [M1.FiniteDimBase k]
  {A : Scheme.{u}} [A.Over (Spk k)] [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A]
  (J : A.IdealSheafData) (hA : ProjectiveIntegralK k A) {r : ℕ}
  (C : GRRBlueprintV4.G2C.RegularCover J r)


-- @@ L152-161 verbatim
theorem FpL_k0ClassOf (V : (Ws A J).Modules) (hV : IsFiniteLocallyFree (Ws A J) V) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
    FpL J hA C (k0ClassOf _ V hV) =
      PerfectRepG2.Sch.repK0 (BundleCoversProjBundleG2.hasBundleCovers_total J hA)
        ((Scheme.Modules.pushforward (subschemeTotalGlobalι A J)).obj V)
        (finitePushObject (subschemeTotalGlobalι A J) ⟨V, hV.isFinitePresentation⟩).2
        (DeformationRegularWSheafLCI.pdLE_pushforward_of_regularCover
          (BundleCoversProjBundleG2.hasBundleCovers_total J hA) C V hV) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  exact DeformationRegularWSheafLCI.regPushOfRegularCover_k0ClassOf _ C V hV


-- @@ L163-175 verbatim
theorem spL_k0ClassOf (CN : AffineFrameCover (Zs A J) (Nsh J)) (V : (Zs A J).Modules)
    (hV : IsFiniteLocallyFree (Zs A J) V) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_adaptedCover_Z J hA CN
      (G2C1.hErankC C.toQuasiregular)
    spL J hA C CN (k0ClassOf _ V hV) =
      PerfectRepG2.Sch.repK0 (BundleCoversProjBundleG2.hasBundleCovers_adaptedCover_Z J hA CN
          (G2C1.hErankC C.toQuasiregular))
        ((Scheme.Modules.pushforward (Cov CN).zeroSection).obj V)
        (finitePushObject (Cov CN).zeroSection ⟨V, hV.isFinitePresentation⟩).2
        (ZeroSectionPushK0LCI.pdLE_zeroSection CN _ (G2C1.hErankC C.toQuasiregular) V hV) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_adaptedCover_Z J hA CN
    (G2C1.hErankC C.toQuasiregular)
  exact ZeroSectionPushK0LCI.liftPush_k0ClassOf _ _ _ _ V hV


-- @@ L177-287 verbatim
/-- **`hbcP` discharged**: the `K⁰`-level base change of `F_!` to the exceptional divisor
`E ⊂ M_∞` holds on every bundle generator (no regularity of `Z`, `M`, `W` or `E`). -/
theorem hbcPGate_proved [IsIntegral A] [IsIntegral J.subscheme] (φ : k →+* Γ(A, ⊤))
    (CN : AffineFrameCover (Zs A J) (Nsh J)) : HbcPGate J hA C CN := by
  intro V hV
  haveI := KG2B.isNoetherian_total J hA
  haveI := KG2B.isNoetherian_W J hA
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_W J hA
  let Cq := C.toQuasiregular
  have hE := G2C1.hErankC Cq
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_adaptedCover_Z J hA CN hE
  have hM := BundleCoversProjBundleG2.hasBundleCovers_total J hA
  have hEc := BundleCoversProjBundleG2.hasBundleCovers_adaptedCover_Z J hA CN hE
  let F := subschemeTotalGlobalι A J
  let ε := εL J C CN
  haveI : IsClosedImmersion ε := by
    change IsClosedImmersion (G2C1.EιOfIsoC Cq CN)
    unfold G2C1.EιOfIsoC
    infer_instance
  let GP := oeGate A φ J
  haveI := GP.qc
  haveI := GP.fp
  let I := sectionEvaluationIdealSheaf GP.σ
  haveI : IsLocallyNoetherian I.subscheme := CIIL3B.isLocallyNoetherian_subscheme I
  have hker1 : I.subschemeι.ker = (componentToTotal A J).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]; exact GP.hid
  have hkerE : ε.ker = I.subschemeι.ker := by
    rw [hker1]
    exact Scheme.Hom.ker_comp_of_isIso _ _
  have hD : PerfectRepG2.Sch.HasBundleCovers I.subscheme := by
    obtain ⟨m, jM, hjM⟩ := KG2B.projEmb_total J hA
    haveI := hjM
    exact BundleCoversProjBundleG2.hasBundleCovers_of_projEmb (R := k)
      ⟨m, I.subschemeι ≫ jM, inferInstance⟩
  let κ := G2GC1.kappa GP.σ ε hkerE
  have hκ : κ ≫ I.subschemeι = ε := G2GC1.kappa_fac GP.σ ε hkerE
  haveI : IsIso κ := G2GC1.kappa_isIso GP.σ ε hkerE
  haveI := G2GC1.isIso_fst_pr_of_ker_inf A J GP.σ hker1.symm
  let ρ := asIso (pullback.fst F I.subschemeι ≫ totalToClosedBase A J)
  have hsec : ρ.inv ≫ pullback.fst F I.subschemeι = secInf A J :=
    KSpecialization.ARRHBCP.inv_comp_fst_eq_secInf A J I.subschemeι hker1
  have hzs : (Cov CN).zeroSection ≫ ε = secInf A J ≫ F := G2C1.hzsC Cq CN
  have hzsκ : (Cov CN).zeroSection ≫ κ = ρ.inv ≫ pullback.snd F I.subschemeι := by
    rw [← cancel_mono I.subschemeι, Category.assoc, hκ, hzs, Category.assoc, ← pullback.condition,
      ← Category.assoc, hsec]
  have hzs' : ρ.inv ≫ pullback.snd F I.subschemeι ≫ inv κ = (Cov CN).zeroSection := by
    rw [← Category.assoc, ← hzsκ]
    simp
  -- monomorphisms
  have hline : IsLocalLineFrame GP.L := isLocalLineFrame_of_hasConstantRank_one GP.hL
  have hΛ1 : HasConstantRank _ (lineBundleDual _ GP.L) 1 := lineBundleDual_hasConstantRank GP.L GP.hL
  have hΛ : IsFiniteLocallyFree _ (lineBundleDual _ GP.L) := hΛ1.isFiniteLocallyFree
  have hΛW : IsFiniteLocallyFree _ ((Scheme.Modules.pullback F).obj (lineBundleDual _ GP.L)) :=
    (SchemeKTheory.hasConstantRank_pullback _ F _ 1 hΛ1).isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits _ _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits _ _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits _ _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits _ _ hΛW
  haveI hs : Mono (pullbackSection F (dualEval GP.σ)) :=
    KSpecialization.ARRHS.mono_pullbackSection_exceptional A J GP.σ k φ GP.hL GP.hreg GP.hid
  haveI : Mono (ap (tensorSheafLeftFunctor _ ((Scheme.Modules.pullback F).obj (lineBundleDual _ GP.L)))
      (sigmaT _ (pullbackSection F (dualEval GP.σ))) V) :=
    CIIL3B.mono_sigmaT_app (pullbackSection F (dualEval GP.σ)) V hV
  have hm : Mono (ap (tensorSheafLeftFunctor _ (lineBundleDual _ GP.L))
      (sigmaT (lineBundleDual _ GP.L) (dualEval GP.σ)) ((Scheme.Modules.pushforward F).obj V)) := by
    rw [(pushCompat F (dualEval GP.σ) hΛ).ap_eq V]
    infer_instance
  have hbund : ∀ E, IsFiniteLocallyFree _ E → Mono (ap (tensorSheafLeftFunctor _ (lineBundleDual _ GP.L))
      (sigmaT (lineBundleDual _ GP.L) (dualEval GP.σ)) E) :=
    fun E hE => CIIL3B.hmono_of_sectionIsRegular GP.σ hline GP.hreg E hE
  -- the `K⁰` computation
  have hG : IsCoherentLike _ ((Scheme.Modules.pushforward F).obj V) :=
    (finitePushObject F ⟨V, hV.isFinitePresentation⟩).2
  have hdG := DeformationRegularWSheafLCI.pdLE_pushforward_of_regularCover hM C V hV
  have hdD := PerfectRepRestrictBG2.Sch.pdLE_pullback_cartier GP.σ hM hD GP.hL hbund hG hm hdG
  have hGD := PerfectRepRestrictBG2.Sch.isCoherentLike_pullback I.subschemeι hG
  have step1 := PerfectRepRestrictBG2.Sch.pullbackK0_repK0_cartier_of_regular GP.σ hM hD GP.hL
    GP.hreg _ hG hm hdG hGD hdD
  have hGE := PerfectRepRestrictBG2.Sch.isCoherentLike_pullback κ hGD
  have hdE := PerfectRepRestrictBG2.Sch.pdLE_pullback_of_flat hEc hD κ hGD hdD
  have step2 := PerfectRepRestrictBG2.Sch.pullbackK0_repK0_of_flat hEc hD κ _ hGD hdD hGE hdE
  have hV' : IsFiniteLocallyFree _ ((Scheme.Modules.pullback (secInf A J)).obj V) :=
    pullback_isFiniteLocallyFree_global _ V hV
  -- the sheaf isomorphism `κ^* ι^* F_* V ≅ s_* s_∞^* V`
  let η := pullback.fst F I.subschemeι
  let Fz := pullback.snd F I.subschemeι
  let N := (Scheme.Modules.pullback η).obj V
  have eR : (Scheme.Modules.pushforward ρ.inv).obj ((Scheme.Modules.pullback ρ.inv).obj N) ≅ N :=
    (pushforwardHomNatIsoPullbackInv ρ.symm).app _ ≪≫
      (Scheme.Modules.pullbackComp ρ.hom ρ.inv).app N ≪≫
      (Scheme.Modules.pullbackCongr ρ.hom_inv_id).app N ≪≫
      (Scheme.Modules.pullbackId _).app N
  have e : (Scheme.Modules.pullback κ).obj ((Scheme.Modules.pullback I.subschemeι).obj
      ((Scheme.Modules.pushforward F).obj V)) ≅
      (Scheme.Modules.pushforward (Cov CN).zeroSection).obj
        ((Scheme.Modules.pullback (secInf A J)).obj V) :=
    (Scheme.Modules.pullback κ).mapIso (pullbackPushIso GP.σ F GP.hL V hV.isFinitePresentation) ≪≫
      (pullbackInvNatIsoPushforwardHom (asIso κ).symm).app _ ≪≫
      (Scheme.Modules.pushforwardComp Fz (inv κ)).app N ≪≫
      (Scheme.Modules.pushforward (Fz ≫ inv κ)).mapIso eR.symm ≪≫
      (Scheme.Modules.pushforward (Fz ≫ inv κ)).mapIso ((Scheme.Modules.pushforward ρ.inv).mapIso
        ((Scheme.Modules.pullbackComp ρ.inv η).app V)) ≪≫
      (Scheme.Modules.pushforwardComp ρ.inv (Fz ≫ inv κ)).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hzs').app _ ≪≫
      (Scheme.Modules.pushforward (Cov CN).zeroSection).mapIso
        ((Scheme.Modules.pullbackCongr hsec).app V)
  have hε : ∀ y, pullbackK0 ε y = pullbackK0 κ (pullbackK0 I.subschemeι y) := fun y => by
    rw [pullbackK0_comp_apply, hκ]
  rw [pullbackK0_classOf, FpL_k0ClassOf, spL_k0ClassOf, hε, step1, step2]
  exact PerfectRepG2.Sch.repK0_iso hEc e _ _ _ _


-- @@ L289-289 verbatim
end Deformation


-- @@ L291-291 verbatim
/-! ### ARR(ii) for lci `Z`, modulo `htw` only -/


-- @@ L293-293 verbatim
section Final


-- @@ L295-298 verbatim
open SchemeProjectiveSpace SchemeProjectiveBundle AlgebraicGeometry.Chow.M7.CIICLASS ARRKG
  SchemeNormalCone.AlgebraicGeometry
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeRelativeRiemannRoch SchemeProjectiveSpace.AdamsRRFinal ARRKG2A


-- @@ L300-304 verbatim
variable {k : Type u} [CommRing k] [IsDomain k] [IsNoetherianRing k] [M1.FiniteDimBase k]
  {A : Scheme.{u}} [A.Over (Spk k)] [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A]
  [IsIntegral A] (J : A.IdealSheafData) [IsIntegral J.subscheme]
  (hA : ProjectiveIntegralK k A) (hAreg : BlowupRegularAR12.IsRegularScheme A) {r : ℕ}
  (C : GRRBlueprintV4.G2C.RegularCover J r)


-- @@ L306-320 verbatim
/-- **ARR(ii) for an lci (possibly singular) integral `Z = V(J) ⊂ A`**, `A` a regular
`ProjectiveIntegralK` scheme, `C` a length-`r` Koszul-regular cover of `J`, `0 < r`, `Z ≠ A`:
`ψʲ(i_* x) = i_*(θʲ(N^∨) · ψʲ x)` in `K₀(A)[1/j]`, modulo the single remainder `htw`
(the pulled-back dual lines of `𝒪(M₀)` and `𝒪(E)` agree in `K₀(Z × ℙ¹)`). -/
theorem arr_caseII_ambient_lci_of_htw (φ : k →+* Γ(A, ⊤)) (hd : 0 < r)
    (hne : ∃ y : A, y ∉ Set.range (iZ A J))
    (htw : ∃ G₀ : ZeroGate A J k φ, HtwOf J hA G₀ (oeGate A φ J))
    {j : ℕ} (hj : 1 ≤ j) (x : KLoc j (Zs A J)) :
    locMap (j := j) (adamsRingHom (rankA A) j)
        (pushLocF3 j (iZ A J) (KG2B.resolutionA hA hAreg).res x) =
      pushLocF3 j (iZ A J) (KG2B.resolutionA hA hAreg).res
        (thetaL J hA C j * locMap (j := j) (adamsRingHom (rankZ A J) j) x) := by
  obtain ⟨CN, hCN⟩ := G2C1.exists_frameCoverC C.toQuasiregular
  exact arr_caseII_ambient_lci J hA hAreg C φ hd hne htw
    ⟨CN, hCN, hbcPGate_proved J hA C φ CN⟩ hj x


-- @@ L322-322 verbatim
end Final


-- @@ L324-324 verbatim
end AdamsRRCaseIILciLCI


-- @@ L326-326 verbatim
end
