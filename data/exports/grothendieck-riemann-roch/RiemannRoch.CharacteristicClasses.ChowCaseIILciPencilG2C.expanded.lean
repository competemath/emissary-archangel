/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.CharacteristicClasses.CaseIIGeomCoverG2C
import RiemannRoch.CharacteristicClasses.PencilEConcreteCIIL3B
import RiemannRoch.RelativeRiemannRoch.DeformationRegularWSheafLCI
import RiemannRoch.KTheory.PerfectRepRestrictBG2
import RiemannRoch.RelativeRiemannRoch.ZeroSectionPushK0LCI


-- @@ L12-29 verbatim
/-!
# Chow case (ii) for an lci `X ⊆ A`: the pencil K-datum (brick G2C / C2)

For a closed immersion `i : X ⟶ A` into a regular integral `ProjectiveIntegralK` ambient `A`,
with `X` integral but possibly **singular**, and `i.ker` covered by regular sequences of
constant length `r` (`C : G2C.RegularCover i.ker r`), we build the K-theoretic part of the
deformation pencil `M = totalGlobal A i.ker` **without** `K₀ M ≅ G₀ M`, `K₀ E ↪ G₀ E` or any
regularity of `X`, `M`, `E`:

* `concreteGeomXA_lci` : the pencil geometry (copy of `RG7.concreteGeomXA`, cover from `C`);
* `liftLci : K₀ X →+ K₀ M`, `x ↦ Rep_M(F_* pr^* φ⁻¹^* x)` (D1F's `regPush` along `W ↪ M`);
* `hbcA_lci`, `hbcE_lci` (`G₀`-level, as in `PencilK`), `fibreRel_lci`;
* `concretePencilK_lci : PencilK (concreteGeomXA_lci …)` (`injA` unchanged: `A` regular);
* the **`K₀`-level** base change to the exceptional divisor
  `hbcE_K0 : e^* (liftLci x) = π^* x · kosE_lci` with `kosE_lci = s_!(1)`
  (Cartier restriction of perfect classes (G2K5B) and an explicit sheaf isomorphism
  `ι_σ^* F_* V ≅ s_* E₀`).
-/


-- @@ L31-31 verbatim
set_option autoImplicit false

-- @@ L32-32 verbatim
set_option linter.unusedSectionVars false

-- @@ L33-33 verbatim
set_option linter.overlappingInstances false


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
/-! ## A. Restriction of `F_* pr^* E₀` to a Cartier divisor, as a sheaf and in `K₀` -/


-- @@ L41-41 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L43-43 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory

-- @@ L44-44 verbatim
open KSpecialization KSpecialization.AR7R KSpecialization.AR4 KSpecialization.AR8

-- @@ L45-45 verbatim
open ExactGrothendieck.CartierGysinAR1 ExactGrothendieck.CartierGysinAR8

-- @@ L46-46 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7


-- @@ L48-48 verbatim
section CartierIso


-- @@ L50-53 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)
  {W Z : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
  (F : W ⟶ Y) [IsFinite F] (pr : W ⟶ Z) [Flat pr]


-- @@ L55-56 verbatim
set_option quotPrecheck false in
local notation "ιΣ" => (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L57-58 verbatim
set_option quotPrecheck false in
local notation "ηΣ" => pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L59-60 verbatim
set_option quotPrecheck false in
local notation "FzΣ" => pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L61-62 verbatim
set_option quotPrecheck false in
local notation "TΣ" => tensorSheafLeftFunctor Y (lineBundleDual Y L)

-- @@ L63-64 verbatim
set_option quotPrecheck false in
local notation "sΣ" => sigmaT (lineBundleDual Y L) (dualEval σ)

-- @@ L65-66 verbatim
set_option quotPrecheck false in
local notation "TW" => tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L))

-- @@ L67-68 verbatim
set_option quotPrecheck false in
local notation "sW" => sigmaT _ (pullbackSection F (dualEval σ))


-- @@ L70-83 verbatim
/-- `ι_σ^*` kills the Koszul map `σ_N`, so `ι_σ^* N ≅ ι_σ^* (N / σ N)`. -/
theorem isIso_pullback_cokernel_π (hL : HasConstantRank Y L 1) (N : Y.Modules) :
    IsIso ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ N))) := by
  have hline : IsLocalLineFrame L := isLocalLineFrame_of_hasConstantRank_one hL
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) := hΛ1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  have hB := ar7Bridge σ hline
  let adj := Scheme.Modules.pullbackPushforwardAdjunction ιΣ
  haveI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback ιΣ) :=
    adj.leftAdjoint_preservesColimits
  exact ExactGrothendieck.CartierGysinAR8.isIso_map_cokernel_π_of_map_eq_zero _ _
    (map_ap_eq_zero_of_adj adj N (hB.killed_of_idealKills _ (idealKills_pushforward _ _)))


-- @@ L85-102 verbatim
/-- The `σ`-Koszul map is a monomorphism on `F_* pr^* E₀` (from `hs` on `W`). -/
theorem mono_ap_pushforward (hL : HasConstantRank Y L 1)
    [Mono (pullbackSection F (dualEval σ))] (E0 : Z.Modules) (hE0 : IsFiniteLocallyFree Z E0) :
    Mono (ap TΣ sΣ ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0))) := by
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) := hΛ1.isFiniteLocallyFree
  have hΛW1 := SchemeKTheory.hasConstantRank_pullback W F _ 1 hΛ1
  have hΛW : IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)) :=
    hΛW1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _ hΛW
  haveI := CIIL3B.hMono_of_mono_pullbackSection σ F pr E0 hE0
  haveI : (Scheme.Modules.pushforward F).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction F).isRightAdjoint
  rw [(pushCompat F (dualEval σ) hΛ).ap_eq]
  infer_instance


-- @@ L104-165 verbatim
/-- **The sheaf isomorphism** `ι_σ^* F_* pr^* E₀ ≅ s_* E₀`, `s = (pr ∘ η)⁻¹ ≫ snd`, when
`W ×_Y V(σ) ≅ Z` via `pr`. -/
def restrictPushIso (hL : HasConstantRank Y L 1) [IsIso (ηΣ ≫ pr)]
    (E0 : Z.Modules) (hE0 : IsCoherentLike Z E0) :
    (Scheme.Modules.pullback ιΣ).obj
        ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0)) ≅
      (Scheme.Modules.pushforward (inv (ηΣ ≫ pr) ≫ FzΣ)).obj E0 := by
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) := hΛ1.isFiniteLocallyFree
  have hΛW1 := SchemeKTheory.hasConstantRank_pullback W F _ 1 hΛ1
  have hΛW : IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)) :=
    hΛW1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _ hΛW
  letI : E0.IsFinitePresentation := hE0
  have hV₀ : IsCoherentLike W ((Scheme.Modules.pullback pr).obj E0) :=
    pullback_isFinitePresentation_global pr E0
  have hT := tensorSheaf_isCoherentLike W _ _ hΛW hV₀
  haveI : IsIso (cokernelComparison (ap TW sW ((Scheme.Modules.pullback pr).obj E0))
      (Scheme.Modules.pushforward F)) :=
    isIso_cokernelComparison_pushforward F _ hT hV₀
  haveI := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL ((Scheme.Modules.pullback pr).obj E0)
  haveI := KSpecialization.ARRHU.hunit_ARRHU σ hL F ((Scheme.Modules.pullback pr).obj E0) hV₀
  haveI := isIso_pullback_cokernel_π σ hL
    ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0))
  haveI : (Scheme.Modules.pushforward ιΣ).Full :=
    (KSpecialization.pushforwardFullyFaithful ιΣ).full
  haveI : (Scheme.Modules.pushforward ιΣ).Faithful :=
    (KSpecialization.pushforwardFullyFaithful ιΣ).faithful
  haveI : IsIso (Scheme.Modules.pullbackPushforwardAdjunction ιΣ).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  -- `Q_W = V / σ_W V`, `G = Fz_* η^* Q_W`
  let QW := cokernel (ap TW sW ((Scheme.Modules.pullback pr).obj E0))
  let G := (Scheme.Modules.pushforward FzΣ).obj ((Scheme.Modules.pullback ηΣ).obj QW)
  -- `e : ι_* G ≅ F_* Q_W` (as in `hbcE_pencil_fibre_bundle`)
  let e : (Scheme.Modules.pushforward ιΣ).obj G ≅ (Scheme.Modules.pushforward F).obj QW :=
    (Scheme.Modules.pushforwardComp FzΣ ιΣ).app _ ≪≫
      (Scheme.Modules.pushforwardCongr pullback.condition.symm).app _ ≪≫
      ((Scheme.Modules.pushforwardComp ηΣ F).app _).symm ≪≫
      (Scheme.Modules.pushforward F).mapIso
        (asIso (SchemeKTheory.ProjectionFormula.adjUnit ηΣ QW)).symm
  let c := pushCompat F (dualEval σ) hΛ
  let step1 := asIso ((Scheme.Modules.pullback ιΣ).map
    (cokernel.π (ap TΣ sΣ ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0)))))
  let step2 : cokernel (ap TΣ sΣ ((Scheme.Modules.pushforward F).obj
      ((Scheme.Modules.pullback pr).obj E0))) ≅ (Scheme.Modules.pushforward ιΣ).obj G :=
    cokernelIso c _ ≪≫ e.symm
  let step3 : (Scheme.Modules.pullback ιΣ).obj ((Scheme.Modules.pushforward ιΣ).obj G) ≅ G :=
    (asIso (Scheme.Modules.pullbackPushforwardAdjunction ιΣ).counit).app G
  let step4 : G ≅ (Scheme.Modules.pushforward FzΣ).obj
      ((Scheme.Modules.pullback ηΣ).obj ((Scheme.Modules.pullback pr).obj E0)) :=
    (Scheme.Modules.pushforward FzΣ).mapIso (asIso ((Scheme.Modules.pullback ηΣ).map
      (cokernel.π (ap TW sW ((Scheme.Modules.pullback pr).obj E0))))).symm
  let step5 : (Scheme.Modules.pullback ηΣ).obj ((Scheme.Modules.pullback pr).obj E0) ≅
      (Scheme.Modules.pushforward (inv (ηΣ ≫ pr))).obj E0 :=
    (Scheme.Modules.pullbackComp ηΣ pr).app E0 ≪≫
      (ARRG45C.pullbackHomIsoPushforwardInv (asIso (ηΣ ≫ pr))).app E0
  exact step1 ≪≫ (Scheme.Modules.pullback ιΣ).mapIso step2 ≪≫ step3 ≪≫ step4 ≪≫
    (Scheme.Modules.pushforward FzΣ).mapIso step5 ≪≫
    (Scheme.Modules.pushforwardComp (inv (ηΣ ≫ pr)) FzΣ).app E0


-- @@ L167-169 verbatim
variable [IsLocallyNoetherian (sectionEvaluationIdealSheaf σ).subscheme]
  (hY : PerfectRepG2.Sch.HasBundleCovers Y)
  (hD : PerfectRepG2.Sch.HasBundleCovers (sectionEvaluationIdealSheaf σ).subscheme)


-- @@ L171-183 verbatim
/-- The pushforward `s_* E₀` along the "zero section" `s = (pr ∘ η)⁻¹ ≫ snd` of a bundle has the
same bundle dimension bound as `F_* pr^* E₀`. -/
theorem pdLE_restrictPush (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    [Mono (pullbackSection F (dualEval σ))] [IsIso (ηΣ ≫ pr)]
    (E0 : Z.Modules) (hE0 : IsFiniteLocallyFree Z E0) {d : ℕ}
    (hN : IsCoherentLike Y ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0)))
    (hd : PerfectRepG2.Sch.PdLE hY d
      ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0))) :
    PerfectRepG2.Sch.PdLE hD d ((Scheme.Modules.pushforward (inv (ηΣ ≫ pr) ≫ FzΣ)).obj E0) :=
  PerfectRepG2.Sch.pdLE_iso hD (restrictPushIso σ F pr hL E0 hE0.isFinitePresentation)
    (PerfectRepRestrictBG2.Sch.pdLE_pullback_cartier σ hY hD hL
      (fun E hE => CIIL3B.hmono_of_sectionIsRegular σ (isLocalLineFrame_of_hasConstantRank_one hL)
        hreg E hE) hN (mono_ap_pushforward σ F pr hL E0 hE0) hd)


-- @@ L185-203 verbatim
/-- **`K₀`-level Tor-independent restriction to the Cartier divisor `V(σ)`**:
`ι_σ^* Rep(F_* pr^* E₀) = Rep(s_* E₀)` in `K₀(V(σ))`. -/
theorem pullbackK0_repK0_restrictPush (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    [Mono (pullbackSection F (dualEval σ))] [IsIso (ηΣ ≫ pr)]
    (E0 : Z.Modules) (hE0 : IsFiniteLocallyFree Z E0) {d d' : ℕ}
    (hN : IsCoherentLike Y ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0)))
    (hd : PerfectRepG2.Sch.PdLE hY d
      ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj E0)))
    (hS : IsCoherentLike (sectionEvaluationIdealSheaf σ).subscheme
      ((Scheme.Modules.pushforward (inv (ηΣ ≫ pr) ≫ FzΣ)).obj E0))
    (hd' : PerfectRepG2.Sch.PdLE hD d' ((Scheme.Modules.pushforward (inv (ηΣ ≫ pr) ≫ FzΣ)).obj E0)) :
    pullbackK0 ιΣ (PerfectRepG2.Sch.repK0 hY _ hN hd) = PerfectRepG2.Sch.repK0 hD _ hS hd' := by
  have hbund : ∀ E, IsFiniteLocallyFree Y E → Mono (ap TΣ sΣ E) := fun E hE =>
    CIIL3B.hmono_of_sectionIsRegular σ (isLocalLineFrame_of_hasConstantRank_one hL) hreg E hE
  have hm := mono_ap_pushforward σ F pr hL E0 hE0
  rw [PerfectRepRestrictBG2.Sch.pullbackK0_repK0_cartier_of_regular σ hY hD hL hreg _ hN hm hd
    (PerfectRepRestrictBG2.Sch.isCoherentLike_pullback ιΣ hN)
    (PerfectRepRestrictBG2.Sch.pdLE_pullback_cartier σ hY hD hL hbund hN hm hd)]
  exact PerfectRepG2.Sch.repK0_iso hD (restrictPushIso σ F pr hL E0 hE0.isFinitePresentation) _ _ _ _


-- @@ L205-205 verbatim
end CartierIso


-- @@ L207-207 verbatim
end GRRBlueprintV4.G2CC2


-- @@ L209-209 verbatim
/-! ## B. The library pencil over `V(J)`: lift, `HbcA`, `HbcE` (bundle form, extended additively) -/


-- @@ L211-211 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L213-213 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory

-- @@ L214-218 verbatim
open SchemeNormalCone.AlgebraicGeometry SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalCompletion
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityExceptionalGlobal
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal


-- @@ L220-229 verbatim
/-- Extension from bundle classes: two additive maps out of `K₀ Z` agreeing on bundles agree. -/
theorem ext_k0 {Z : Scheme.{u}} {B : Type*} [AddCommGroup B] (f g : K0 Z →+ B)
    (h : ∀ (E : Z.Modules) (hE : IsFiniteLocallyFree Z E), f (k0ClassOf Z E hE) = g (k0ClassOf Z E hE))
    (x : K0 Z) : f x = g x := by
  have hfg : f = g := by
    apply ExactGrothendieck.hom_ext
    intro E
    obtain ⟨E, hE⟩ := E
    exact h E hE
  rw [hfg]


-- @@ L231-231 verbatim
section HbcBundle


-- @@ L233-233 verbatim
open KSpecialization KSpecialization.CIIL3B AlgebraicGeometry.Chow.M7 ExactGrothendieck.PrincipalGysin


-- @@ L235-281 verbatim
/-- **HbcA for the library pencil, one bundle** (`CIIL3B.hbcA_pencil` without `K₀ M = G₀ M`). -/
theorem hbcA_pencil_bundle_total (Y : Scheme.{u}) (J : Y.IdealSheafData) (k : Type u) [CommRing k]
    (φk : k →+* Γ(Y, ⊤)) [IsIntegral Y] [IsIntegral J.subscheme] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian (totalGlobal Y J)] (E0 : J.subscheme.Modules)
    (hE0 : IsFiniteLocallyFree J.subscheme E0) (y : K0 (totalGlobal Y J))
    (hy : k0ToG0 (totalGlobal Y J) y = finitePushforward (subschemeTotalGlobalι Y J)
      (flatPullbackG0 (totalToClosedBase Y J) (g0ClassOf J.subscheme E0 hE0.isFinitePresentation))) :
    k0ToG0 Y (pullbackK0 (fibreιGlobal Y J k φk 1) y) =
      finitePushforward J.subschemeι (g0ClassOf J.subscheme E0 hE0.isFinitePresentation) := by
  obtain ⟨e, he⟩ := exists_fibre_iso Y J k φk 1
  obtain ⟨e₀, he₀⟩ := exists_fibre_iso Y J k φk 0
  haveI : IsLocallyNoetherian (subschemeTotalGlobal Y J) :=
    LocallyOfFiniteType.isLocallyNoetherian (subschemeTotalGlobalι Y J)
  haveI : IsLocallyNoetherian (DeformationSpace.line Y) :=
    isLocallyNoetherian_of_isOpenImmersion (lineTι Y J)
  haveI : IsLocallyNoetherian (subschemeUGlobal Y J) :=
    isLocallyNoetherian_of_isOpenImmersion (subschemeTιGlobal Y J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI : IsIntegral (DeformationSpace.line Y) := IntegralARRM346.isIntegral_line Y
  haveI : IsIntegral (subschemeTotalGlobal Y J) := IntegralARRM346.isIntegral_subschemeTotalGlobal Y J
  have hσ0 := sigma_toBase Y J k φk 0 e₀ he₀
  haveI : Nonempty (subschemeUGlobal Y J) := by
    let sW : J.subscheme ⟶ subschemeUGlobal Y J :=
      (isPullback_subschemeLine Y J).lift (J.subschemeι ≫ e₀.hom ≫ zeroι _) (𝟙 _) (by
        rw [Category.assoc, hσ0]; simp)
    obtain ⟨z⟩ := (inferInstance : Nonempty J.subscheme)
    exact ⟨sW z⟩
  haveI : IsIntegral (subschemeUGlobal Y J) := isIntegral_of_isOpenImmersion (subschemeTιGlobal Y J)
  have hmono : ∀ E : (DeformationSpace.line Y).Modules, IsFiniteLocallyFree _ E →
      Mono (tMul (lineFn Y k φk 1) E) := fun E hE =>
    mono_tMul_of_isIntegral _ (lineFn_one_ne_zero Y k φk) E hE
  have hmonoW : ∀ E : J.subscheme.Modules, IsFiniteLocallyFree _ E →
      Mono (tMul ((subschemeToLineGlobal Y J).appTop (lineFn Y k φk 1))
        ((Scheme.Modules.pullback (subschemeTιGlobal Y J)).obj
          ((Scheme.Modules.pullback (totalToClosedBase Y J)).obj E))) := fun E hE =>
    mono_tMul_of_isIntegral _ (lineFn_one_pullback_ne_zero Y J k φk) _
      (pullback_isFiniteLocallyFree_global _ _ (pullback_isFiniteLocallyFree_global _ _ hE))
  have hσ := sigma_toBase Y J k φk 1 e he
  have hsq' : IsPullback (subschemeToLineGlobal Y J) (subschemeTιGlobal Y J ≫ totalToClosedBase Y J)
      (DeformationSpace.toBase Y ⊥) J.subschemeι := by
    rw [subschemeTι_totalToClosedBase]; exact isPullback_subschemeLine Y J
  obtain ⟨hiso, hsi⟩ := fibre_of_section (DeformationSpace.toBase Y ⊥) (e.hom ≫ zeroι _) hσ
    (lineFn Y k φk 1) e rfl (subschemeToLineGlobal Y J) _ J.subschemeι hsq'
  haveI := hiso
  exact hbcA_pencil_bundle (subschemeTotalGlobalι Y J) (lineTι Y J) (subschemeTιGlobal Y J)
    (subschemeToLineGlobal Y J) (isPullback_lineTι_subschemeTotal Y J) (lineFn Y k φk 1)
    (totalToClosedBase Y J) J.subschemeι (fibreιGlobal Y J k φk 1) e he hmono hmonoW hsi E0 hE0 y hy


-- @@ L283-317 verbatim
/-- **HbcE for the library pencil, one bundle** (`CIIL3B.hbcE_pencil` without `K₀ M = G₀ M`). -/
theorem hbcE_pencil_bundle_total (Y : Scheme.{u}) (J : Y.IdealSheafData) (k : Type u) [CommRing k]
    (φk : k →+* Γ(Y, ⊤)) [IsIntegral J.subscheme] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian (totalGlobal Y J)]
    {L : (totalGlobal Y J).Modules} [L.IsQuasicoherent] [L.IsFinitePresentation]
    (σ : tensorUnitSheaf (totalGlobal Y J) ⟶ L)
    (hL : HasConstantRank (totalGlobal Y J) L 1) (hreg : SectionIsRegular σ)
    (hid : sectionEvaluationIdealSheaf σ = (componentToTotal Y J).ker)
    (E0 : J.subscheme.Modules) (hE0 : IsFiniteLocallyFree J.subscheme E0) (y : K0 (totalGlobal Y J))
    (hy : k0ToG0 (totalGlobal Y J) y = finitePushforward (subschemeTotalGlobalι Y J)
      (flatPullbackG0 (totalToClosedBase Y J) (g0ClassOf J.subscheme E0 hE0.isFinitePresentation))) :
    haveI : IsIso (pullback.fst (subschemeTotalGlobalι Y J)
        (sectionEvaluationIdealSheaf σ).subschemeι ≫ totalToClosedBase Y J) :=
      haveI := isIso_fst_comp_totalToClosedBase Y J
      isIso_fst_comp_of_ker_eq (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
        (sectionEvaluationIdealSheaf σ).subschemeι (componentToTotal Y J)
        (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hid)
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme
        (pullbackK0 (sectionEvaluationIdealSheaf σ).subschemeι y) =
      finitePushforward
        (inv (pullback.fst (subschemeTotalGlobalι Y J)
          (sectionEvaluationIdealSheaf σ).subschemeι ≫ totalToClosedBase Y J) ≫
          pullback.snd (subschemeTotalGlobalι Y J) (sectionEvaluationIdealSheaf σ).subschemeι)
        (g0ClassOf J.subscheme E0 hE0.isFinitePresentation) := by
  haveI : IsLocallyNoetherian (subschemeTotalGlobal Y J) :=
    LocallyOfFiniteType.isLocallyNoetherian (subschemeTotalGlobalι Y J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI := isIso_fst_comp_totalToClosedBase Y J
  haveI : IsIso (pullback.fst (subschemeTotalGlobalι Y J)
      (sectionEvaluationIdealSheaf σ).subschemeι ≫ totalToClosedBase Y J) :=
    isIso_fst_comp_of_ker_eq (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
      (sectionEvaluationIdealSheaf σ).subschemeι (componentToTotal Y J)
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hid)
  exact hbcE_pencil_fibre_bundle σ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL hreg
    (KSpecialization.ARRHS.mono_pullbackSection_exceptional Y J σ k φk hL hreg hid) E0 hE0 y hy


-- @@ L319-319 verbatim
end HbcBundle


-- @@ L321-321 verbatim
end GRRBlueprintV4.G2CC2


-- @@ L323-323 verbatim
/-! ## C. The lift `K₀ V(J) →+ K₀ M` and its base changes over a projective integral ambient -/


-- @@ L325-325 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L327-327 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory

-- @@ L328-332 verbatim
open SchemeNormalCone.AlgebraicGeometry SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalCompletion
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityExceptionalGlobal
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal

-- @@ L333-333 verbatim
open AlgebraicGeometry.Chow.M7 AlgebraicGeometry.Chow.M7.CIICLASS


-- @@ L335-335 verbatim
section LiftZ


-- @@ L337-339 verbatim
variable {k : Type u} [Field k] {A : Scheme.{u}} [A.Over (Spk k)]
  [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A]
  (J : A.IdealSheafData) (hA : ProjectiveIntegralK k A) {r : ℕ} (C : G2C.RegularCover J r)


-- @@ L341-347 verbatim
include hA C in
/-- **The lift** `ℓ : K₀ V(J) →+ K₀ M`, `[E₀] ↦ Rep_M(F_* pr^* E₀)` (`F : W = V(J) × ℙ¹ ↪ M`). -/
def liftZ : K0 J.subscheme →+ K0 (totalGlobal A J) :=
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  (DeformationRegularWSheafLCI.regPushOfRegularCover
    (BundleCoversProjBundleG2.hasBundleCovers_total J hA) C).comp
    (pullbackK0 (totalToClosedBase A J))


-- @@ L349-363 verbatim
theorem liftZ_k0ClassOf (E0 : J.subscheme.Modules) (hE0 : IsFiniteLocallyFree J.subscheme E0) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
    liftZ J hA C (k0ClassOf _ E0 hE0) =
      PerfectRepG2.Sch.repK0 (BundleCoversProjBundleG2.hasBundleCovers_total J hA)
        ((Scheme.Modules.pushforward (subschemeTotalGlobalι A J)).obj
          ((Scheme.Modules.pullback (totalToClosedBase A J)).obj E0))
        (finitePushObject (subschemeTotalGlobalι A J)
          ⟨_, (pullback_isFiniteLocallyFree_global _ E0 hE0).isFinitePresentation⟩).2
        (DeformationRegularWSheafLCI.pdLE_pushforward_of_regularCover _ C _
          (pullback_isFiniteLocallyFree_global _ E0 hE0)) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  change DeformationRegularWSheafLCI.regPushOfRegularCover _ C
    (pullbackK0 (totalToClosedBase A J) (k0ClassOf _ E0 hE0)) = _
  rw [pullbackK0_classOf]
  exact DeformationRegularWSheafLCI.regPushOfRegularCover_k0ClassOf _ C _ _


-- @@ L365-376 verbatim
theorem k0ToG0_liftZ (x : K0 J.subscheme) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
    k0ToG0 (totalGlobal A J) (liftZ J hA C x) =
      finitePushforward (subschemeTotalGlobalι A J)
        (flatPullbackG0 (totalToClosedBase A J) (k0ToG0 J.subscheme x)) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  haveI : IsLocallyNoetherian (subschemeTotalGlobal A J) :=
    LocallyOfFiniteType.isLocallyNoetherian (subschemeTotalGlobalι A J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  change k0ToG0 _ (DeformationRegularWSheafLCI.regPushOfRegularCover _ C
    (pullbackK0 (totalToClosedBase A J) x)) = _
  rw [DeformationRegularWSheafLCI.k0ToG0_regPushOfRegularCover, ARRG45C.k0ToG0_pullbackK0]


-- @@ L378-378 verbatim
variable [IsIntegral A] [IsIntegral J.subscheme] (φk : k →+* Γ(A, ⊤))


-- @@ L380-391 verbatim
/-- **HbcA** for the lift (any class): `j₁^* ℓ(x) = i_* x` in `G₀ A`. -/
theorem hbcA_liftZ (x : K0 J.subscheme) :
    k0ToG0 A (pullbackK0 (fibreιGlobal A J k φk 1) (liftZ J hA C x)) =
      finitePushforward J.subschemeι (k0ToG0 J.subscheme x) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  refine ext_k0 ((k0ToG0 A).comp ((pullbackK0 (fibreιGlobal A J k φk 1)).comp (liftZ J hA C)))
    ((finitePushforward J.subschemeι).comp (k0ToG0 J.subscheme)) (fun E0 hE0 => ?_) x
  change k0ToG0 A (pullbackK0 (fibreιGlobal A J k φk 1) (liftZ J hA C (k0ClassOf _ E0 hE0))) =
    finitePushforward J.subschemeι (k0ToG0 J.subscheme (k0ClassOf _ E0 hE0))
  rw [k0ToG0_classOf]
  refine hbcA_pencil_bundle_total A J k φk E0 hE0 _ ?_
  rw [k0ToG0_liftZ, k0ToG0_classOf]


-- @@ L393-393 verbatim
end LiftZ


-- @@ L395-395 verbatim
section Sigma


-- @@ L397-397 verbatim
open GRRBlueprintV4.RG7


-- @@ L399-402 verbatim
variable {k : Type u} [Field k] {A : Scheme.{u}} [A.Over (Spk k)]
  [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A] [IsIntegral A]
  (J : A.IdealSheafData) [IsIntegral J.subscheme] (hA : ProjectiveIntegralK k A) {r : ℕ}
  (C : G2C.RegularCover J r) (φk : k →+* Γ(A, ⊤))


-- @@ L404-408 verbatim
include hA in
/-- `S_σ ≅ E` has bundle covers (closed in `M`). -/
theorem hasBundleCovers_sigma : PerfectRepG2.Sch.HasBundleCovers (Ssigma J φk) :=
  BundleCoversProjBundleG2.hasBundleCovers_of_projEmb
    (AR11.ProjEmb.of_closedImmersion (iotaSigma J φk) (KG2B.projEmb_total J hA))


-- @@ L410-413 verbatim
include hA in
theorem isLocallyNoetherian_sigma : IsLocallyNoetherian (Ssigma J φk) :=
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  inferInstance


-- @@ L415-435 verbatim
include hA C in
/-- The zero section `s_σ : V(J) ⟶ S_σ` has `PdLE r` direct images of bundles. -/
theorem pdLE_zeroSigma (V : J.subscheme.Modules) (hV : IsFiniteLocallyFree J.subscheme V) :
    haveI := isLocallyNoetherian_sigma J hA φk
    PerfectRepG2.Sch.PdLE (hasBundleCovers_sigma J hA φk) r
      ((Scheme.Modules.pushforward (zeroSigma J φk)).obj V) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  haveI : IsLocallyNoetherian (subschemeTotalGlobal A J) :=
    LocallyOfFiniteType.isLocallyNoetherian (subschemeTotalGlobalι A J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI := (ARRKG2A.oeGate A φk J).qc
  haveI := (ARRKG2A.oeGate A φk J).fp
  haveI := KSpecialization.ARRHS.mono_pullbackSection_exceptional A J (ARRKG2A.oeGate A φk J).σ k φk
    (ARRKG2A.oeGate A φk J).hL (ARRKG2A.oeGate A φk J).hreg (ARRKG2A.oeGate A φk J).hid
  exact pdLE_restrictPush (ARRKG2A.oeGate A φk J).σ (subschemeTotalGlobalι A J)
    (totalToClosedBase A J) (BundleCoversProjBundleG2.hasBundleCovers_total J hA)
    (hasBundleCovers_sigma J hA φk) (ARRKG2A.oeGate A φk J).hL (ARRKG2A.oeGate A φk J).hreg V hV
    (finitePushObject (subschemeTotalGlobalι A J)
      ⟨_, (pullback_isFiniteLocallyFree_global _ V hV).isFinitePresentation⟩).2
    (DeformationRegularWSheafLCI.pdLE_pushforward_of_regularCover _ C _
      (pullback_isFiniteLocallyFree_global _ V hV))


-- @@ L437-441 verbatim
/-- The Euler-class pushforward along the zero section `s_σ : V(J) ⟶ S_σ` (B5's `liftPush`). -/
def zsSigma : K0 J.subscheme →+ K0 (Ssigma J φk) :=
  haveI := isLocallyNoetherian_sigma J hA φk
  ZeroSectionPushK0LCI.liftPush (zeroSigma J φk) (hasBundleCovers_sigma J hA φk) r
    (pdLE_zeroSigma J hA C φk)


-- @@ L443-447 verbatim
theorem k0ToG0_zsSigma (x : K0 J.subscheme) :
    haveI := isLocallyNoetherian_sigma J hA φk
    k0ToG0 _ (zsSigma J hA C φk x) = finitePushforward (zeroSigma J φk) (k0ToG0 _ x) :=
  haveI := isLocallyNoetherian_sigma J hA φk
  ZeroSectionPushK0LCI.k0ToG0_liftPush_apply _ _ _ _ x


-- @@ L449-468 verbatim
/-- **`K₀`-level HbcE on `S_σ`**: `ι_σ^* ℓ(x) = s_{σ!}(x)` in `K₀(S_σ)`, any `x ∈ K₀ V(J)`. -/
theorem hbcSigma_K0 (x : K0 J.subscheme) :
    pullbackK0 (iotaSigma J φk) (liftZ J hA C x) = zsSigma J hA C φk x := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  haveI : IsLocallyNoetherian (subschemeTotalGlobal A J) :=
    LocallyOfFiniteType.isLocallyNoetherian (subschemeTotalGlobalι A J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  haveI := (ARRKG2A.oeGate A φk J).qc
  haveI := (ARRKG2A.oeGate A φk J).fp
  haveI := KSpecialization.ARRHS.mono_pullbackSection_exceptional A J (ARRKG2A.oeGate A φk J).σ k φk
    (ARRKG2A.oeGate A φk J).hL (ARRKG2A.oeGate A φk J).hreg (ARRKG2A.oeGate A φk J).hid
  refine ext_k0 ((pullbackK0 (iotaSigma J φk)).comp (liftZ J hA C)) (zsSigma J hA C φk)
    (fun E0 hE0 => ?_) x
  change pullbackK0 (iotaSigma J φk) (liftZ J hA C (k0ClassOf _ E0 hE0)) =
    zsSigma J hA C φk (k0ClassOf _ E0 hE0)
  rw [liftZ_k0ClassOf, zsSigma, ZeroSectionPushK0LCI.liftPush_k0ClassOf]
  exact pullbackK0_repK0_restrictPush (ARRKG2A.oeGate A φk J).σ (subschemeTotalGlobalι A J)
    (totalToClosedBase A J) (BundleCoversProjBundleG2.hasBundleCovers_total J hA)
    (hasBundleCovers_sigma J hA φk) (ARRKG2A.oeGate A φk J).hL (ARRKG2A.oeGate A φk J).hreg
    E0 hE0 _ _ _ _


-- @@ L470-475 verbatim
/-- **HbcE** (`G₀`) on `S_σ`, from the `K₀` statement. -/
theorem hbcE_sigma_liftZ (x : K0 J.subscheme) :
    haveI := isLocallyNoetherian_sigma J hA φk
    k0ToG0 (Ssigma J φk) (pullbackK0 (iotaSigma J φk) (liftZ J hA C x)) =
      finitePushforward (zeroSigma J φk) (k0ToG0 J.subscheme x) := by
  rw [hbcSigma_K0, k0ToG0_zsSigma]


-- @@ L477-479 verbatim
/-- The Koszul class on `E` (`Z`-level): `κ = (ψ⁻¹)^* s_{σ!}(1)`. -/
def kosEZ : K0 (component A J) :=
  pullbackK0 (inv (psiSigma J φk)) (zsSigma J hA C φk 1)


-- @@ L481-491 verbatim
/-- `s_{σ!}(z) = π_σ^* z · s_{σ!}(1)` (projection formula, `π_σ ∘ s_σ = id`). -/
theorem zsSigma_eq (z : K0 J.subscheme) :
    zsSigma J hA C φk z =
      pullbackK0 (psiSigma J φk ≫ componentToCentre A J) z * zsSigma J hA C φk 1 := by
  haveI := isLocallyNoetherian_sigma J hA φk
  have h := ZeroSectionPushK0LCI.liftPush_projection (zeroSigma J φk) (hasBundleCovers_sigma J hA φk)
    r (pdLE_zeroSigma J hA C φk) (pullbackK0 (psiSigma J φk ≫ componentToCentre A J) z) 1
  have hz : zeroSigma J φk ≫ psiSigma J φk ≫ componentToCentre A J = 𝟙 J.subscheme := by
    rw [← Category.assoc]; exact zeroE_comp_centre J φk
  rw [mul_one, pullbackK0RingHom_apply, pullbackK0_comp_apply, hz, pullbackK0_id] at h
  exact h


-- @@ L493-502 verbatim
/-- **`K₀`-level HbcE on `E`** (`Z`-level): `e^* ℓ(z) = π_E^* z · κ`. -/
theorem hbcE_K0_Z (z : K0 J.subscheme) :
    pullbackK0 (componentToTotal A J) (liftZ J hA C z) =
      pullbackK0 (componentToCentre A J) z * kosEZ J hA C φk := by
  have h1 : pullbackK0 (componentToTotal A J) (liftZ J hA C z) =
      pullbackK0 (inv (psiSigma J φk)) (pullbackK0 (iotaSigma J φk) (liftZ J hA C z)) := by
    rw [pullbackK0_comp_apply, ← psiSigma_fac J φk, IsIso.inv_hom_id_assoc]
  rw [h1, hbcSigma_K0, zsSigma_eq, kosEZ, ← pullbackK0RingHom_apply, map_mul,
    pullbackK0RingHom_apply, pullbackK0RingHom_apply, pullbackK0_comp_apply,
    IsIso.inv_hom_id_assoc]


-- @@ L504-530 verbatim
/-- **HbcE** (`G₀`) on `E` for the lift (copy of `RG7.hbcE_concrete'` without `bijective_total`). -/
theorem hbcE_component_liftZ (x : K0 J.subscheme) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
    haveI : IsLocallyNoetherian (component A J) :=
      LocallyOfFiniteType.isLocallyNoetherian (componentToTotal A J)
    k0ToG0 (component A J) (pullbackK0 (componentToTotal A J) (liftZ J hA C x)) =
      finitePushforward (zeroE J φk) (k0ToG0 J.subscheme x) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total J hA
  haveI : IsLocallyNoetherian (component A J) :=
    LocallyOfFiniteType.isLocallyNoetherian (componentToTotal A J)
  haveI : IsLocallyNoetherian J.subscheme := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have hbc := hbcE_sigma_liftZ J hA C φk x
  set ε := pullbackK0 (componentToTotal A J) (liftZ J hA C x) with hε
  have h1 : pullbackK0 (iotaSigma J φk) (liftZ J hA C x) = pullbackK0 (psiSigma J φk) ε := by
    rw [hε, pullbackK0_comp_apply, psiSigma_fac]
  have h2 : k0ToG0 (Ssigma J φk) (pullbackK0 (psiSigma J φk) ε) =
      finitePushforward (inv (psiSigma J φk)) (k0ToG0 (component A J) ε) := by
    rw [ARRG45C.k0ToG0_pullbackK0]
    exact DFunLike.congr_fun
      (ARRG45C.flatPullbackG0_iso_eq_finitePushforward_inv (asIso (psiSigma J φk))) _
  rw [h1, h2] at hbc
  have h3 := congrArg (finitePushforward (psiSigma J φk)) hbc
  rw [CIIASM.finitePushforward_inv_cancel] at h3
  rw [h3]
  unfold zeroE
  rw [ARRG45C.finitePushforward_comp]
  rfl


-- @@ L532-532 verbatim
end Sigma


-- @@ L534-534 verbatim
/-! ## D. The pencil over `X` itself -/


-- @@ L536-536 verbatim
section FibreRel


-- @@ L538-538 verbatim
open GRRBlueprintV4.RG7 AlgebraicGeometry.Chow.M7.CIIB6 AlgebraicGeometry.Chow.M7.CIIB7 AlgebraicGeometry.Chow.M7.K3


-- @@ L540-544 verbatim
variable {k : Type u} [Field k] [Infinite k] {A : Scheme.{u}} [A.Over (Spk k)]
  [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A] [IsIntegral A]
  (J : A.IdealSheafData) [IsIntegral J.subscheme]
  (hA : ProjectiveIntegralK k A) {r : ℕ} (Cq : ConormalSheaf.QuasiregularCover J r)
  (φk : k →+* Γ(A, ⊤))


-- @@ L546-596 verbatim
include hA Cq in
/-- **FibreRel** from a quasi-regular cover (copy of `RG7.fibreRel_ambient`; no regularity). -/
theorem fibreRel_cover (c : k) :
    letI := KG2B.zOver (k := k) J
    haveI := z_lft (k := k) J
    haveI := z_noeth J
    letI := totalOver (k := k) J
    haveI := total_lft (k := k) J hA
    haveI := total_isNoetherian (k := k) J hA
    haveI := SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.IntegralARRM346.isIntegral_totalGlobal
      A J
    haveI : Fact (D28.ProjectiveIntegral k (totalGlobal A J)) :=
      ⟨CIICLASS.projectiveIntegral_of_K (projectiveIntegralK_total (k := k) J hA)⟩
    letI := componentOver (k := k) J
    haveI := component_lft J Cq (KG2B.projectiveIntegralK_Z J hA)
    haveI := component_isNoetherian J Cq (KG2B.projectiveIntegralK_Z J hA)
    haveI : Fact (D28.ProjectiveIntegral k (component A J)) :=
      ⟨CIICLASS.projectiveIntegral_of_K (G2C1.projectiveIntegralK_EC J Cq hA)⟩
    haveI : Fact (D28.ProjectiveIntegral k A) := ⟨CIICLASS.projectiveIntegral_of_K hA⟩
    haveI := fibre_isOver' (k := k) J φk c
    haveI := component_isOver' (k := k) J
    ∃ (L N : (totalGlobal A J).Modules)
      (hL : SchemeKTheory.HasConstantRank (totalGlobal A J) L 1)
      (hN : SchemeKTheory.HasConstantRank (totalGlobal A J) N 1),
      totalPushOn (GRRBlueprintV4.opsV4 k) (fibreιGlobal A J k φk c)
          (GRRBlueprintV4.fundClass k (W := A)) =
        totalCapOn (GRRBlueprintV4.opsV4 k) (A5FR.LPof L N) (A5FR.hasConstantRank_LPof hL hN)
            (GRRBlueprintV4.fundClass k (W := totalGlobal A J)) +
          totalPushOn (GRRBlueprintV4.opsV4 k) (componentToTotal A J)
            (GRRBlueprintV4.fundClass k (W := component A J)) := by
  letI := KG2B.zOver (k := k) J
  haveI := z_lft (k := k) J
  haveI := z_noeth J
  letI := totalOver (k := k) J
  haveI := total_lft (k := k) J hA
  haveI := total_isNoetherian (k := k) J hA
  haveI := SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.IntegralARRM346.isIntegral_totalGlobal
    A J
  haveI : Fact (D28.ProjectiveIntegral k (totalGlobal A J)) :=
    ⟨CIICLASS.projectiveIntegral_of_K (projectiveIntegralK_total (k := k) J hA)⟩
  letI := componentOver (k := k) J
  haveI := component_lft J Cq (KG2B.projectiveIntegralK_Z J hA)
  haveI := component_isNoetherian J Cq (KG2B.projectiveIntegralK_Z J hA)
  haveI : Fact (D28.ProjectiveIntegral k (component A J)) :=
    ⟨CIICLASS.projectiveIntegral_of_K (G2C1.projectiveIntegralK_EC J Cq hA)⟩
  haveI : Fact (D28.ProjectiveIntegral k A) := ⟨CIICLASS.projectiveIntegral_of_K hA⟩
  haveI := fibre_isOver' (k := k) J φk c
  haveI := component_isOver' (k := k) J
  haveI := isIntegral_component J Cq (KG2B.projectiveIntegralK_Z J hA)
  obtain ⟨d, hd⟩ := exists_height_generic hA
  exact FRI.fibreRel_totalGlobal_of_height A J φk c (n := d) hd


-- @@ L598-598 verbatim
end FibreRel


-- @@ L600-600 verbatim
end GRRBlueprintV4.G2CC2


-- @@ L602-602 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L604-614 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order SchemeKTheory SchemeProjectiveSpace
  AlgebraicGeometry.Chow.M7 AlgebraicGeometry.Chow.M7.CIICLASS AlgebraicGeometry.Chow.M7.D28
  AlgebraicGeometry.Chow.M7.CIIB6 AlgebraicGeometry.Chow.M7.CIIB7 AlgebraicGeometry.Chow.M7.K3
  AlgebraicGeometry.Chow.M7.FRI AlgebraicGeometry.Chow.M7.A5FR
  GRRBlueprintV4 GRRBlueprintV4.CIIASM GRRBlueprintV4.RG7
  SchemeNormalCone.AlgebraicGeometry
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalCompletion
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityExceptionalGlobal
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal


-- @@ L616-616 verbatim
section XVersion


-- @@ L618-623 verbatim
variable {k : Type u} [Field k] [Infinite k] {A : Scheme.{u}} [A.Over (Spk k)]
  [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A] [IsIntegral A]
  {X : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i] [X.Over (Spk k)]
  [LocallyOfFiniteType (X ↘ Spk k)] [IsNoetherian X]
  [Fact (D28.ProjectiveIntegral k X)] [i.IsOver (Spk k)]
  (hA : ProjectiveIntegralK k A) {r : ℕ} (C : G2C.RegularCover i.ker r) (φk : k →+* Γ(A, ⊤))


-- @@ L625-712 verbatim
include hA C in
/-- **The pencil geometry over an lci `X`** (copy of `RG7.concreteGeomXA`; the exceptional
component is built from the regular cover `C`, no regularity of `X`). -/
def concreteGeomXA_lci : PencilGeom k := by
  haveI hXi : IsIntegral X := (Fact.out : D28.ProjectiveIntegral k X).1
  haveI hZi : IsIntegral i.ker.subscheme := integralZA i
  haveI hAn : IsNoetherian A := inferInstance
  have hZK := KG2B.projectiveIntegralK_Z i.ker hA
  letI hZo := KG2B.zOver (k := k) i.ker
  haveI hZl := z_lft (k := k) i.ker
  haveI hZn := z_noeth i.ker
  haveI hNe : Nonempty A := KG2B.nonempty_A hA
  letI hMo := totalOver (k := k) i.ker
  haveI hMl := total_lft (k := k) i.ker hA
  haveI hMn := total_isNoetherian (k := k) i.ker hA
  have hMK : ProjectiveIntegralK k (totalGlobal A i.ker) :=
    projectiveIntegralK_total (k := k) i.ker hA
  letI hEo := componentOver (k := k) i.ker
  haveI hEl := component_lft i.ker C.toQuasiregular hZK
  haveI hEn := component_isNoetherian i.ker C.toQuasiregular hZK
  have hEK := G2C1.projectiveIntegralK_EC i.ker C.toQuasiregular hA
  have hXover : (phiXA i).inv ≫ (X ↘ Spk k) = (i.ker.subscheme ↘ Spk k) := by
    rw [← phiXA_over i, Iso.inv_hom_id_assoc]
  haveI hXP : IsProper (X ↘ Spk k) := by
    have e : X ↘ Spk k = i ≫ (A ↘ Spk k) := (CategoryTheory.comp_over (f := i) (S := Spk k)).symm
    rw [e]
    haveI : IsProper (A ↘ Spk k) := isProper_of_K hA
    infer_instance
  haveI : IsProper (totalGlobalToBase A i.ker ≫ (A ↘ Spk k)) :=
    isProper_of_K hMK
  haveI : IsProper (componentToCentre A i.ker ≫ (i.ker.subscheme ↘ Spk k)) :=
    isProper_of_K hEK
  haveI : IsProper (i.ker.subscheme ↘ Spk k) := isProper_of_K hZK
  haveI : IsProper (A ↘ Spk k) := isProper_of_K hA
  haveI hqP : IsProper (totalGlobalToBase A i.ker) :=
    IsProper.of_comp (totalGlobalToBase A i.ker) (A ↘ Spk k)
  haveI hπZP : IsProper (componentToCentre A i.ker) :=
    IsProper.of_comp (componentToCentre A i.ker) (i.ker.subscheme ↘ Spk k)
  haveI hπP : IsProper (componentToCentre A i.ker ≫ (phiXA i).inv) := inferInstance
  exact
    { A := A
      Z := X
      M := totalGlobal A i.ker
      E := component A i.ker
      overA := inferInstance
      overZ := inferInstance
      overM := hMo
      overE := hEo
      lftA := inferInstance
      lftZ := inferInstance
      lftM := hMl
      lftE := hEl
      noethA := hAn
      noethZ := inferInstance
      noethM := hMn
      noethE := hEn
      factA := ⟨projectiveIntegral_of_K hA⟩
      factZ := inferInstance
      factM := ⟨projectiveIntegral_of_K hMK⟩
      factE := ⟨projectiveIntegral_of_K hEK⟩
      i := i
      j := fibreιGlobal A i.ker k φk 1
      e := componentToTotal A i.ker
      q := totalGlobalToBase A i.ker
      π := componentToCentre A i.ker ≫ (phiXA i).inv
      s := (phiXA i).hom ≫ RG7.zeroE i.ker φk
      i_ci := inferInstance
      j_ci := inferInstance
      e_ci := inferInstance
      s_ci := by infer_instance
      q_proper := hqP
      π_proper := hπP
      i_over := inferInstance
      j_over := fibre_isOver' (k := k) i.ker φk 1
      e_over := component_isOver' (k := k) i.ker
      q_over := ⟨rfl⟩
      π_over := ⟨by
        change (componentToCentre A i.ker ≫ (phiXA i).inv) ≫ (X ↘ Spk k) =
          componentToCentre A i.ker ≫ (i.ker.subscheme ↘ Spk k)
        rw [Category.assoc, hXover]⟩
      qj := fibreιGlobal_toBase _ _ _ _ _
      qe := by
        have h1 : (phiXA i).inv ≫ i = i.ker.subschemeι := by
          rw [Iso.inv_comp_eq]; exact (phiXA_comp i).symm
        rw [componentToTotal_toBase, Category.assoc, h1]
      sπ := by
        rw [Category.assoc, ← Category.assoc (RG7.zeroE i.ker φk), RG7.zeroE_comp_centre,
          Category.id_comp, Iso.hom_inv_id] }


-- @@ L714-717 verbatim
include hA C in
/-- **The lci lift** `liftLci : K₀ X →+ K₀ M`, `x ↦ ℓ(φ⁻¹^* x)` with `φ : X ≅ V(ker i)`. -/
def liftLci : K0 X →+ K0 (totalGlobal A i.ker) :=
  (liftZ i.ker hA C).comp (pullbackK0 (phiXA i).inv)


-- @@ L719-720 verbatim
theorem liftLci_apply (x : K0 X) :
    liftLci i hA C x = liftZ i.ker hA C (pullbackK0 (phiXA i).inv x) := rfl


-- @@ L722-722 verbatim
attribute [local instance] integralZA


-- @@ L724-731 verbatim
/-- `G₀` image of the lift: `[ℓ x] = F_* pr^* φ⁻¹^* [x]` (the old `liftK'_spec`). -/
theorem k0ToG0_liftLci (x : K0 X) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total i.ker hA
    k0ToG0 (totalGlobal A i.ker) (liftLci i hA C x) =
      finitePushforward (subschemeTotalGlobalι A i.ker)
        (flatPullbackG0 (totalToClosedBase A i.ker)
          (k0ToG0 i.ker.subscheme (pullbackK0 (phiXA i).inv x))) :=
  k0ToG0_liftZ i.ker hA C _


-- @@ L733-744 verbatim
/-- **HbcA** for the lci lift. -/
theorem hbcA_lci [IsIntegral X] (x : K0 X) :
    k0ToG0 A (pullbackK0 (fibreιGlobal A i.ker k φk 1) (liftLci i hA C x)) =
      finitePushforward i (k0ToG0 X x) := by
  haveI : IsLocallyNoetherian i.ker.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i.ker.subschemeι
  rw [liftLci_apply, hbcA_liftZ i.ker hA C φk, k0ToG0_phiXA]
  calc finitePushforward i.ker.subschemeι (finitePushforward (phiXA i).hom (k0ToG0 X x))
      = finitePushforward ((phiXA i).hom ≫ i.ker.subschemeι) (k0ToG0 X x) := by
        rw [ARRG45C.finitePushforward_comp]; rfl
    _ = finitePushforward i (k0ToG0 X x) := by
        rw [ARRG45C.finitePushforward_congr (phiXA_comp i)]


-- @@ L746-760 verbatim
/-- **HbcE** (`G₀`) for the lci lift. -/
theorem hbcE_lci [IsIntegral X] (x : K0 X) :
    haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total i.ker hA
    haveI : IsLocallyNoetherian (component A i.ker) :=
      LocallyOfFiniteType.isLocallyNoetherian (componentToTotal A i.ker)
    k0ToG0 (component A i.ker) (pullbackK0 (componentToTotal A i.ker) (liftLci i hA C x)) =
      finitePushforward ((phiXA i).hom ≫ RG7.zeroE i.ker φk) (k0ToG0 X x) := by
  haveI := BundleCoversProjBundleG2.isLocallyNoetherian_total i.ker hA
  haveI : IsLocallyNoetherian (component A i.ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (componentToTotal A i.ker)
  haveI : IsLocallyNoetherian i.ker.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i.ker.subschemeι
  rw [liftLci_apply, hbcE_component_liftZ i.ker hA C φk, k0ToG0_phiXA,
    ARRG45C.finitePushforward_comp]
  rfl


-- @@ L762-785 verbatim
include hA C in
/-- **The K-datum of route A' over an lci `X`** (`FibreRel`, lift, `HbcA`, `HbcE`, injectivity on
the regular ambient `A`).  No regularity of `X`, `M` or `E`. -/
def concretePencilK_lci (hAreg : BlowupRegularAR12.IsRegularScheme A) :
    PencilK (concreteGeomXA_lci i hA C φk) :=
  haveI : IsIntegral X := (Fact.out : D28.ProjectiveIntegral k X).1
  haveI : IsNoetherian (totalGlobal A i.ker) := total_isNoetherian (k := k) i.ker hA
  haveI : IsIntegral (totalGlobal A i.ker) :=
    SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.IntegralARRM346.isIntegral_totalGlobal
      A i.ker
  haveI : IsIntegral (concreteGeomXA_lci i hA C φk).M :=
    SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.IntegralARRM346.isIntegral_totalGlobal
      A i.ker
  haveI : IsIntegral i.ker.subscheme := integralZA i
  haveI : Fact (ProjectiveIntegral k A) := ⟨projectiveIntegral_of_K hA⟩
  let h := fibreRel_cover i.ker hA C.toQuasiregular φk 1
  { LP := LPof h.choose h.choose_spec.choose
    hLP := hasConstantRank_LPof h.choose_spec.choose_spec.choose
      h.choose_spec.choose_spec.choose_spec.choose
    lift := liftLci i hA C
    fibreRel := h.choose_spec.choose_spec.choose_spec.choose_spec
    hbcA := hbcA_lci i hA C φk
    hbcE := hbcE_lci i hA C φk
    injA := injA_ambient (A := A) hA hAreg }


-- @@ L787-788 verbatim
theorem concretePencilK_lci_lift (hAreg : BlowupRegularAR12.IsRegularScheme A) :
    (concretePencilK_lci i hA C φk hAreg).lift = liftLci i hA C := rfl


-- @@ L790-795 verbatim
include hA C in
/-- The Koszul class `κ ∈ K₀ E` of the lci pencil (`= s_!(1)` transported along `S_σ ≅ E`). -/
def kosE_lci : K0 (component A i.ker) :=
  haveI : IsIntegral X := (Fact.out : D28.ProjectiveIntegral k X).1
  haveI : IsIntegral i.ker.subscheme := integralZA i
  kosEZ i.ker hA C φk


-- @@ L797-803 verbatim
/-- **`K₀`-level HbcE** (replaces `injE`/`zsClassP`): `e^* ℓ(x) = π^* x · κ` in `K₀ E`. -/
theorem hbcE_K0 (x : K0 X) :
    pullbackK0 (componentToTotal A i.ker) (liftLci i hA C x) =
      pullbackK0 (componentToCentre A i.ker ≫ (phiXA i).inv) x * kosE_lci i hA C φk := by
  haveI : IsIntegral X := (Fact.out : D28.ProjectiveIntegral k X).1
  rw [liftLci_apply, hbcE_K0_Z i.ker hA C φk, pullbackK0_comp_apply]
  rfl


-- @@ L805-810 verbatim
/-- `hbcE_K0` in the vocabulary of the pencil `P = concreteGeomXA_lci`, `K = concretePencilK_lci`. -/
theorem hbcE_K0_pencil (hAreg : BlowupRegularAR12.IsRegularScheme A) (x : K0 X) :
    pullbackK0 (concreteGeomXA_lci i hA C φk).e ((concretePencilK_lci i hA C φk hAreg).lift x) =
      pullbackK0 (concreteGeomXA_lci i hA C φk).π x *
        (show K0 (concreteGeomXA_lci i hA C φk).E from kosE_lci i hA C φk) :=
  hbcE_K0 i hA C φk x


-- @@ L812-812 verbatim
end XVersion


-- @@ L814-814 verbatim
end GRRBlueprintV4.G2CC2


-- @@ L816-816 verbatim
/-! ## E. Transport of Euler-class pushforwards along isomorphisms; the Koszul class of `E` -/


-- @@ L818-818 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L820-820 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory


-- @@ L822-822 verbatim
section IsoTransport


-- @@ L824-827 verbatim
variable {S₁ T₁ S₂ T₂ : Scheme.{u}} (ι₁ : S₁ ⟶ T₁) [IsClosedImmersion ι₁] (ι₂ : S₂ ⟶ T₂)
  [IsClosedImmersion ι₂] [IsLocallyNoetherian T₁] [IsLocallyNoetherian T₂]
  (h₁ : PerfectRepG2.Sch.HasBundleCovers T₁) (h₂ : PerfectRepG2.Sch.HasBundleCovers T₂)
  (θ : T₁ ⟶ T₂) [IsIso θ] (α : S₁ ⟶ S₂) [IsIso α]


-- @@ L829-841 verbatim
/-- `θ^* ι₂_* V ≅ ι₁_* α^* V` for isomorphisms `θ`, `α` with `ι₁ ≫ θ = α ≫ ι₂`. -/
def pushIsoTransport (w : ι₁ ≫ θ = α ≫ ι₂) (V : S₂.Modules) :
    (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pushforward ι₂).obj V) ≅
      (Scheme.Modules.pushforward ι₁).obj ((Scheme.Modules.pullback α).obj V) :=
  have hw' : ι₂ ≫ inv θ = inv α ≫ ι₁ := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  (ARRG45C.pullbackHomIsoPushforwardInv (asIso θ)).app _ ≪≫
    (Scheme.Modules.pushforwardComp ι₂ (inv θ)).app V ≪≫
    (Scheme.Modules.pushforwardCongr hw').app V ≪≫
    ((Scheme.Modules.pushforwardComp (inv α) ι₁).app V).symm ≪≫
    (Scheme.Modules.pushforward ι₁).mapIso
      ((ARRG45C.pullbackHomIsoPushforwardInv (asIso α)).app V).symm


-- @@ L843-863 verbatim
/-- **Naturality of `liftPush` under isomorphisms**: `ι₁!(α^* x) = θ^* ι₂!(x)`. -/
theorem liftPush_pullback_iso {d₁ d₂ : ℕ}
    (hpd₁ : ∀ V : S₁.Modules, IsFiniteLocallyFree S₁ V →
      PerfectRepG2.Sch.PdLE h₁ d₁ ((Scheme.Modules.pushforward ι₁).obj V))
    (hpd₂ : ∀ V : S₂.Modules, IsFiniteLocallyFree S₂ V →
      PerfectRepG2.Sch.PdLE h₂ d₂ ((Scheme.Modules.pushforward ι₂).obj V))
    (w : ι₁ ≫ θ = α ≫ ι₂) (x : K0 S₂) :
    ZeroSectionPushK0LCI.liftPush ι₁ h₁ d₁ hpd₁ (pullbackK0 α x) =
      pullbackK0 θ (ZeroSectionPushK0LCI.liftPush ι₂ h₂ d₂ hpd₂ x) := by
  refine ext_k0 ((ZeroSectionPushK0LCI.liftPush ι₁ h₁ d₁ hpd₁).comp (pullbackK0 α))
    ((pullbackK0 θ).comp (ZeroSectionPushK0LCI.liftPush ι₂ h₂ d₂ hpd₂)) (fun V hV => ?_) x
  change ZeroSectionPushK0LCI.liftPush ι₁ h₁ d₁ hpd₁ (pullbackK0 α (k0ClassOf S₂ V hV)) =
    pullbackK0 θ (ZeroSectionPushK0LCI.liftPush ι₂ h₂ d₂ hpd₂ (k0ClassOf S₂ V hV))
  rw [pullbackK0_classOf, ZeroSectionPushK0LCI.liftPush_k0ClassOf,
    ZeroSectionPushK0LCI.liftPush_k0ClassOf]
  have hc : IsCoherentLike T₂ ((Scheme.Modules.pushforward ι₂).obj V) :=
    (finitePushObject ι₂ ⟨V, hV.isFinitePresentation⟩).2
  rw [PerfectRepRestrictBG2.Sch.pullbackK0_repK0_of_flat h₁ h₂ θ _ hc (hpd₂ V hV)
    (PerfectRepRestrictBG2.Sch.isCoherentLike_pullback θ hc)
    (PerfectRepRestrictBG2.Sch.pdLE_pullback_of_flat h₁ h₂ θ hc (hpd₂ V hV))]
  exact (PerfectRepG2.Sch.repK0_iso h₁ (pushIsoTransport ι₁ ι₂ θ α w V) _ _ _ _).symm


-- @@ L865-865 verbatim
end IsoTransport


-- @@ L867-867 verbatim
end GRRBlueprintV4.G2CC2


-- @@ L869-869 verbatim
namespace GRRBlueprintV4.G2CC2


-- @@ L871-876 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order SchemeKTheory SchemeProjectiveSpace
  AlgebraicGeometry.Chow.M7 AlgebraicGeometry.Chow.M7.CIICLASS AlgebraicGeometry.Chow.M7.D28
  GRRBlueprintV4 GRRBlueprintV4.CIIASM GRRBlueprintV4.RG7
  SchemeNormalCone.AlgebraicGeometry
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation
  SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.InfinityExceptionalGlobal


-- @@ L878-878 verbatim
section XBridge


-- @@ L880-885 verbatim
variable {k : Type u} [Field k] [Infinite k] {A : Scheme.{u}} [A.Over (Spk k)]
  [LocallyOfFiniteType (A ↘ Spk k)] [IsNoetherian A] [IsIntegral A]
  {X : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i] [X.Over (Spk k)]
  [LocallyOfFiniteType (X ↘ Spk k)] [IsNoetherian X]
  [Fact (D28.ProjectiveIntegral k X)] [i.IsOver (Spk k)]
  (hA : ProjectiveIntegralK k A) {r : ℕ} (C : G2C.RegularCover i.ker r) (φk : k →+* Γ(A, ⊤))


-- @@ L887-923 verbatim
include hA C in
/-- **The Koszul class of the lci pencil is the transported `λ₋₁` of the tautological kernel**,
for any geometric model `M : E ≅ ℙ(N ⊞ 𝟙)` (`ZSModel`) of the exceptional divisor.  With the
landed bridge `λ₋₁(taut) = kosClassX` this is `kosE_lci = M.kosE`. -/
theorem kosE_lci_eq_lambda [IsIntegral X] {e : ℕ}
    (M : ZSModel (concreteGeomXA_lci i hA C φk).i (concreteGeomXA_lci i hA C φk).π
      (concreteGeomXA_lci i hA C φk).s e) :
    (show K0 (concreteGeomXA_lci i hA C φk).E from kosE_lci i hA C φk) =
      pullbackK0 M.φ.hom (lambdaMinusOne (RiemannRoch.KNFA.adaptedCover M.CN).tautologicalKernel
        ((RiemannRoch.KNFA.adaptedCover M.CN).hasConstantRank_tautologicalKernel M.hE)) := by
  haveI : IsNoetherian (RiemannRoch.KNFA.adaptedCover M.CN).scheme :=
    (RiemannRoch.KNFA.adaptedCover M.CN).isNoetherian_scheme
  have hP' : PerfectRepG2.Sch.HasBundleCovers (RiemannRoch.KNFA.adaptedCover M.CN).scheme :=
    BundleCoversProjBundleG2.hasBundleCovers_of_projEmb
      (AR11.ProjEmb.of_closedImmersion M.φ.inv (G2C1.projEmb_EC i.ker C.toQuasiregular hA))
  haveI := isLocallyNoetherian_sigma i.ker hA φk
  have hs : ((phiXA i).hom ≫ RG7.zeroE i.ker φk) ≫ M.φ.hom =
      (RiemannRoch.KNFA.adaptedCover M.CN).zeroSection := M.hφs
  have w : RG7.zeroSigma i.ker φk ≫ (RG7.psiSigma i.ker φk ≫ M.φ.hom) =
      (phiXA i).inv ≫ (RiemannRoch.KNFA.adaptedCover M.CN).zeroSection := by
    rw [← hs, Category.assoc, Iso.inv_hom_id_assoc, RG7.zeroE, Category.assoc]
  have key := liftPush_pullback_iso (RG7.zeroSigma i.ker φk)
    (RiemannRoch.KNFA.adaptedCover M.CN).zeroSection (hasBundleCovers_sigma i.ker hA φk) hP'
    (RG7.psiSigma i.ker φk ≫ M.φ.hom) (phiXA i).inv (pdLE_zeroSigma i.ker hA C φk)
    (ZeroSectionPushK0LCI.pdLE_zeroSection M.CN hP' M.hE) w 1
  rw [pullbackK0_one] at key
  have hz : ZeroSectionPushK0LCI.liftPush (RiemannRoch.KNFA.adaptedCover M.CN).zeroSection hP'
      ((e + 1) + 1) (ZeroSectionPushK0LCI.pdLE_zeroSection M.CN hP' M.hE) 1 =
      lambdaMinusOne (RiemannRoch.KNFA.adaptedCover M.CN).tautologicalKernel
        ((RiemannRoch.KNFA.adaptedCover M.CN).hasConstantRank_tautologicalKernel M.hE) :=
    ZeroSectionPushK0LCI.zsPush_one M.CN hP' M.hE
  rw [hz] at key
  change pullbackK0 (inv (RG7.psiSigma i.ker φk)) (zsSigma i.ker hA C φk 1) = _
  have hk : zsSigma i.ker hA C φk 1 = ZeroSectionPushK0LCI.liftPush (RG7.zeroSigma i.ker φk)
      (hasBundleCovers_sigma i.ker hA φk) r (pdLE_zeroSigma i.ker hA C φk) 1 := rfl
  rw [hk, key, pullbackK0_comp_apply, IsIso.inv_hom_id_assoc]
  rfl


-- @@ L925-936 verbatim
/-- **`zsClass` without `injE`** (the `K₀` input of the zero-section gate for C3): for a model `M`
and the landed bridge `λ₋₁(taut) = kosClassX`, `e^* ℓ(x) = π^* x · M.kosE`. -/
theorem hbcE_K0_kosE [IsIntegral X] (hAreg : BlowupRegularAR12.IsRegularScheme A) {e : ℕ}
    (M : ZSModel (concreteGeomXA_lci i hA C φk).i (concreteGeomXA_lci i hA C φk).π
      (concreteGeomXA_lci i hA C φk).s e)
    (bridge : lambdaMinusOne (RiemannRoch.KNFA.adaptedCover M.CN).tautologicalKernel
      ((RiemannRoch.KNFA.adaptedCover M.CN).hasConstantRank_tautologicalKernel M.hE) =
      GRRBlueprintV4.CIIL1E.kosClassX M.CX M.hN) (x : K0 X) :
    pullbackK0 (concreteGeomXA_lci i hA C φk).e ((concretePencilK_lci i hA C φk hAreg).lift x) =
      pullbackK0 (concreteGeomXA_lci i hA C φk).π x * M.kosE := by
  rw [hbcE_K0_pencil, kosE_lci_eq_lambda i hA C φk M, bridge]
  rfl


-- @@ L938-938 verbatim
end XBridge


-- @@ L940-940 verbatim
end GRRBlueprintV4.G2CC2
