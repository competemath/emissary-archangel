/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.CharacteristicClasses.ChowCaseIILciPencilG2C


-- @@ L8-24 verbatim
/-!
# REG remainder (c2): Tor-independence of `F_* pr^* F₀` for a coherent `F₀` (G2TREG3, part 2)

Setting of G2CC2's `restrictPushIso`: a section `σ` of a line `L` on `Y`, a finite `F : W ⟶ Y`,
a flat `pr : W ⟶ Z`, with `W ×_Y V(σ) ≅ Z` via `η ≫ pr`.  G2CC2 proves that the Koszul map
`σ : L⁻¹ ⊗ N ⟶ N` is a monomorphism for `N = F_* pr^* E₀`, `E₀` a **bundle**.  Here:

* `mono_app_of_ses` (abstract, refinements): for `0 → K → E → Q → 0` and a natural `σ : T ⟶ 𝟭`
  (`T` additive, `T(E ⟶ Q)` epi), if `σ_E` is mono and `coker σ_K ⟶ coker σ_E` is mono, then
  `σ_Q` is mono (snake lemma, "`Tor₁` vanishing");
* `mono_cokernel_map_pr`: the map `coker σ_{pr^*K} ⟶ coker σ_{pr^*E}` is `η_* η^*` of
  `pr^* K ⟶ pr^* E` up to the unit isomorphisms, and `η^* pr^* ≅ (η ≫ pr)^*` with `η ≫ pr` an
  isomorphism, so it is mono for every mono `K ⟶ E`;
* `mono_ap_pullback_coherent`, `mono_ap_pushforward_coherent`: **the Koszul map is a
  monomorphism on `pr^* F₀` and on `F_* pr^* F₀` for every coherent `F₀`**, when `Z` has bundle
  covers (a bundle `E ↠ F₀`).
-/


-- @@ L26-26 verbatim
set_option autoImplicit false

-- @@ L27-27 verbatim
set_option linter.unusedSectionVars false


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L35-35 verbatim
namespace AlgebraicGeometry.SingTau.RegularComparison.Generic


-- @@ L37-37 verbatim
/-! ### The abstract chase -/


-- @@ L39-39 verbatim
section Abstract


-- @@ L41-41 verbatim
variable {C : Type*} [Category C] [Abelian C] (T : C ⥤ C)


-- @@ L43-69 verbatim
/-- **`Tor₁` vanishing by the snake lemma (refinement form)**, with explicit components
`aᵢ : T Sᵢ ⟶ Sᵢ` of a natural map. -/
theorem mono_of_ses [T.PreservesZeroMorphisms] (S : ShortComplex C) (hS : S.ShortExact)
    [Epi (T.map S.g)]
    (a₁ : T.obj S.X₁ ⟶ S.X₁) (a₂ : T.obj S.X₂ ⟶ S.X₂) (a₃ : T.obj S.X₃ ⟶ S.X₃)
    (h₁ : T.map S.f ≫ a₂ = a₁ ≫ S.f) (h₂ : T.map S.g ≫ a₃ = a₂ ≫ S.g) [Mono a₂]
    (hφ : Mono (cokernel.map a₁ a₂ (T.map S.f) S.f h₁.symm)) : Mono a₃ := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi (T.map S.g) x
  have hy0 : (y ≫ a₂) ≫ S.g = 0 := by
    rw [Category.assoc, ← h₂, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, z, hz⟩ := hS.exact.exact_up_to_refinements _ hy0
  have hz0 : z ≫ cokernel.π a₁ = 0 := by
    rw [← cancel_mono (cokernel.map a₁ a₂ (T.map S.f) S.f h₁.symm), Category.assoc,
      cokernel.π_desc, zero_comp, ← Category.assoc, ← hz, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  obtain ⟨A₃, π₃, hπ₃, w, hw⟩ :=
    (ShortComplex.exact_cokernel a₁).exact_up_to_refinements z hz0
  have hw' : w ≫ T.map S.f = π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono a₂, Category.assoc, h₁, ← Category.assoc]
    rw [← hw, Category.assoc, ← hz, Category.assoc, Category.assoc]
  have hfin : π₃ ≫ π₂ ≫ π₁ ≫ x = 0 := by
    calc π₃ ≫ π₂ ≫ π₁ ≫ x = (π₃ ≫ π₂ ≫ y) ≫ T.map S.g := by
          rw [hy]; simp only [Category.assoc]
      _ = 0 := by rw [← hw', Category.assoc, ← T.map_comp, S.zero, T.map_zero, comp_zero]
  rw [← cancel_epi π₁, ← cancel_epi π₂, ← cancel_epi π₃, hfin, comp_zero, comp_zero, comp_zero]


-- @@ L71-71 verbatim
end Abstract



-- @@ L74-74 verbatim
/-! ### The Cartier divisor `V(σ)`: Koszul maps on `pr^* F₀` and `F_* pr^* F₀` -/


-- @@ L76-76 verbatim
section CartierMono


-- @@ L78-78 verbatim
open SchemeKTheory KSpecialization KSpecialization.AR7R KSpecialization.AR4 KSpecialization.AR8

-- @@ L79-79 verbatim
open ExactGrothendieck.CartierGysinAR1 ExactGrothendieck.CartierGysinAR8

-- @@ L80-80 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7


-- @@ L82-85 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)
  {W Z : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
  (F : W ⟶ Y) [IsFinite F] (pr : W ⟶ Z) [Flat pr]


-- @@ L87-88 verbatim
set_option quotPrecheck false in
local notation "ηΣ" => pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L89-90 verbatim
set_option quotPrecheck false in
local notation "TΣ" => tensorSheafLeftFunctor Y (lineBundleDual Y L)

-- @@ L91-92 verbatim
set_option quotPrecheck false in
local notation "sΣ" => sigmaT (lineBundleDual Y L) (dualEval σ)

-- @@ L93-94 verbatim
set_option quotPrecheck false in
local notation "TW" => tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L))

-- @@ L95-96 verbatim
set_option quotPrecheck false in
local notation "sW" => sigmaT _ (pullbackSection F (dualEval σ))


-- @@ L98-101 verbatim
/-- Naturality of the Koszul map on `W`. -/
theorem ap_naturality_g2treg3 {A B : W.Modules} (f : A ⟶ B) :
    (TW).map f ≫ ap TW sW B = ap TW sW A ≫ f :=
  (sW).naturality f


-- @@ L103-113 verbatim
/-- `η^*` of `pr^*` of a monomorphism is a monomorphism when `η ≫ pr` is an isomorphism. -/
theorem mono_pullback_eta_pr [IsIso (ηΣ ≫ pr)] {K E : Z.Modules} (k : K ⟶ E) [Mono k] :
    Mono ((Scheme.Modules.pullback ηΣ).map ((Scheme.Modules.pullback pr).map k)) := by
  haveI : (Scheme.Modules.pushforward (inv (ηΣ ≫ pr))).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (inv (ηΣ ≫ pr))).isRightAdjoint
  haveI h1 : (Scheme.Modules.pullback (ηΣ ≫ pr)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms.of_iso
      (ARRG45C.pullbackHomIsoPushforwardInv (asIso (ηΣ ≫ pr))).symm
  haveI : (Scheme.Modules.pullback pr ⋙ Scheme.Modules.pullback ηΣ).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms.of_iso (Scheme.Modules.pullbackComp ηΣ pr).symm
  exact (Scheme.Modules.pullback pr ⋙ Scheme.Modules.pullback ηΣ).map_mono k


-- @@ L115-161 verbatim
/-- **The cokernel comparison** `coker σ_{pr^*K} ⟶ coker σ_{pr^*E}` is a monomorphism for every
monomorphism `K ⟶ E` of coherent sheaves (`W ∩ V(σ) ≅ Z` is Tor-independent of `pr^*`). -/
theorem mono_cokernel_map_pr (hL : HasConstantRank Y L 1) [IsIso (ηΣ ≫ pr)]
    {K E : Z.Modules} (k : K ⟶ E) [Mono k] (hK : IsCoherentLike Z K) :
    Mono (cokernel.map (ap TW sW ((Scheme.Modules.pullback pr).obj K))
      (ap TW sW ((Scheme.Modules.pullback pr).obj E)) ((TW).map ((Scheme.Modules.pullback pr).map k))
      ((Scheme.Modules.pullback pr).map k) (ap_naturality_g2treg3 σ F _).symm) := by
  letI : K.IsFinitePresentation := hK
  have hV : IsCoherentLike W ((Scheme.Modules.pullback pr).obj K) :=
    pullback_isFinitePresentation_global pr K
  set φ := cokernel.map (ap TW sW ((Scheme.Modules.pullback pr).obj K))
      (ap TW sW ((Scheme.Modules.pullback pr).obj E)) ((TW).map ((Scheme.Modules.pullback pr).map k))
      ((Scheme.Modules.pullback pr).map k) (ap_naturality_g2treg3 σ F _).symm with hφdef
  let adj := Scheme.Modules.pullbackPushforwardAdjunction ηΣ
  haveI hu : IsIso (adj.unit.app (cokernel (ap TW sW ((Scheme.Modules.pullback pr).obj K)))) :=
    KSpecialization.ARRHU.hunit_ARRHU σ hL F _ hV
  haveI hK' := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL ((Scheme.Modules.pullback pr).obj K)
  haveI hE' := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL ((Scheme.Modules.pullback pr).obj E)
  haveI hm := mono_pullback_eta_pr σ F pr k
  have hsq : (Scheme.Modules.pullback ηΣ).map
        (cokernel.π (ap TW sW ((Scheme.Modules.pullback pr).obj K))) ≫
      (Scheme.Modules.pullback ηΣ).map φ =
      (Scheme.Modules.pullback ηΣ).map ((Scheme.Modules.pullback pr).map k) ≫
        (Scheme.Modules.pullback ηΣ).map
          (cokernel.π (ap TW sW ((Scheme.Modules.pullback pr).obj E))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hφdef, cokernel.π_desc]
  haveI hpm : Mono ((Scheme.Modules.pullback ηΣ).map φ) := by
    have : (Scheme.Modules.pullback ηΣ).map φ =
        inv ((Scheme.Modules.pullback ηΣ).map
          (cokernel.π (ap TW sW ((Scheme.Modules.pullback pr).obj K)))) ≫
        (Scheme.Modules.pullback ηΣ).map ((Scheme.Modules.pullback pr).map k) ≫
          (Scheme.Modules.pullback ηΣ).map
            (cokernel.π (ap TW sW ((Scheme.Modules.pullback pr).obj E))) := by
      rw [IsIso.eq_inv_comp, hsq]
    rw [this]
    infer_instance
  haveI : (Scheme.Modules.pushforward ηΣ).IsRightAdjoint := adj.isRightAdjoint
  have hnat : φ ≫ adj.unit.app (cokernel (ap TW sW ((Scheme.Modules.pullback pr).obj E))) =
      adj.unit.app (cokernel (ap TW sW ((Scheme.Modules.pullback pr).obj K))) ≫
        (Scheme.Modules.pushforward ηΣ).map ((Scheme.Modules.pullback ηΣ).map φ) :=
    adj.unit.naturality φ
  have hpush : Mono ((Scheme.Modules.pushforward ηΣ).map ((Scheme.Modules.pullback ηΣ).map φ)) :=
    Functor.map_mono _ _
  have h2 : Mono (φ ≫ adj.unit.app (cokernel (ap TW sW ((Scheme.Modules.pullback pr).obj E)))) := by
    rw [hnat]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hu) _ hpush
  exact @mono_of_mono _ _ _ _ _ _ _ h2


-- @@ L163-192 verbatim
/-- **The Koszul map on `pr^* F₀` is a monomorphism for every coherent `F₀`** (`Z` with bundle
covers; `σ_W` mono on bundles, i.e. `Mono (pullbackSection F (dualEval σ))`). -/
theorem mono_ap_pullback_coherent (hL : HasConstantRank Y L 1)
    [Mono (pullbackSection F (dualEval σ))] [IsIso (ηΣ ≫ pr)]
    (hcov : PerfectRepG2.Sch.HasBundleCovers Z) (F0 : Z.Modules) (hF0 : IsCoherentLike Z F0) :
    Mono (ap TW sW ((Scheme.Modules.pullback pr).obj F0)) := by
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛW1 := SchemeKTheory.hasConstantRank_pullback W F _ 1 hΛ1
  have hΛW : IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)) :=
    hΛW1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _ hΛW
  obtain ⟨E, hE, g, hg⟩ := hcov F0 hF0
  have hEc : IsCoherentLike Z E := hE.isFinitePresentation
  have hKc : IsCoherentLike Z (kernel g) :=
    (KSpecialization.kerCokerClosed_isCoherentLike).kernel g hEc hF0
  letI : F0.IsFinitePresentation := hF0
  letI : E.IsFinitePresentation := hEc
  letI : (kernel g).IsFinitePresentation := hKc
  let S : ShortComplex Z.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel g }
  have hS' := pullback_map_shortExact_global pr S hS
  haveI : Epi ((TW).map (S.map (Scheme.Modules.pullback pr)).g) := by
    haveI : Epi (S.map (Scheme.Modules.pullback pr)).g := hS'.epi_g
    infer_instance
  haveI : Mono (ap TW sW (S.map (Scheme.Modules.pullback pr)).X₂) :=
    CIIL3B.hMono_of_mono_pullbackSection σ F pr E hE
  exact mono_of_ses (TW) (S.map (Scheme.Modules.pullback pr)) hS' _ _ _
    (ap_naturality_g2treg3 σ F _) (ap_naturality_g2treg3 σ F _)
    (mono_cokernel_map_pr σ F pr hL (kernel.ι g) hKc)


-- @@ L194-213 verbatim
/-- **The Koszul map on `F_* pr^* F₀` is a monomorphism for every coherent `F₀`** — the gate
`hm` of REG2's `resolutionData_pullback_cartier` for `G = F_* pr^* F₀`. -/
theorem mono_ap_pushforward_coherent (hL : HasConstantRank Y L 1)
    [Mono (pullbackSection F (dualEval σ))] [IsIso (ηΣ ≫ pr)]
    (hcov : PerfectRepG2.Sch.HasBundleCovers Z) (F0 : Z.Modules) (hF0 : IsCoherentLike Z F0) :
    Mono (ap TΣ sΣ ((Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback pr).obj F0))) := by
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) := hΛ1.isFiniteLocallyFree
  have hΛW1 := SchemeKTheory.hasConstantRank_pullback W F _ 1 hΛ1
  have hΛW : IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)) :=
    hΛW1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ hΛW
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _ hΛW
  haveI := mono_ap_pullback_coherent σ F pr hL hcov F0 hF0
  haveI : (Scheme.Modules.pushforward F).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction F).isRightAdjoint
  rw [(pushCompat F (dualEval σ) hΛ).ap_eq]
  infer_instance


-- @@ L215-215 verbatim
end CartierMono


-- @@ L217-217 verbatim
end AlgebraicGeometry.SingTau.RegularComparison.Generic
