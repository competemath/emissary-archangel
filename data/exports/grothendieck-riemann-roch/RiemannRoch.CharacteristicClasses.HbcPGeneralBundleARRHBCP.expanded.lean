/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.CharacteristicClasses.PencilEFibreCIIL3B


-- @@ L9-21 verbatim
/-!
# HbcE for an arbitrary vector bundle on `W` (route ARRHBCP)

`hbcE_pencil_fibre_bundle` (CIIL3B) treats the classes `pr^* E₀` pulled back from the base.  Here
the same Cartier-divisor Gysin base change is proved for **every** finite locally free `V` on `W`
(no `pr`, no flatness): for `σ` a regular section of a line bundle `L` on `Y` with
`Mono (F^*σ^∨)`, `F : W ⟶ Y` finite, `y ∈ K₀(Y)` with `[y] = F_*[V]` in `G₀(Y)`,

`[ι^* y] = (Fz)_* [η^* V]` in `G₀(V(σ))`, where `Wz = W ×_Y V(σ)`.

* `hbcE_general_bundle`: one bundle.
* `hbcE_general`: every `w ∈ K₀(W)` (given `K₀(Y) = G₀(Y)`).
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option linter.unusedSectionVars false


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-30 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory KSpecialization Opposite
  TopologicalSpace AlgebraicGeometry.Chow.M7.D23 AlgebraicGeometry.Chow.M7
  SchemeKTheory.LineBundleDual KSpecialization.AR7R ExactGrothendieck.CartierGysinAR1


-- @@ L32-32 verbatim
universe u


-- @@ L34-34 verbatim
namespace KSpecialization.ARRHBCP


-- @@ L36-36 verbatim
section General


-- @@ L38-41 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)
  {W : Scheme.{u}} [IsLocallyNoetherian W]
  (F : W ⟶ Y) [IsFinite F]


-- @@ L43-44 verbatim
set_option quotPrecheck false in
local notation "ιΣ" => (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L45-46 verbatim
set_option quotPrecheck false in
local notation "ηΣ" => pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L47-48 verbatim
set_option quotPrecheck false in
local notation "FzΣ" => pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι


-- @@ L50-108 verbatim
/-- **HbcE for one arbitrary vector bundle `V` on `W`.** -/
theorem hbcE_general_bundle (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    (hs : Mono (pullbackSection F (dualEval σ)))
    (V : W.Modules) (hV : IsFiniteLocallyFree W V) (y : K0 Y)
    (hy : k0ToG0 Y y = finitePushforward F (g0ClassOf W V hV.isFinitePresentation)) :
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme (pullbackK0 ιΣ y) =
      finitePushforward FzΣ
        (k0ToG0 (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
          (pullbackK0 ηΣ (k0ClassOf W V hV))) := by
  have hV₀ : IsCoherentLike W V := hV.isFinitePresentation
  letI : V.IsFinitePresentation := hV₀
  haveI : Mono (ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
      (sigmaT _ (pullbackSection F (dualEval σ))) V) :=
    CIIL3B.mono_sigmaT_app (pullbackSection F (dualEval σ)) _ hV
  haveI : IsLocallyNoetherian (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) :=
    LocallyOfFiniteType.isLocallyNoetherian ηΣ
  have hT := tensorSheaf_isCoherentLike W _ _
    (SchemeKTheory.hasConstantRank_pullback W F _ 1
      (lineBundleDual_hasConstantRank L hL)).isFiniteLocallyFree hV₀
  have hC : IsCoherentLike W (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V)) :=
    (kerCokerClosed_isCoherentLike (Y := W)).cokernel _ hT hV₀
  letI : (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V)).IsFinitePresentation := hC
  have hunit := KSpecialization.ARRHU.hunit_ARRHU σ hL F V hV₀
  have hG0 : IsCoherentLike (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
      ((Scheme.Modules.pullback ηΣ).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V))) :=
    pullback_isFinitePresentation_global ηΣ _
  have hG' := (finitePushObject FzΣ ⟨_, hG0⟩).2
  let e : (Scheme.Modules.pushforward ιΣ).obj ((Scheme.Modules.pushforward FzΣ).obj
      ((Scheme.Modules.pullback ηΣ).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V)))) ≅
      (Scheme.Modules.pushforward F).obj (cokernel (ap (tensorSheafLeftFunctor W
        ((Scheme.Modules.pullback F).obj (lineBundleDual Y L)))
        (sigmaT _ (pullbackSection F (dualEval σ))) V)) :=
    (Scheme.Modules.pushforwardComp FzΣ ιΣ).app _ ≪≫
      (Scheme.Modules.pushforwardCongr pullback.condition.symm).app _ ≪≫
      ((Scheme.Modules.pushforwardComp ηΣ F).app _).symm ≪≫
      (Scheme.Modules.pushforward F).mapIso (asIso (SchemeKTheory.ProjectionFormula.adjUnit ηΣ _)).symm
  have h := CIIL3B.hbc_cartier_closed σ hL hreg F _ hV₀ y hy _ hG' e
  rw [h]
  haveI := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL V
  have hV₂ : IsCoherentLike (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
      ((Scheme.Modules.pullback ηΣ).obj V) :=
    pullback_isFinitePresentation_global ηΣ _
  have hcls : g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hG0 =
      k0ToG0 (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
        (pullbackK0 ηΣ (k0ClassOf W V hV)) := by
    have h1 : g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hG0 =
        g0ClassOf (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) _ hV₂ :=
      g0ClassOf_iso _ _ _ (asIso ((Scheme.Modules.pullback ηΣ).map (cokernel.π _))).symm
    rw [h1, pullbackK0_classOf, k0ToG0_classOf]
  refine (finitePushforward_classOf FzΣ _ hG0).symm.trans ?_
  rw [hcls]



-- @@ L111-143 verbatim
/-- **HbcE for every class `w ∈ K₀(W)`**, assuming `K₀(Y) = G₀(Y)`: if `[y] = F_*[w]` then
`[ι^* y] = (Fz)_* [η^* w]`. -/
theorem hbcE_general (hL : HasConstantRank Y L 1) (hreg : SectionIsRegular σ)
    (hs : Mono (pullbackSection F (dualEval σ)))
    (hres : Function.Bijective (k0ToG0 Y)) (w : K0 W) (y : K0 Y)
    (hy : k0ToG0 Y y = finitePushforward F (k0ToG0 W w)) :
    k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme (pullbackK0 ιΣ y) =
      finitePushforward FzΣ
        (k0ToG0 (pullback F (sectionEvaluationIdealSheaf σ).subschemeι)
          (pullbackK0 ηΣ w)) := by
  haveI : IsLocallyNoetherian (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) :=
    LocallyOfFiniteType.isLocallyNoetherian ηΣ
  let Ψ : G0 Y ≃+ K0 Y := (AddEquiv.ofBijective (k0ToG0 Y) hres).symm
  have hΨ : ∀ g, k0ToG0 Y (Ψ g) = g := fun g =>
    (AddEquiv.ofBijective (k0ToG0 Y) hres).apply_symm_apply g
  let L' : K0 W →+ G0 (sectionEvaluationIdealSheaf σ).subscheme :=
    (k0ToG0 _).comp ((pullbackK0 ιΣ).comp (Ψ.toAddMonoidHom.comp ((finitePushforward F).comp
      (k0ToG0 W))))
  let R : K0 W →+ G0 (sectionEvaluationIdealSheaf σ).subscheme :=
    (finitePushforward FzΣ).comp ((k0ToG0 _).comp (pullbackK0 ηΣ))
  have hLR : L' = R := by
    apply ExactGrothendieck.hom_ext
    intro E
    change k0ToG0 _ (pullbackK0 ιΣ (Ψ (finitePushforward F (k0ToG0 W (k0ClassOf W E.1 E.2))))) =
      finitePushforward FzΣ (k0ToG0 _ (pullbackK0 ηΣ (k0ClassOf W E.1 E.2)))
    rw [k0ToG0_classOf]
    exact hbcE_general_bundle σ F hL hreg hs E.1 E.2 _ (by rw [hΨ])
  have hyΨ : y = Ψ (finitePushforward F (k0ToG0 W w)) := by
    rw [← hy]; exact ((AddEquiv.ofBijective (k0ToG0 Y) hres).symm_apply_apply y).symm
  have := DFunLike.congr_fun hLR w
  change k0ToG0 _ (pullbackK0 ιΣ (Ψ (finitePushforward F (k0ToG0 W w)))) =
    finitePushforward FzΣ (k0ToG0 _ (pullbackK0 ηΣ w)) at this
  rw [hyΨ]; exact this


-- @@ L145-145 verbatim
end General


-- @@ L147-147 verbatim
end KSpecialization.ARRHBCP
