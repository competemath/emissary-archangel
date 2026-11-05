import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_pcmpin_outerCompat_genericPoint_agree


-- @@ L7-7 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L8-8 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L9-9 verbatim
open scoped TensorProduct


-- @@ L11-11 verbatim
universe u


-- @@ L13-13 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L14-14 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L16-16 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L18-21 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L22-41 expanded
theorem WeierstrassProjModel.kw_pcmpin_outerCompat_genericPoint_agree [IsDomain R]
    [IsNoetherianRing R] [W.IsElliptic]
    (pcm :
      ∀ (i j : Fin 3),
        Spec
            (CommRingCat.of
              ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X j : MvPolynomial (Fin 3) R))))) ⟶
          projModelCR W.toProjective)
    (hpin :
      ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
        kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij ij' : Fin 3 × Fin 3)
    [IsIntegral
        ↑(pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
            ((kwProjPullbackOpenCoverCR R W.toProjective).f ij'))] :
    (pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
              ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')).fromSpecStalk
          (genericPoint _) ≫
        pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
            ((kwProjPullbackOpenCoverCR R W.toProjective).f ij') ≫
          (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2 =
      (pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
              ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')).fromSpecStalk
          (genericPoint _) ≫
        pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
            ((kwProjPullbackOpenCoverCR R W.toProjective).f ij') ≫
          (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom ≫ pcm ij'.1 ij'.2 :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_pcmpin_outerCompat_genericPoint_agree.solution

