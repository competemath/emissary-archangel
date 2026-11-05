import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over


-- @@ L5-5 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L6-6 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L7-7 verbatim
open scoped TensorProduct


-- @@ L9-9 verbatim
universe u


-- @@ L11-11 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L12-12 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L14-14 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L16-19 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L20-26 expanded
theorem WeierstrassProjModel.kw_pcmpin_chartIso_inv_cover_fst_over (ij : Fin 3 × Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).inv ≫
        (kwProjPullbackOpenCoverCR R W.toProjective).f ij ≫
          pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫
            projModelStrCR W.toProjective =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap R
            ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X ij.1 : MvPolynomial (Fin 3) R))) ⊗[R]
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X ij.2 : MvPolynomial (Fin 3) R)))))) :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over.solution

