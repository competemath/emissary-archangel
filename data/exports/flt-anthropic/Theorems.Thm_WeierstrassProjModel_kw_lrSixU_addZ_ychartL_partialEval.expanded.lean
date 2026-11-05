import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval


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

-- @@ L20-22 expanded
theorem WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval (j : Fin 3) :
    ∃ (φ :
      ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X 1 : MvPolynomial (Fin 3) R))) ⊗[R]
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X j : MvPolynomial (Fin 3) R)))) →+*
        (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X j : MvPolynomial (Fin 3) R)))),
      φ (kw_lrSixU W 1 j (.inl 2)) = -(kw_lrChart_gen W j 2) ^ 2 :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval.solution

