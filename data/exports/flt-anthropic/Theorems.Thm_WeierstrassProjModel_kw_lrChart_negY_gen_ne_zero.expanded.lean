import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero


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

-- @@ L20-24 expanded
theorem WeierstrassProjModel.kw_lrChart_negY_gen_ne_zero [IsDomain R] [W.IsElliptic] :
    (2 :
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X (2 : Fin 3) : MvPolynomial (Fin 3) R)))) *
            kw_lrChart_gen W 2 1 +
          (algebraMap R
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X (2 : Fin 3) : MvPolynomial (Fin 3) R)))
              W.a₁) *
            kw_lrChart_gen W 2 0 +
        algebraMap R
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X (2 : Fin 3) : MvPolynomial (Fin 3) R)))
          W.a₃ ≠
      0 :=
  by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero.solution

