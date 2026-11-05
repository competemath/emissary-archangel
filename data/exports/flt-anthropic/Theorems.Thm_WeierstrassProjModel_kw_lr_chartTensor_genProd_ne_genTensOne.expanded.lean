import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne


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

-- @@ L20-23 expanded
theorem WeierstrassProjModel.kw_lr_chartTensor_genProd_ne_genTensOne [IsDomain R]
    [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    ∃ k : Fin 3,
      (kw_lrChart_gen W i j :
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X i : MvPolynomial (Fin 3) R)))) ⊗ₜ[R]
          (kw_lrChart_gen W j k :
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R)))) ≠
        (kw_lrChart_gen W i k) ⊗ₜ[R]
          (1 :
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R)))) :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genProd_ne_genTensOne.solution

