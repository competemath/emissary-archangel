import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.RingTheory.Localization.FractionRing
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne


-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L9-9 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L10-10 verbatim
open scoped TensorProduct


-- @@ L12-12 verbatim
universe u


-- @@ L14-14 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L15-15 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L17-17 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L19-22 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L23-35 expanded
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem WeierstrassProjModel.kw_lr_chartTensor_genericProj_pointClass_ne [IsDomain R]
    [IsNoetherianRing R] [W.IsElliptic] (i j : Fin 3) :
    haveI :
      IsDomain
        ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X i : MvPolynomial (Fin 3) R))) ⊗[R]
          (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (X j : MvPolynomial (Fin 3) R)))) :=
      isDomain_chartTensor_of_isElliptic W i j
    let ψᵢ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X i : MvPolynomial (Fin 3) R))) →ₐ[R]
        FractionRing
          ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X i : MvPolynomial (Fin 3) R))) ⊗[R]
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R)))) :=
      (IsScalarTower.toAlgHom R
            ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X i : MvPolynomial (Fin 3) R))) ⊗[R]
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X j : MvPolynomial (Fin 3) R))))
            (FractionRing
              ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X j : MvPolynomial (Fin 3) R)))))).comp
        Algebra.TensorProduct.includeLeft
    let ψⱼ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X j : MvPolynomial (Fin 3) R))) →ₐ[R]
        FractionRing
          ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X i : MvPolynomial (Fin 3) R))) ⊗[R]
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R)))) :=
      (IsScalarTower.toAlgHom R
            ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X i : MvPolynomial (Fin 3) R))) ⊗[R]
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X j : MvPolynomial (Fin 3) R))))
            (FractionRing
              ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X j : MvPolynomial (Fin 3) R)))))).comp
        Algebra.TensorProduct.includeRight
    (⟦kw_lrApt_chartEval W
            (FractionRing
              ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                    (X j : MvPolynomial (Fin 3) R)))))
            i ψᵢ⟧ :
        WeierstrassCurve.Projective.PointClass
          (FractionRing
            ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X i : MvPolynomial (Fin 3) R))) ⊗[R]
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X j : MvPolynomial (Fin 3) R)))))) ≠
      ⟦kw_lrApt_chartEval W
          (FractionRing
            ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X i : MvPolynomial (Fin 3) R))) ⊗[R]
              (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                  (X j : MvPolynomial (Fin 3) R)))))
          j ψⱼ⟧ :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_lr_chartTensor_genericProj_pointClass_ne.solution

