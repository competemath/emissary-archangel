import Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrThird_toE3_compat_of_isDomain


-- @@ L6-6 verbatim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

-- @@ L7-7 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L8-8 verbatim
open scoped TensorProduct


-- @@ L10-10 verbatim
universe u


-- @@ L12-12 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L13-13 verbatim
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra


-- @@ L15-15 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L17-20 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))


-- @@ L22-33 expanded
theorem WeierstrassProjModel.kw_lrThird_toE3_compat_of_isDomain [IsDomain R] [IsNoetherianRing R]
    [W.IsElliptic] (i j k : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    pullback.fst
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap
                ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                  (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X j : MvPolynomial (Fin 3) R))))
                (Localization.Away (kw_lrThird_u₃ W i j k)))))
          (kw_lrSixU_locMap W i j l) ≫
        kw_lrThird_toE₃ W i j k =
      pullback.snd
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap
                ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X i : MvPolynomial (Fin 3) R))) ⊗[R]
                  (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
                    (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                      (X j : MvPolynomial (Fin 3) R))))
                (Localization.Away (kw_lrThird_u₃ W i j k)))))
          (kw_lrSixU_locMap W i j l) ≫
        kw_lrSixU_toE W i j l :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_lrThird_toE3_compat_of_isDomain.solution

