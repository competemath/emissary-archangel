import Definitions.Def_WeierstrassCurve_ProjModel_ThirdLawCharts
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrThird_nineCoverage_of_isElliptic


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


-- @@ L22-25 expanded
theorem WeierstrassProjModel.kw_lrThird_nineCoverage_of_isElliptic [W.IsElliptic] (i j : Fin 3) :
    Ideal.span (Set.range (kw_lrSixU W i j) ∪ Set.range (kw_lrThird_u₃ W i j)) =
      (⊤ :
        Ideal
          ((HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X i : MvPolynomial (Fin 3) R))) ⊗[R]
            (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (X j : MvPolynomial (Fin 3) R))))) :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_lrThird_nineCoverage_of_isElliptic.solution

