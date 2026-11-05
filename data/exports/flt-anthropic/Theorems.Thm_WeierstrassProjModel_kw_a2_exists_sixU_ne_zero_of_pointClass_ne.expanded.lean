import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne


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

-- @@ L17-17 verbatim
variable (F : Type u) [Field F] [Algebra R F]


-- @@ L19-22 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L23-28 expanded
theorem WeierstrassProjModel.kw_a2_exists_sixU_ne_zero_of_pointClass_ne
    (hΔ : algebraMap R F W.Δ ≠ 0) (i j : Fin 3)
    (ψᵢ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X i : MvPolynomial (Fin 3) R))) →ₐ[R]
        F)
    (ψⱼ :
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (X j : MvPolynomial (Fin 3) R))) →ₐ[R]
        F)
    (hne :
      (⟦kw_lrApt_chartEval W F i ψᵢ⟧ : WeierstrassCurve.Projective.PointClass F) ≠
        ⟦kw_lrApt_chartEval W F j ψⱼ⟧) :
    ∃ l, (Algebra.TensorProduct.productMap ψᵢ ψⱼ) (kw_lrSixU W i j l) ≠ 0 := by
  p2m_exact_reverting
    @_root_.P2MW.S_WeierstrassProjModel_kw_a2_exists_sixU_ne_zero_of_pointClass_ne.solution

