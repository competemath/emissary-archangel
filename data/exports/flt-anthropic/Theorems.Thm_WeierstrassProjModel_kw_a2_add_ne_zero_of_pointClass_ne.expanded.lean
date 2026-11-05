import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_add_ne_zero_of_pointClass_ne


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

-- @@ L23-29 verbatim
theorem WeierstrassProjModel.kw_a2_add_ne_zero_of_pointClass_ne
    (hΔ : algebraMap R F W.Δ ≠ 0) (P Q : Fin 3 → F)
    (hP : (kw_lrApt_WF W F).Equation P) (hQ : (kw_lrApt_WF W F).Equation Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hne : (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) ≠ ⟦Q⟧) :
    (kw_lrApt_WF W F).addX P Q ≠ 0 ∨ (kw_lrApt_WF W F).addY P Q ≠ 0
      ∨ (kw_lrApt_WF W F).addZ P Q ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_add_ne_zero_of_pointClass_ne.solution
