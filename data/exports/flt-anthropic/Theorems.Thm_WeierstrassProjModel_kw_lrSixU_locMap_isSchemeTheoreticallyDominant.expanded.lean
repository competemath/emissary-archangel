import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant


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

-- @@ L22-25 verbatim
theorem WeierstrassProjModel.kw_lrSixU_locMap_isSchemeTheoreticallyDominant
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) (hl : kw_lrSixU W i j l ≠ 0) :
    IsSchemeTheoreticallyDominant (kw_lrSixU_locMap W i j l) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant.solution
