import Mathlib
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt


-- @@ L9-9 verbatim
set_option autoImplicit false


-- @@ L11-11 verbatim
open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne

-- @@ L12-12 verbatim
open scoped MatrixGroups


-- @@ L14-14 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L16-25 expanded
theorem LanglandsTunnell.det_lift_eq_chiNegThree_of_isFrobeniusAt
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod 3))
    (hdet :
      ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : A.IsFrobeniusAt σ p) :
    ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).det =
      ((chiNegThree p : ℤ) : ℤ√(-2)) :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt.solution

