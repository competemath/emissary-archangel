import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ArtinL_LSeriesSummable_coeff_of_one_lt_re


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
open scoped MatrixGroups


-- @@ L11-11 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L13-15 verbatim
theorem ArtinL.LSeriesSummable_coeff_of_one_lt_re {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.coeff ρ) s := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_LSeriesSummable_coeff_of_one_lt_re.solution
