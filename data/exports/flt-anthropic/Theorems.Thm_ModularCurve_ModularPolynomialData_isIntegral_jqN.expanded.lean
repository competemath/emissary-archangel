import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_isIntegral_jqN


-- @@ L5-5 verbatim
open ModularCurve IntermediateField

-- @@ L6-6 verbatim
theorem ModularCurve.ModularPolynomialData.isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN.solution
