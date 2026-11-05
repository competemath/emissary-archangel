import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_evalAtJGen_injective

-- @@ L5-5 verbatim
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

-- @@ L6-6 verbatim
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single


-- @@ L8-8 verbatim
open ModularCurve IntermediateField

-- @@ L9-10 verbatim
theorem ModularCurve.evalAtJGen_injective :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_evalAtJGen_injective.solution
