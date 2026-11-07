/-
  EvmAsm.Evm64.SDiv.Compose.SignFrame

  Small named assertion for the SDIV wrapper-private sign frame that is carried
  across the unsigned DIV callable.
-/

module

public import EvmAsm.Rv64.SepLogic


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64.SDiv.Compose


-- @@ L16-19 verbatim
/-- SDIV wrapper-private sign frame preserved across the unsigned DIV callable. -/
def sdivDivCallSignFrame (vRa resultSign divisorSign : Word) : EvmAsm.Rv64.Assertion :=
  (.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
  (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))


-- @@ L21-26 verbatim
theorem sdivDivCallSignFrame_unfold
    {vRa resultSign divisorSign : Word} :
    sdivDivCallSignFrame vRa resultSign divisorSign =
      ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
       (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) := by
  rfl


-- @@ L28-28 verbatim
end EvmAsm.Evm64.SDiv.Compose
