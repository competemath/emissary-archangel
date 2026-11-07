/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree

  PC-free helpers for SMOD result-sign-fix postconditions.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ResultSignFixView


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.SMod.Compose


-- @@ L15-19 verbatim
theorem smodResultSignFixPost_smodResultSign_pcFree
    {sp dividendTop limb0 limb1 limb2 limb3 : Word} :
    (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      limb0 limb1 limb2 limb3).pcFree := by
  exact smodResultSignFixPost_pcFree


-- @@ L21-26 verbatim
instance pcFreeInst_smodResultSignFixPost_smodResultSign
    (sp dividendTop limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        limb0 limb1 limb2 limb3) :=
  ⟨smodResultSignFixPost_smodResultSign_pcFree⟩


-- @@ L28-32 verbatim
theorem smodResultSignFixPost_smodResultSign_zero_pcFree
    {sp dividendTop : Word} :
    (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      0 0 0 0).pcFree := by
  exact smodResultSignFixPost_smodResultSign_pcFree


-- @@ L34-39 verbatim
instance pcFreeInst_smodResultSignFixPost_smodResultSign_zero
    (sp dividendTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        0 0 0 0) :=
  ⟨smodResultSignFixPost_smodResultSign_zero_pcFree⟩


-- @@ L41-41 verbatim
end EvmAsm.Evm64.SMod.Compose
