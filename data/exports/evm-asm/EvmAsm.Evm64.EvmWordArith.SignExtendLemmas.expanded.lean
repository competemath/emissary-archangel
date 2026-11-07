module

public import EvmAsm.Rv64.Instructions


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
namespace EvmAsm.Evm64


-- @@ L9-9 verbatim
open EvmAsm.Rv64


-- @@ L11-14 verbatim
/-- Sign-extending the 12-bit immediate `4095` produces the all-ones word. -/
theorem signExtend12_4095_toNat :
    (signExtend12 (4095 : BitVec 12) : Word).toNat = 2^64 - 1 := by
  decide


-- @@ L16-16 verbatim
end EvmAsm.Evm64
