/-
  EvmAsm.Codegen.Programs.EvmGasHandlers

  Dispatcher handler for the GAS opcode.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.GasOpcode.Program


-- @@ L10-10 verbatim
namespace EvmAsm.Codegen


-- @@ L12-23 verbatim
/-- M30: GAS (0x5a) pushes the dispatcher-maintained remaining gas
    (env+568, charged per-opcode by the dispatch loop). Mirrors the
    MSIZE handler — read the env cell, push it as a 256-bit word (low
    limb = remaining gas, high limbs 0). The loop charges GAS's own
    cost (BASE = 2) *before* this handler runs, so the pushed value
    already reflects it, matching EVM semantics. -/
def gasHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_GAS"
      opcodes := [0x5a]
      preBody := stackOverflowGuardAsm
      body    := EvmAsm.Evm64.GasOpcode.evm_gas .x20 .x14
      tail    := .advanceAndRet 1 } ]


-- @@ L25-25 verbatim
end EvmAsm.Codegen
