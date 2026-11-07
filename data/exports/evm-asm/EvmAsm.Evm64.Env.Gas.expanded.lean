/-
  EvmAsm.Evm64.Env.Gas

  Static gas helpers for simple environment opcodes (issues #117 / #103).
-/

module

public import EvmAsm.Evm64.Env.Field
public import EvmAsm.Evm64.Gas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace Env


-- @@ L17-17 verbatim
namespace SimpleEnvField


-- @@ L19-33 verbatim
/-- EVM opcode table entry for a simple environment field. -/
def opcode : SimpleEnvField → EvmOpcode
  | address => .ADDRESS
  | caller => .CALLER
  | callValue => .CALLVALUE
  | origin => .ORIGIN
  | gasPrice => .GASPRICE
  | coinbase => .COINBASE
  | timestamp => .TIMESTAMP
  | number => .NUMBER
  | prevrandao => .PREVRANDAO
  | gasLimit => .GASLIMIT
  | chainId => .CHAINID
  | baseFee => .BASEFEE
  | selfBalance => .SELFBALANCE


-- @@ L35-38 verbatim
/-- Shanghai static/base gas for the simple environment opcodes. -/
def simpleEnvStaticGasCost : SimpleEnvField → Nat
  | selfBalance => 5
  | _ => 2


-- @@ L40-42 verbatim
theorem opcode_byte (field : SimpleEnvField) :
    EvmOpcode.byte? field.opcode = some field.opcodeByte := by
  cases field <;> rfl


-- @@ L44-44 verbatim
end SimpleEnvField


-- @@ L46-46 verbatim
end Env

-- @@ L47-47 verbatim
end EvmAsm.Evm64
