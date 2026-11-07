/-
  EvmAsm.Evm64.Env.Semantics

  Pure semantic bridge for simple environment opcode bytes (GH #103 slice 3).
-/

module

public import EvmAsm.Evm64.Env.Field


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace Env


-- @@ L16-18 verbatim
/-- Value pushed by a simple environment opcode byte, when the byte is supported. -/
def simpleEnvOpcodeValue? (opcode : Nat) (env : EvmEnv) : Option EvmWord :=
  (SimpleEnvField.ofOpcodeByte? opcode).map (fun field => field.value env)


-- @@ L20-23 verbatim
theorem simpleEnvOpcodeValue?_of_decoded {opcode : Nat} {field : SimpleEnvField}
    (env : EvmEnv) (h_decode : SimpleEnvField.ofOpcodeByte? opcode = some field) :
    simpleEnvOpcodeValue? opcode env = some (field.value env) := by
  simp [simpleEnvOpcodeValue?, h_decode]


-- @@ L25-27 verbatim
theorem simpleEnvOpcodeValue?_of_opcodeByte (field : SimpleEnvField) (env : EvmEnv) :
    simpleEnvOpcodeValue? field.opcodeByte env = some (field.value env) := by
  exact simpleEnvOpcodeValue?_of_decoded env (SimpleEnvField.ofOpcodeByte?_opcodeByte field)


-- @@ L29-32 verbatim
theorem simpleEnvOpcodeValue?_of_unknown {opcode : Nat} (env : EvmEnv)
    (h_decode : SimpleEnvField.ofOpcodeByte? opcode = none) :
    simpleEnvOpcodeValue? opcode env = none := by
  simp [simpleEnvOpcodeValue?, h_decode]


-- @@ L34-36 verbatim
@[simp] theorem simpleEnvOpcodeValue?_balance (env : EvmEnv) :
    simpleEnvOpcodeValue? 0x31 env = none := by
  exact simpleEnvOpcodeValue?_of_unknown env SimpleEnvField.ofOpcodeByte?_balance


-- @@ L38-40 verbatim
@[simp] theorem simpleEnvOpcodeValue?_unknown_ff (env : EvmEnv) :
    simpleEnvOpcodeValue? 0xff env = none := by
  exact simpleEnvOpcodeValue?_of_unknown env SimpleEnvField.ofOpcodeByte?_unknown_ff


-- @@ L42-42 verbatim
end Env

-- @@ L43-43 verbatim
end EvmAsm.Evm64
