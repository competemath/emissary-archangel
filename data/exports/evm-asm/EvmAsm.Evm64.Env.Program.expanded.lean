/-
  EvmAsm.Evm64.Env.Program

  Parameterized program implementing the simple environment opcodes
  (`ADDRESS`, `CALLER`, `CALLVALUE`, `ORIGIN`, `GASPRICE`, `COINBASE`,
  `TIMESTAMP`, `NUMBER`, `PREVRANDAO`, `GASLIMIT`, `CHAINID`, `BASEFEE`,
  `SELFBALANCE` — see `EvmAsm.Evm64.Env.Field.SimpleEnvField`).

  Slice 4 of GH #103 / `evm-asm-30td`. The program is parameterized over
  the `SimpleEnvField` enum so a single skeleton + spec covers all 13
  opcodes; per-opcode wrappers (slice 6 / `evm-asm-bqc2`) are thin
  abbreviations.

  Layout (9 instructions = 36 bytes):

      ADDI x12 x12 (-32)                                -- bump EVM SP
      LD   tmpReg envBaseReg (offset + 0)               -- limb 0 (LSB)
      SD   x12    tmpReg     0
      LD   tmpReg envBaseReg (offset + 8)               -- limb 1
      SD   x12    tmpReg     8
      LD   tmpReg envBaseReg (offset + 16)              -- limb 2
      SD   x12    tmpReg     16
      LD   tmpReg envBaseReg (offset + 24)              -- limb 3 (MSB)
      SD   x12    tmpReg     24

  `envBaseReg` is the caller's environment-base register (see
  `EvmAsm.Evm64.EvmState.Layout.envBaseReg`). `tmpReg` is a caller-saved
  temporary distinct from `x12` and `envBaseReg`; the spec slice
  (`evm-asm-3fvb`) will pin down the disjointness side conditions.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Evm64.Env.Field


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace EvmAsm.Evm64

-- @@ L42-42 verbatim
namespace Env


-- @@ L44-44 verbatim
open EvmAsm.Rv64

-- @@ L45-45 verbatim
open SimpleEnvField


-- @@ L47-53 verbatim
/-- Load and push a single 64-bit limb of the environment field at
    `field.offset + 8 * i` onto the EVM stack slot `8 * i` above the
    new top-of-stack pointer in `x12`. -/
def env_one_limb (envBaseReg tmpReg : Reg) (field : SimpleEnvField)
    (i : Nat) : Program :=
  LD tmpReg envBaseReg (BitVec.ofNat 12 (field.offset + 8 * i)) ;;
  SD .x12   tmpReg     (BitVec.ofNat 12 (8 * i))


-- @@ L55-63 verbatim
/-- Parameterized program for a simple environment opcode.
    Bumps the EVM stack pointer by 32 bytes and writes the four 64-bit
    limbs of `field.value env` into the freshly-allocated stack slot. -/
def evm_env_load (envBaseReg tmpReg : Reg) (field : SimpleEnvField) : Program :=
  ADDI .x12 .x12 (-32) ;;
  env_one_limb envBaseReg tmpReg field 0 ;;
  env_one_limb envBaseReg tmpReg field 1 ;;
  env_one_limb envBaseReg tmpReg field 2 ;;
  env_one_limb envBaseReg tmpReg field 3


-- @@ L65-68 verbatim
/-- `CodeReq` for `evm_env_load` placed at `base`. -/
abbrev evm_env_load_code
    (envBaseReg tmpReg : Reg) (field : SimpleEnvField) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_env_load envBaseReg tmpReg field)


-- @@ L70-74 verbatim
/-- One limb block is exactly 2 instructions (LD + SD). -/
theorem env_one_limb_length
    (envBaseReg tmpReg : Reg) (field : SimpleEnvField) (i : Nat) :
    (env_one_limb envBaseReg tmpReg field i).length = 2 := by
  simp [env_one_limb, LD, SD, single, seq]


-- @@ L76-80 verbatim
/-- `evm_env_load` is exactly 9 RISC-V instructions = 36 bytes. -/
theorem evm_env_load_length
    (envBaseReg tmpReg : Reg) (field : SimpleEnvField) :
    (evm_env_load envBaseReg tmpReg field).length = 9 := by
  simp [evm_env_load, ADDI, single, seq, env_one_limb_length]


-- @@ L82-82 verbatim
end Env

-- @@ L83-83 verbatim
end EvmAsm.Evm64
