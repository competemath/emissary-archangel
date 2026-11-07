/-
  EvmAsm.Evm64.MStore8.Program

  256-bit EVM MSTORE8 in two layers:

  * `evm_mstore8_kernel` (slice 5 of #99) — single-instruction byte-write
    kernel. Caller has already computed `memBase + offset` into `addrReg`
    and holds the 256-bit value in `dataReg`; the kernel just performs
    the `SB` of the low byte. Stack pop and memory-expansion bookkeeping
    are caller responsibilities here.

  * `evm_mstore8` (slice 5a of #99) — full EVM-level MSTORE8 program.
    Pops two 32-byte words from the EVM stack — offset (top, at `sp`) and
    value (next, at `sp + 32`) — and writes the LOW byte of `value` to
    EVM memory at byte-address `offset`.

    Memory is byte-addressable but lives inside the dword-keyed RV64
    memory via the `extractByte` / `replaceByte` algebra in
    `Rv64/ByteOps.lean`. The RISC-V `SB` instruction handles the
    byte-level write through that layer; this slice just assembles the
    addressing and the pop.

    Per the EVM yellow paper §H.1, MSTORE8 reads only the low 8 bits of
    the value word and triggers a 1-byte memory expansion at byte
    `offset`.

    Implementation (5 instructions = 20 bytes):

      LD   offReg   x12   0     -- low limb of offset (full 64-bit byte addr)
      LD   valReg   x12   32    -- low limb of value (low byte is the relevant one)
      ADD  addrReg  memBaseReg offReg
                                -- target byte address inside the EVM memory buf
      SB   addrReg  valReg 0    -- write the low byte of valReg
      ADDI .x12     .x12  64    -- pop both 32-byte words

    Program-only — the spec proof lands in a follow-up slice. All
    scratch registers (`offReg`, `valReg`, `addrReg`, `memBaseReg`) are
    caller-chosen; the spec slice will pin down the disjointness side
    conditions (must differ from `.x0`, `.x12`, and from each other
    where required for SD/LD non-aliasing).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Rv64.SepLogic


-- @@ L50-50 verbatim
@[expose] public section


-- @@ L52-52 verbatim
namespace EvmAsm.Evm64


-- @@ L54-54 verbatim
open EvmAsm.Rv64


-- @@ L56-64 verbatim
/-- 256-bit EVM MSTORE8 byte-write kernel: a single SB at offset 0.

    `addrReg` carries the EVM memory byte address (caller has already
    computed `memBase + offset`); `dataReg` carries the 256-bit EVM word
    whose low byte is written. Caller is responsible for stack pop and
    memory-expansion bookkeeping; this kernel only performs the byte
    write itself. -/
def evm_mstore8_kernel (addrReg dataReg : Reg) : Program :=
  SB addrReg dataReg 0


-- @@ L66-67 verbatim
abbrev evm_mstore8_kernel_code (addrReg dataReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_mstore8_kernel addrReg dataReg)


-- @@ L69-72 verbatim
/-- Concrete instruction length of the MSTORE8 byte-write kernel. -/
theorem evm_mstore8_kernel_length (addrReg dataReg : Reg) :
    (evm_mstore8_kernel addrReg dataReg).length = 1 := by
  rfl


-- @@ L74-77 verbatim
/-- Concrete byte length of the MSTORE8 byte-write kernel. -/
theorem evm_mstore8_kernel_byte_length (addrReg dataReg : Reg) :
    4 * (evm_mstore8_kernel addrReg dataReg).length = 4 := by
  rw [evm_mstore8_kernel_length]


-- @@ L79-98 verbatim
/-- 256-bit EVM MSTORE8 program parameterized over the registers used as
    scratch and the register holding the EVM memory base address.

    * `offReg` — scratch reg, receives the low 64 bits of the popped
      offset; together with `memBaseReg` it forms the target byte
      address.
    * `valReg` — scratch reg, receives the low 64 bits of the popped
      value (only the low 8 bits matter for `SB`).
    * `addrReg` — scratch reg, holds `memBaseReg + offReg` (the actual
      byte address fed to `SB`).
    * `memBaseReg` — caller-chosen register holding the base address of
      the EVM memory buffer.

    5 instructions = 20 bytes. -/
def evm_mstore8 (offReg valReg addrReg memBaseReg : Reg) : Program :=
  LD offReg .x12 0 ;;
  LD valReg .x12 32 ;;
  ADD addrReg memBaseReg offReg ;;
  SB addrReg valReg 0 ;;
  ADDI .x12 .x12 64


-- @@ L100-102 verbatim
/-- `CodeReq` for `evm_mstore8` placed at `base`. -/
abbrev evm_mstore8_code (offReg valReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_mstore8 offReg valReg addrReg memBaseReg)


-- @@ L104-107 verbatim
/-- Concrete instruction length of `evm_mstore8`. -/
theorem evm_mstore8_length (offReg valReg addrReg memBaseReg : Reg) :
    (evm_mstore8 offReg valReg addrReg memBaseReg).length = 5 := by
  simp [evm_mstore8, LD, ADD, ADDI, SB, single, seq]


-- @@ L109-112 verbatim
/-- Concrete byte length of `evm_mstore8` when placed in RV64 code memory. -/
theorem evm_mstore8_byte_length (offReg valReg addrReg memBaseReg : Reg) :
    4 * (evm_mstore8 offReg valReg addrReg memBaseReg).length = 20 := by
  rw [evm_mstore8_length]


-- @@ L114-116 verbatim
/-- Byte offset of the MSTORE8 offset-load instruction. -/
theorem evm_mstore8_offset_load_byte_off : 4 * 0 = 0 := by
  rfl


-- @@ L118-120 verbatim
/-- Byte offset of the MSTORE8 value-load instruction. -/
theorem evm_mstore8_value_load_byte_off : 4 * 1 = 4 := by
  rfl


-- @@ L122-124 verbatim
/-- Byte offset of the MSTORE8 address-add instruction. -/
theorem evm_mstore8_addr_add_byte_off : 4 * 2 = 8 := by
  rfl


-- @@ L126-128 verbatim
/-- Byte offset of the MSTORE8 byte-store instruction. -/
theorem evm_mstore8_store_byte_off : 4 * 3 = 12 := by
  rfl


-- @@ L130-132 verbatim
/-- Byte offset of the MSTORE8 final stack-pointer update. -/
theorem evm_mstore8_pop_byte_off : 4 * 4 = 16 := by
  rfl


-- @@ L134-136 verbatim
/-- Byte offset immediately after the full MSTORE8 program. -/
theorem evm_mstore8_end_byte_off : 4 * 5 = 20 := by
  rfl


-- @@ L138-138 verbatim
end EvmAsm.Evm64
