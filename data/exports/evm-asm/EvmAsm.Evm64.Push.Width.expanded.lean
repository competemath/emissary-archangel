/-
  EvmAsm.Evm64.Push.Width

  PUSH1..PUSH32 width-validity bridge for GH #101.
-/

module

public import EvmAsm.Evm64.Dispatch
public import EvmAsm.Evm64.Push.Immediate


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace PushWidth


-- @@ L17-22 verbatim
/-- Valid immediate width for PUSH1 through PUSH32.

Distinctive token: PushWidth.validWidth #101.
-/
def validWidth (n : Nat) : Prop :=
  1 ≤ n ∧ n ≤ 32


-- @@ L24-26 verbatim
/-- Concrete opcode byte for PUSHn when `n` is valid. -/
def opcodeByte (n : Nat) : Nat :=
  0x5f + n


-- @@ L28-31 verbatim
theorem validWidth_iff_byte_valid (n : Nat) :
    validWidth n ↔ EvmOpcode.validPushWidth n = true := by
  unfold validWidth EvmOpcode.validPushWidth
  simp


-- @@ L33-37 verbatim
theorem opcodeByte_bounds {n : Nat} (h_valid : validWidth n) :
    0x60 ≤ opcodeByte n ∧ opcodeByte n ≤ 0x7f := by
  dsimp [validWidth] at h_valid
  unfold opcodeByte
  omega


-- @@ L39-42 verbatim
theorem byte?_push_of_valid {n : Nat} (h_valid : validWidth n) :
    EvmOpcode.byte? (EvmOpcode.PUSH n) = some (opcodeByte n) := by
  rw [validWidth_iff_byte_valid] at h_valid
  simp [EvmOpcode.byte?, opcodeByte, h_valid]


-- @@ L44-48 verbatim
theorem decodeByte?_push_of_valid {n : Nat} (h_valid : validWidth n) :
    EvmOpcode.decodeByte? (opcodeByte n) = some (EvmOpcode.PUSH n) := by
  rcases h_valid with ⟨h_pos, h_le⟩
  unfold opcodeByte
  interval_cases n <;> rfl


-- @@ L50-53 verbatim
theorem byte?_roundtrip_push_of_valid {n : Nat} (h_valid : validWidth n) :
    EvmOpcode.byte? (EvmOpcode.PUSH n) = some (opcodeByte n) ∧
      EvmOpcode.decodeByte? (opcodeByte n) = some (EvmOpcode.PUSH n) :=
  ⟨byte?_push_of_valid h_valid, decodeByte?_push_of_valid h_valid⟩


-- @@ L55-57 verbatim
theorem pcAfterPush_gt_pc {pc n : Nat} (h_valid : validWidth n) :
    pc < PushImmediate.pcAfterPush pc n := by
  exact PushImmediate.pc_lt_pcAfterPush_of_width_pos h_valid.1


-- @@ L59-63 verbatim
theorem pcAfterPush_le_pc_plus_33 {pc n : Nat} (h_valid : validWidth n) :
    PushImmediate.pcAfterPush pc n ≤ pc + 33 := by
  dsimp [validWidth] at h_valid
  unfold PushImmediate.pcAfterPush
  omega


-- @@ L65-66 verbatim
theorem pcAfterPush_eq_opcodeByte_offset (pc n : Nat) :
    PushImmediate.pcAfterPush pc n = pc + 1 + n := rfl


-- @@ L68-68 verbatim
end PushWidth

-- @@ L69-69 verbatim
end EvmAsm.Evm64
