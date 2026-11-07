/-
  EvmAsm.Evm64.MemoryGas

  Pure EVM memory expansion gas helpers for issue #118.
-/

module

public import EvmAsm.Evm64.Memory


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace MemoryGas


-- @@ L16-17 verbatim
/-- Shanghai memory expansion linear coefficient, charged per 32-byte word. -/
def memoryGasPerWord : Nat := 3


-- @@ L19-21 verbatim
/-- Convert a byte high-water mark to EVM memory words (32-byte chunks). -/
def memoryWords (sizeBytes : Nat) : Nat :=
  roundUpTo32 sizeBytes / 32


-- @@ L23-25 verbatim
/-- EVM memory cost function `C_mem(words) = 3 * words + words^2 / 512`. -/
def memoryCost (words : Nat) : Nat :=
  memoryGasPerWord * words + (words * words) / 512


-- @@ L27-29 verbatim
/-- Memory cost for a byte high-water mark. -/
def memoryCostForBytes (sizeBytes : Nat) : Nat :=
  memoryCost (memoryWords sizeBytes)


-- @@ L31-33 verbatim
/-- Incremental memory expansion cost from an old byte high-water mark to a new one. -/
def memoryExpansionCost (oldSizeBytes newSizeBytes : Nat) : Nat :=
  memoryCostForBytes newSizeBytes - memoryCostForBytes oldSizeBytes


-- @@ L35-37 verbatim
/-- Incremental memory expansion cost caused by an access `(offset, length)`. -/
def memoryAccessExpansionCost (sizeBytes offset length : Nat) : Nat :=
  memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length)


-- @@ L39-40 verbatim
@[simp] theorem memoryWords_zero : memoryWords 0 = 0 := by
  simp [memoryWords, roundUpTo32_zero]


-- @@ L42-43 verbatim
@[simp] theorem memoryCost_zero : memoryCost 0 = 0 := by
  simp [memoryCost, memoryGasPerWord]


-- @@ L45-46 verbatim
@[simp] theorem memoryCostForBytes_zero : memoryCostForBytes 0 = 0 := by
  simp [memoryCostForBytes]


-- @@ L48-50 verbatim
@[simp] theorem memoryExpansionCost_same (sizeBytes : Nat) :
    memoryExpansionCost sizeBytes sizeBytes = 0 := by
  simp [memoryExpansionCost]


-- @@ L52-54 verbatim
@[simp] theorem memoryAccessExpansionCost_zero_length (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 0 = 0 := by
  simp [memoryAccessExpansionCost]


-- @@ L56-59 verbatim
theorem memoryExpansionCost_eq
    (oldSizeBytes newSizeBytes : Nat) :
    memoryExpansionCost oldSizeBytes newSizeBytes =
      memoryCost (memoryWords newSizeBytes) - memoryCost (memoryWords oldSizeBytes) := rfl


-- @@ L61-65 verbatim
theorem memoryAccessExpansionCost_eq
    (sizeBytes offset length : Nat) :
    memoryAccessExpansionCost sizeBytes offset length =
      memoryCost (memoryWords (evmMemExpand sizeBytes offset length)) -
        memoryCost (memoryWords sizeBytes) := rfl


-- @@ L67-71 verbatim
theorem memoryAccessExpansionCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset length = 0 := by
  simp [memoryAccessExpansionCost, memoryExpansionCost, h_no_growth]


-- @@ L73-78 verbatim
theorem memoryAccessExpansionCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)


-- @@ L80-84 verbatim
theorem memoryAccessExpansionCost_mload_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 32 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 32))) := by
  simp [memoryAccessExpansionCost, evmMemExpand_word_eq]


-- @@ L86-90 verbatim
theorem memoryAccessExpansionCost_mstore_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 32 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 32))) := by
  exact memoryAccessExpansionCost_mload_eq sizeBytes offset


-- @@ L92-96 verbatim
theorem memoryAccessExpansionCost_mstore8_eq (sizeBytes offset : Nat) :
    memoryAccessExpansionCost sizeBytes offset 1 =
      memoryExpansionCost sizeBytes
        (max sizeBytes (roundUpTo32 (offset + 1))) := by
  simp [memoryAccessExpansionCost, evmMemExpand_byte_eq]


-- @@ L98-102 verbatim
theorem memoryAccessExpansionCost_mload_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 32 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L104-108 verbatim
theorem memoryAccessExpansionCost_mstore_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 32 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L110-114 verbatim
theorem memoryAccessExpansionCost_mstore8_eq_zero_of_no_growth
    {sizeBytes offset : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset 1 = sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 1 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L116-120 verbatim
theorem memoryAccessExpansionCost_mload_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 32) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L122-126 verbatim
theorem memoryAccessExpansionCost_mstore_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 32) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 32 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L128-132 verbatim
theorem memoryAccessExpansionCost_mstore8_eq_zero_of_access_le
    {sizeBytes offset : Nat}
    (h_access : roundUpTo32 (offset + 1) ≤ sizeBytes) :
    memoryAccessExpansionCost sizeBytes offset 1 = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L134-139 verbatim
/--
  Dynamic gas for RETURN memory output. RETURN charges memory expansion for
  the output byte slice, but no per-word copy charge.
-/
def returnDynamicCost (sizeBytes offset length : Nat) : Nat :=
  memoryAccessExpansionCost sizeBytes offset length


-- @@ L141-146 verbatim
/--
  Dynamic gas for REVERT memory output. REVERT has the same memory-expansion
  shape as RETURN and no per-word copy charge.
-/
def revertDynamicCost (sizeBytes offset length : Nat) : Nat :=
  memoryAccessExpansionCost sizeBytes offset length


-- @@ L148-150 verbatim
@[simp] theorem returnDynamicCost_zero_length (sizeBytes offset : Nat) :
    returnDynamicCost sizeBytes offset 0 = 0 := by
  simp [returnDynamicCost]


-- @@ L152-154 verbatim
@[simp] theorem revertDynamicCost_zero_length (sizeBytes offset : Nat) :
    revertDynamicCost sizeBytes offset 0 = 0 := by
  simp [revertDynamicCost]


-- @@ L156-159 verbatim
theorem returnDynamicCost_eq
    (sizeBytes offset length : Nat) :
    returnDynamicCost sizeBytes offset length =
      memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl


-- @@ L161-164 verbatim
theorem revertDynamicCost_eq
    (sizeBytes offset length : Nat) :
    revertDynamicCost sizeBytes offset length =
      memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl


-- @@ L166-170 verbatim
theorem returnDynamicCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    returnDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L172-176 verbatim
theorem revertDynamicCost_eq_zero_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    revertDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L178-182 verbatim
theorem returnDynamicCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    returnDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L184-188 verbatim
theorem revertDynamicCost_eq_zero_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    revertDynamicCost sizeBytes offset length = 0 := by
  exact memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L190-191 verbatim
/-- KECCAK256/SHA3 dynamic gas charged per 32-byte input chunk. -/
def keccakGasPerWord : Nat := 6


-- @@ L193-199 verbatim
/--
  KECCAK256 dynamic gas: per-word input charge plus memory expansion caused by
  the input range.
-/
def keccakDynamicCost (sizeBytes offset length : Nat) : Nat :=
  keccakGasPerWord * memoryWords length +
    memoryAccessExpansionCost sizeBytes offset length


-- @@ L201-203 verbatim
@[simp] theorem keccakDynamicCost_zero_length (sizeBytes offset : Nat) :
    keccakDynamicCost sizeBytes offset 0 = 0 := by
  simp [keccakDynamicCost, keccakGasPerWord]


-- @@ L205-209 verbatim
theorem keccakDynamicCost_eq
    (sizeBytes offset length : Nat) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length +
        memoryExpansionCost sizeBytes (evmMemExpand sizeBytes offset length) := rfl


-- @@ L211-217 verbatim
theorem keccakDynamicCost_eq_word_charge_of_no_growth
    {sizeBytes offset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes offset length = sizeBytes) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length := by
  simp [keccakDynamicCost,
    memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]


-- @@ L219-225 verbatim
theorem keccakDynamicCost_eq_word_charge_of_access_le
    {sizeBytes offset length : Nat}
    (h_access : roundUpTo32 (offset + length) ≤ sizeBytes) :
    keccakDynamicCost sizeBytes offset length =
      keccakGasPerWord * memoryWords length := by
  exact keccakDynamicCost_eq_word_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes offset length h_access)


-- @@ L227-228 verbatim
/-- Dynamic copy gas charged per 32-byte input chunk for copy-style opcodes. -/
def copyGasPerWord : Nat := 3


-- @@ L230-232 verbatim
/-- Number of 32-byte chunks charged by copy-style opcode dynamic gas. -/
def memoryCopyWords (length : Nat) : Nat :=
  memoryWords length


-- @@ L234-240 verbatim
/--
  Generic dynamic gas for copy-style memory writes: per-word copy charge plus
  memory expansion caused by the destination range.
-/
def memoryCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  copyGasPerWord * memoryCopyWords length +
    memoryAccessExpansionCost sizeBytes dstOffset length


-- @@ L242-244 verbatim
/-- CALLDATACOPY dynamic gas: copy charge plus destination memory expansion. -/
def calldataCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length


-- @@ L246-248 verbatim
/-- CODECOPY dynamic gas: copy charge plus destination memory expansion. -/
def codeCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length


-- @@ L250-252 verbatim
/-- RETURNDATACOPY dynamic gas: copy charge plus destination memory expansion. -/
def returndataCopyDynamicCost (sizeBytes dstOffset length : Nat) : Nat :=
  memoryCopyDynamicCost sizeBytes dstOffset length


-- @@ L254-255 verbatim
@[simp] theorem memoryCopyWords_zero : memoryCopyWords 0 = 0 := by
  simp [memoryCopyWords]


-- @@ L257-259 verbatim
@[simp] theorem memoryCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    memoryCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [memoryCopyDynamicCost, copyGasPerWord]


-- @@ L261-263 verbatim
@[simp] theorem calldataCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    calldataCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [calldataCopyDynamicCost]


-- @@ L265-267 verbatim
@[simp] theorem codeCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    codeCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [codeCopyDynamicCost]


-- @@ L269-271 verbatim
@[simp] theorem returndataCopyDynamicCost_zero_length (sizeBytes dstOffset : Nat) :
    returndataCopyDynamicCost sizeBytes dstOffset 0 = 0 := by
  simp [returndataCopyDynamicCost]


-- @@ L273-277 verbatim
theorem memoryCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    memoryCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryExpansionCost sizeBytes (evmMemExpand sizeBytes dstOffset length) := rfl


-- @@ L279-283 verbatim
theorem calldataCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl


-- @@ L285-289 verbatim
theorem codeCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl


-- @@ L291-295 verbatim
theorem returndataCopyDynamicCost_eq
    (sizeBytes dstOffset length : Nat) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length +
        memoryAccessExpansionCost sizeBytes dstOffset length := rfl


-- @@ L297-303 verbatim
theorem memoryCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    memoryCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  simp [memoryCopyDynamicCost,
    memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth]


-- @@ L305-310 verbatim
theorem calldataCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth


-- @@ L312-317 verbatim
theorem codeCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth


-- @@ L319-324 verbatim
theorem returndataCopyDynamicCost_eq_copy_charge_of_no_growth
    {sizeBytes dstOffset length : Nat}
    (h_no_growth : evmMemExpand sizeBytes dstOffset length = sizeBytes) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact memoryCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth


-- @@ L326-332 verbatim
theorem calldataCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    calldataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact calldataCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)


-- @@ L334-340 verbatim
theorem codeCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    codeCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact codeCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)


-- @@ L342-348 verbatim
theorem returndataCopyDynamicCost_eq_copy_charge_of_access_le
    {sizeBytes dstOffset length : Nat}
    (h_access : roundUpTo32 (dstOffset + length) ≤ sizeBytes) :
    returndataCopyDynamicCost sizeBytes dstOffset length =
      copyGasPerWord * memoryCopyWords length := by
  exact returndataCopyDynamicCost_eq_copy_charge_of_no_growth
    (evmMemExpand_eq_old_of_access_le sizeBytes dstOffset length h_access)


-- @@ L350-350 verbatim
end MemoryGas

-- @@ L351-351 verbatim
end EvmAsm.Evm64
