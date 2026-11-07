/-
  EvmAsm.Evm64.KeccakArgs

  Pure stack-argument record for KECCAK256/SHA3 (GH #111).
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Evm64.MemoryGas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace KeccakArgs


-- @@ L18-22 verbatim
/-- Memory slice hashed by KECCAK256, described by EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L24-27 verbatim
/-- Stack arguments for KECCAK256/SHA3: input memory offset and size. -/
structure Args where
  input : MemoryRange
  deriving Repr


-- @@ L29-30 verbatim
/-- KECCAK256 pops two stack words: input offset and input size. -/
def stackArgumentCount : Nat := 2


-- @@ L32-33 verbatim
/-- KECCAK256 pushes one 256-bit hash result. -/
def resultCount : Nat := 1


-- @@ L35-37 verbatim
/-- Convenience builder for KECCAK256 stack arguments. -/
def keccakArgs (offset size : EvmWord) : Args :=
  { input := { offset := offset, size := size } }


-- @@ L39-41 verbatim
/-- Input memory range projected from KECCAK256 stack arguments. -/
def inputRange (args : Args) : MemoryRange :=
  args.input


-- @@ L43-45 verbatim
/-- Input offset converted to host `Nat` for executable gas/memory helpers. -/
def inputOffsetNat (args : Args) : Nat :=
  args.input.offset.toNat


-- @@ L47-49 verbatim
/-- Input size converted to host `Nat` for executable gas/memory helpers. -/
def inputSizeNat (args : Args) : Nat :=
  args.input.size.toNat


-- @@ L51-54 verbatim
/-- Dynamic gas for KECCAK256 computed from the stack-argument record.
    Distinctive token: KeccakArgs.keccakDynamicCostFromArgs. -/
def keccakDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.keccakDynamicCost sizeBytes (inputOffsetNat args) (inputSizeNat args)


-- @@ L56-56 verbatim
theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl


-- @@ L58-58 verbatim
theorem resultCount_eq_one : resultCount = 1 := rfl


-- @@ L60-61 verbatim
theorem keccakArgs_offset (offset size : EvmWord) :
    (keccakArgs offset size).input.offset = offset := rfl


-- @@ L63-64 verbatim
theorem keccakArgs_size (offset size : EvmWord) :
    (keccakArgs offset size).input.size = size := rfl


-- @@ L66-67 verbatim
theorem inputRange_offset (args : Args) :
    (inputRange args).offset = args.input.offset := rfl


-- @@ L69-70 verbatim
theorem inputRange_size (args : Args) :
    (inputRange args).size = args.input.size := rfl


-- @@ L72-73 verbatim
theorem inputOffsetNat_eq (args : Args) :
    inputOffsetNat args = args.input.offset.toNat := rfl


-- @@ L75-76 verbatim
theorem inputSizeNat_eq (args : Args) :
    inputSizeNat args = args.input.size.toNat := rfl


-- @@ L78-80 verbatim
theorem keccakDynamicCostFromArgs_eq (sizeBytes : Nat) (args : Args) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakDynamicCost sizeBytes args.input.offset.toNat args.input.size.toNat := rfl


-- @@ L82-85 verbatim
@[simp] theorem keccakDynamicCostFromArgs_zero_length
    (sizeBytes : Nat) (offset : EvmWord) :
    keccakDynamicCostFromArgs sizeBytes (keccakArgs offset 0) = 0 := by
  simp [keccakDynamicCostFromArgs, keccakArgs, inputOffsetNat, inputSizeNat]


-- @@ L87-93 verbatim
theorem keccakDynamicCostFromArgs_eq_word_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.input.offset.toNat args.input.size.toNat = sizeBytes) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakGasPerWord * MemoryGas.memoryWords args.input.size.toNat := by
  exact MemoryGas.keccakDynamicCost_eq_word_charge_of_no_growth h_no_growth


-- @@ L95-101 verbatim
theorem keccakDynamicCostFromArgs_eq_word_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.input.offset.toNat + args.input.size.toNat) ≤ sizeBytes) :
    keccakDynamicCostFromArgs sizeBytes args =
      MemoryGas.keccakGasPerWord * MemoryGas.memoryWords args.input.size.toNat := by
  exact MemoryGas.keccakDynamicCost_eq_word_charge_of_access_le h_access


-- @@ L103-103 verbatim
end KeccakArgs


-- @@ L105-105 verbatim
end EvmAsm.Evm64
