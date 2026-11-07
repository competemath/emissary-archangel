/-
  EvmAsm.Evm64.Code.CopyArgs

  Pure stack-argument record for CODECOPY executable-spec bridges
  (GH #107 / GH #118).
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Evm64.MemoryGas


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace CodeCopyArgs


-- @@ L18-22 verbatim
/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L24-30 verbatim
/-- CODECOPY stack arguments: destination memory offset, code source offset,
    and byte size. -/
structure Args where
  destOffset : EvmWord
  codeOffset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L32-33 verbatim
/-- CODECOPY pops three stack words. -/
def stackArgumentCount : Nat := 3


-- @@ L35-36 verbatim
/-- CODECOPY pushes no result words. -/
def resultCount : Nat := 0


-- @@ L38-39 verbatim
/-- CODECOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1


-- @@ L41-44 verbatim
/-- Convenience builder for CODECOPY stack arguments.
    Distinctive token: CodeCopyArgs.copyArgs #107 #118. -/
def copyArgs (destOffset codeOffset size : EvmWord) : Args :=
  { destOffset := destOffset, codeOffset := codeOffset, size := size }


-- @@ L46-48 verbatim
/-- Destination memory range written by CODECOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }


-- @@ L50-52 verbatim
/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat


-- @@ L54-56 verbatim
/-- Code source offset as a host `Nat` for executable code helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.codeOffset.toNat


-- @@ L58-60 verbatim
/-- Byte count as a host `Nat` for executable memory/code helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat


-- @@ L62-66 verbatim
/-- Dynamic gas caused by CODECOPY's copy charge and destination memory
    expansion. -/
def copyDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.codeCopyDynamicCost
    sizeBytes (destinationOffsetNat args) (sizeNat args)


-- @@ L68-68 verbatim
theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl


-- @@ L70-70 verbatim
theorem resultCount_eq_zero : resultCount = 0 := rfl


-- @@ L72-72 verbatim
theorem memoryRangeCount_eq_one : memoryRangeCount = 1 := rfl


-- @@ L74-75 verbatim
theorem copyArgs_destOffset (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).destOffset = destOffset := rfl


-- @@ L77-78 verbatim
theorem copyArgs_codeOffset (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).codeOffset = codeOffset := rfl


-- @@ L80-81 verbatim
theorem copyArgs_size (destOffset codeOffset size : EvmWord) :
    (copyArgs destOffset codeOffset size).size = size := rfl


-- @@ L83-84 verbatim
theorem destinationRange_offset (args : Args) :
    (destinationRange args).offset = args.destOffset := rfl


-- @@ L86-87 verbatim
theorem destinationRange_size (args : Args) :
    (destinationRange args).size = args.size := rfl


-- @@ L89-90 verbatim
theorem destinationOffsetNat_eq (args : Args) :
    destinationOffsetNat args = args.destOffset.toNat := rfl


-- @@ L92-93 verbatim
theorem sourceOffsetNat_eq (args : Args) :
    sourceOffsetNat args = args.codeOffset.toNat := rfl


-- @@ L95-96 verbatim
theorem sizeNat_eq (args : Args) :
    sizeNat args = args.size.toNat := rfl


-- @@ L98-102 verbatim
theorem copyDynamicCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.codeCopyDynamicCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl


-- @@ L104-108 verbatim
@[simp] theorem copyDynamicCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset codeOffset : EvmWord) :
    copyDynamicCostFromArgs sizeBytes
      (copyArgs destOffset codeOffset 0) = 0 := by
  simp [copyDynamicCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]


-- @@ L110-116 verbatim
theorem copyDynamicCostFromArgs_eq_copy_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.codeCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth


-- @@ L118-124 verbatim
theorem copyDynamicCostFromArgs_eq_copy_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.codeCopyDynamicCost_eq_copy_charge_of_access_le h_access


-- @@ L126-126 verbatim
end CodeCopyArgs

-- @@ L127-127 verbatim
end EvmAsm.Evm64
