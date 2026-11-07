/-
  EvmAsm.Evm64.Calldata.CopyArgs

  Pure stack-argument record for CALLDATACOPY (GH #104).
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Evm64.MemoryGas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace CallDataCopyArgs


-- @@ L17-21 verbatim
/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L23-29 verbatim
/-- CALLDATACOPY stack arguments: destination memory offset, calldata source
    offset, and byte size. -/
structure Args where
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L31-32 verbatim
/-- CALLDATACOPY pops three stack words. -/
def stackArgumentCount : Nat := 3


-- @@ L34-35 verbatim
/-- CALLDATACOPY pushes no result words. -/
def resultCount : Nat := 0


-- @@ L37-38 verbatim
/-- CALLDATACOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1


-- @@ L40-42 verbatim
/-- Convenience builder for CALLDATACOPY stack arguments. -/
def copyArgs (destOffset dataOffset size : EvmWord) : Args :=
  { destOffset := destOffset, dataOffset := dataOffset, size := size }


-- @@ L44-46 verbatim
/-- Destination memory range written by CALLDATACOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }


-- @@ L48-50 verbatim
/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat


-- @@ L52-54 verbatim
/-- Calldata source offset as a host `Nat` for executable calldata helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.dataOffset.toNat


-- @@ L56-58 verbatim
/-- Byte count as a host `Nat` for executable memory/calldata helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat


-- @@ L60-64 verbatim
/-- Memory expansion caused by the CALLDATACOPY destination range.
    Distinctive token: CallDataCopyArgs.copyMemoryExpansionCostFromArgs. -/
def copyMemoryExpansionCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.memoryAccessExpansionCost
    sizeBytes (destinationOffsetNat args) (sizeNat args)


-- @@ L66-66 verbatim
theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl


-- @@ L68-68 verbatim
theorem resultCount_eq_zero : resultCount = 0 := rfl


-- @@ L70-70 verbatim
theorem memoryRangeCount_eq_one : memoryRangeCount = 1 := rfl


-- @@ L72-73 verbatim
theorem copyArgs_destOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).destOffset = destOffset := rfl


-- @@ L75-76 verbatim
theorem copyArgs_dataOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).dataOffset = dataOffset := rfl


-- @@ L78-79 verbatim
theorem copyArgs_size (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).size = size := rfl


-- @@ L81-82 verbatim
theorem destinationRange_offset (args : Args) :
    (destinationRange args).offset = args.destOffset := rfl


-- @@ L84-85 verbatim
theorem destinationRange_size (args : Args) :
    (destinationRange args).size = args.size := rfl


-- @@ L87-88 verbatim
theorem destinationOffsetNat_eq (args : Args) :
    destinationOffsetNat args = args.destOffset.toNat := rfl


-- @@ L90-91 verbatim
theorem sourceOffsetNat_eq (args : Args) :
    sourceOffsetNat args = args.dataOffset.toNat := rfl


-- @@ L93-94 verbatim
theorem sizeNat_eq (args : Args) :
    sizeNat args = args.size.toNat := rfl


-- @@ L96-100 verbatim
theorem copyMemoryExpansionCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyMemoryExpansionCostFromArgs sizeBytes args =
      MemoryGas.memoryAccessExpansionCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl


-- @@ L102-106 verbatim
@[simp] theorem copyMemoryExpansionCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset dataOffset : EvmWord) :
    copyMemoryExpansionCostFromArgs sizeBytes
      (copyArgs destOffset dataOffset 0) = 0 := by
  simp [copyMemoryExpansionCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]


-- @@ L108-113 verbatim
theorem copyMemoryExpansionCostFromArgs_eq_zero_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyMemoryExpansionCostFromArgs sizeBytes args = 0 := by
  exact MemoryGas.memoryAccessExpansionCost_eq_zero_of_no_growth h_no_growth


-- @@ L115-120 verbatim
theorem copyMemoryExpansionCostFromArgs_eq_zero_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyMemoryExpansionCostFromArgs sizeBytes args = 0 := by
  exact MemoryGas.memoryAccessExpansionCost_eq_zero_of_access_le h_access


-- @@ L122-122 verbatim
end CallDataCopyArgs

-- @@ L123-123 verbatim
end EvmAsm.Evm64
