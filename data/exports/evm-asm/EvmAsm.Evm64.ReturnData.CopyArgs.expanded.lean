/-
  EvmAsm.Evm64.ReturnData.CopyArgs

  Pure stack-argument record for RETURNDATACOPY executable-spec bridges
  (GH #107 / GH #114).
-/

module

public import EvmAsm.Evm64.EvmWord
public import EvmAsm.Evm64.MemoryGas


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace ReturnDataCopyArgs


-- @@ L18-22 verbatim
/-- Memory slice described by an EVM offset and byte size. -/
structure MemoryRange where
  offset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L24-30 verbatim
/-- RETURNDATACOPY stack arguments: destination memory offset, returndata
    source offset, and byte size. -/
structure Args where
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr


-- @@ L32-33 verbatim
/-- RETURNDATACOPY pops three stack words. -/
def stackArgumentCount : Nat := 3


-- @@ L35-36 verbatim
/-- RETURNDATACOPY pushes no result words. -/
def resultCount : Nat := 0


-- @@ L38-39 verbatim
/-- RETURNDATACOPY has one destination memory range. -/
def memoryRangeCount : Nat := 1


-- @@ L41-44 verbatim
/-- Convenience builder for RETURNDATACOPY stack arguments.
    Distinctive token: ReturnDataCopyArgs.copyArgs #107 #114. -/
def copyArgs (destOffset dataOffset size : EvmWord) : Args :=
  { destOffset := destOffset, dataOffset := dataOffset, size := size }


-- @@ L46-48 verbatim
/-- Destination memory range written by RETURNDATACOPY. -/
def destinationRange (args : Args) : MemoryRange :=
  { offset := args.destOffset, size := args.size }


-- @@ L50-52 verbatim
/-- Destination memory offset as a host `Nat` for executable memory helpers. -/
def destinationOffsetNat (args : Args) : Nat :=
  args.destOffset.toNat


-- @@ L54-56 verbatim
/-- Returndata source offset as a host `Nat` for executable returndata helpers. -/
def sourceOffsetNat (args : Args) : Nat :=
  args.dataOffset.toNat


-- @@ L58-60 verbatim
/-- Byte count as a host `Nat` for executable memory/returndata helpers. -/
def sizeNat (args : Args) : Nat :=
  args.size.toNat


-- @@ L62-66 verbatim
/-- Dynamic gas caused by RETURNDATACOPY's copy charge and destination memory
    expansion. -/
def copyDynamicCostFromArgs (sizeBytes : Nat) (args : Args) : Nat :=
  MemoryGas.returndataCopyDynamicCost
    sizeBytes (destinationOffsetNat args) (sizeNat args)


-- @@ L68-68 verbatim
theorem stackArgumentCount_eq_three : stackArgumentCount = 3 := rfl


-- @@ L70-70 verbatim
theorem resultCount_eq_zero : resultCount = 0 := rfl


-- @@ L72-72 verbatim
theorem memoryRangeCount_eq_one : memoryRangeCount = 1 := rfl


-- @@ L74-75 verbatim
theorem copyArgs_destOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).destOffset = destOffset := rfl


-- @@ L77-78 verbatim
theorem copyArgs_dataOffset (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).dataOffset = dataOffset := rfl


-- @@ L80-81 verbatim
theorem copyArgs_size (destOffset dataOffset size : EvmWord) :
    (copyArgs destOffset dataOffset size).size = size := rfl


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
    sourceOffsetNat args = args.dataOffset.toNat := rfl


-- @@ L95-96 verbatim
theorem sizeNat_eq (args : Args) :
    sizeNat args = args.size.toNat := rfl


-- @@ L98-102 verbatim
theorem copyDynamicCostFromArgs_eq
    (sizeBytes : Nat) (args : Args) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.returndataCopyDynamicCost
        sizeBytes args.destOffset.toNat args.size.toNat := rfl


-- @@ L104-108 verbatim
@[simp] theorem copyDynamicCostFromArgs_zero_size
    (sizeBytes : Nat) (destOffset dataOffset : EvmWord) :
    copyDynamicCostFromArgs sizeBytes
      (copyArgs destOffset dataOffset 0) = 0 := by
  simp [copyDynamicCostFromArgs, copyArgs, destinationOffsetNat, sizeNat]


-- @@ L110-116 verbatim
theorem copyDynamicCostFromArgs_eq_copy_charge_of_no_growth
    {sizeBytes : Nat} {args : Args}
    (h_no_growth :
      evmMemExpand sizeBytes args.destOffset.toNat args.size.toNat = sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.returndataCopyDynamicCost_eq_copy_charge_of_no_growth h_no_growth


-- @@ L118-124 verbatim
theorem copyDynamicCostFromArgs_eq_copy_charge_of_access_le
    {sizeBytes : Nat} {args : Args}
    (h_access :
      roundUpTo32 (args.destOffset.toNat + args.size.toNat) ≤ sizeBytes) :
    copyDynamicCostFromArgs sizeBytes args =
      MemoryGas.copyGasPerWord * MemoryGas.memoryCopyWords args.size.toNat := by
  exact MemoryGas.returndataCopyDynamicCost_eq_copy_charge_of_access_le h_access


-- @@ L126-126 verbatim
end ReturnDataCopyArgs

-- @@ L127-127 verbatim
end EvmAsm.Evm64
