/-
  EvmAsm.Evm64.ReturnData.CopyMemory

  Destination-address bridge for RETURNDATACOPY copied bytes
  (GH #107 / GH #114).
-/

module

public import Mathlib.Data.List.GetD
public import EvmAsm.Evm64.ReturnData.CopyExec


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace ReturnDataCopyMemory


-- @@ L18-20 verbatim
/-- First destination memory byte written by RETURNDATACOPY. -/
def destinationStart (args : ReturnDataCopyArgs.Args) : Nat :=
  ReturnDataCopyArgs.destinationOffsetNat args


-- @@ L22-24 verbatim
/-- One-past-the-end destination memory byte written by RETURNDATACOPY. -/
def destinationEnd (args : ReturnDataCopyArgs.Args) : Nat :=
  destinationStart args + ReturnDataCopyArgs.sizeNat args


-- @@ L26-28 verbatim
/-- Destination-relative index for a concrete memory byte address. -/
def writeIndex (args : ReturnDataCopyArgs.Args) (addr : Nat) : Nat :=
  addr - destinationStart args


-- @@ L30-32 verbatim
/-- Prop-valued range predicate for addresses written by RETURNDATACOPY. -/
def writesAddress (args : ReturnDataCopyArgs.Args) (addr : Nat) : Prop :=
  destinationStart args ≤ addr ∧ addr < destinationEnd args


-- @@ L34-37 verbatim
instance (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    Decidable (writesAddress args addr) := by
  unfold writesAddress
  infer_instance


-- @@ L39-47 verbatim
/-- Byte written at `addr` by RETURNDATACOPY, or zero outside the destination
    range. Distinctive token: ReturnDataCopyMemory.copyWriteByteAt #107 #114. -/
def copyWriteByteAt
    (data : List (BitVec 8)) (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    BitVec 8 :=
  if _ : writesAddress args addr then
    (ReturnDataCopyExec.copiedBytesFromArgs data args).getD (writeIndex args addr) 0
  else
    0


-- @@ L49-50 verbatim
theorem destinationStart_eq (args : ReturnDataCopyArgs.Args) :
    destinationStart args = args.destOffset.toNat := rfl


-- @@ L52-53 verbatim
theorem destinationEnd_eq (args : ReturnDataCopyArgs.Args) :
    destinationEnd args = args.destOffset.toNat + args.size.toNat := rfl


-- @@ L55-56 verbatim
theorem writeIndex_eq (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    writeIndex args addr = addr - args.destOffset.toNat := rfl


-- @@ L58-61 verbatim
theorem writesAddress_iff (args : ReturnDataCopyArgs.Args) (addr : Nat) :
    writesAddress args addr ↔
      args.destOffset.toNat ≤ addr ∧ addr < args.destOffset.toNat + args.size.toNat := by
  rfl


-- @@ L63-69 verbatim
theorem writesAddress_at_destination_add
    {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    writesAddress args (destinationStart args + i) := by
  unfold writesAddress destinationEnd destinationStart ReturnDataCopyArgs.destinationOffsetNat
    ReturnDataCopyArgs.sizeNat
  omega


-- @@ L71-75 verbatim
theorem writeIndex_at_destination_add
    (args : ReturnDataCopyArgs.Args) (i : Nat) :
    writeIndex args (destinationStart args + i) = i := by
  unfold writeIndex
  omega


-- @@ L77-82 verbatim
theorem copyWriteByteAt_outside
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {addr : Nat}
    (h : ¬ writesAddress args addr) :
    copyWriteByteAt data args addr = 0 := by
  rw [copyWriteByteAt]
  rw [dif_neg h]


-- @@ L84-95 verbatim
theorem copyWriteByteAt_at_destination_add
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      (ReturnDataCopyExec.copiedBytesFromArgs data args)[i]'(by
        simpa [ReturnDataCopyExec.copiedBytesFromArgs_length] using h) := by
  rw [copyWriteByteAt]
  rw [dif_pos (writesAddress_at_destination_add h)]
  rw [writeIndex_at_destination_add]
  exact List.getD_eq_getElem
    (l := ReturnDataCopyExec.copiedBytesFromArgs data args) (d := 0)
    (by simpa [ReturnDataCopyExec.copiedBytesFromArgs_length] using h)


-- @@ L97-103 verbatim
theorem copyWriteByteAt_at_destination_add_eq_returnDataByte
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      ReturnData.byte data (args.dataOffset.toNat + i) := by
  rw [copyWriteByteAt_at_destination_add h]
  exact ReturnDataCopyExec.copiedBytesFromArgs_get h


-- @@ L105-112 verbatim
theorem copyWriteByteAt_at_destination_add_of_in_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.dataOffset.toNat + i < data.length) :
    copyWriteByteAt data args (destinationStart args + i) =
      data[args.dataOffset.toNat + i] := by
  rw [copyWriteByteAt_at_destination_add_eq_returnDataByte h]
  exact ReturnData.byte_of_lt hsrc


-- @@ L114-120 verbatim
theorem copyWriteByteAt_at_destination_add_of_out_of_bounds
    {data : List (BitVec 8)} {args : ReturnDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : data.length ≤ args.dataOffset.toNat + i) :
    copyWriteByteAt data args (destinationStart args + i) = 0 := by
  rw [copyWriteByteAt_at_destination_add_eq_returnDataByte h]
  exact ReturnData.byte_of_ge hsrc


-- @@ L122-130 verbatim
@[simp] theorem copyWriteByteAt_zero_size
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) (addr : Nat) :
    copyWriteByteAt data (ReturnDataCopyArgs.copyArgs destOffset dataOffset 0) addr = 0 := by
  apply copyWriteByteAt_outside
  intro h
  unfold writesAddress destinationEnd destinationStart ReturnDataCopyArgs.destinationOffsetNat
    ReturnDataCopyArgs.sizeNat ReturnDataCopyArgs.copyArgs at h
  simp at h
  omega


-- @@ L132-132 verbatim
end ReturnDataCopyMemory

-- @@ L133-133 verbatim
end EvmAsm.Evm64
