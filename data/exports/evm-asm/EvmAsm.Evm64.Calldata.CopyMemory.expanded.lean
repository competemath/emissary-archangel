/-
  EvmAsm.Evm64.Calldata.CopyMemory

  Destination-address bridge for CALLDATACOPY copied bytes (GH #104).
-/

module

public import Mathlib.Data.List.GetD
public import EvmAsm.Evm64.Calldata.CopyExec


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace CallDataCopyMemory


-- @@ L17-19 verbatim
/-- First destination memory byte written by CALLDATACOPY. -/
def destinationStart (args : CallDataCopyArgs.Args) : Nat :=
  CallDataCopyArgs.destinationOffsetNat args


-- @@ L21-23 verbatim
/-- One-past-the-end destination memory byte written by CALLDATACOPY. -/
def destinationEnd (args : CallDataCopyArgs.Args) : Nat :=
  destinationStart args + CallDataCopyArgs.sizeNat args


-- @@ L25-27 verbatim
/-- Destination-relative index for a concrete memory byte address. -/
def writeIndex (args : CallDataCopyArgs.Args) (addr : Nat) : Nat :=
  addr - destinationStart args


-- @@ L29-31 verbatim
/-- Prop-valued range predicate for addresses written by CALLDATACOPY. -/
def writesAddress (args : CallDataCopyArgs.Args) (addr : Nat) : Prop :=
  destinationStart args ≤ addr ∧ addr < destinationEnd args


-- @@ L33-36 verbatim
instance (args : CallDataCopyArgs.Args) (addr : Nat) :
    Decidable (writesAddress args addr) := by
  unfold writesAddress
  infer_instance


-- @@ L38-46 verbatim
/-- Byte written at `addr` by CALLDATACOPY, or zero outside the destination
    range. Distinctive token: CallDataCopyMemory.copyWriteByteAt #104. -/
def copyWriteByteAt
    (data : List (BitVec 8)) (args : CallDataCopyArgs.Args) (addr : Nat) :
    BitVec 8 :=
  if _ : writesAddress args addr then
    (CallDataCopyExec.copiedBytesFromArgs data args).getD (writeIndex args addr) 0
  else
    0


-- @@ L48-49 verbatim
theorem destinationStart_eq (args : CallDataCopyArgs.Args) :
    destinationStart args = args.destOffset.toNat := rfl


-- @@ L51-52 verbatim
theorem destinationEnd_eq (args : CallDataCopyArgs.Args) :
    destinationEnd args = args.destOffset.toNat + args.size.toNat := rfl


-- @@ L54-55 verbatim
theorem writeIndex_eq (args : CallDataCopyArgs.Args) (addr : Nat) :
    writeIndex args addr = addr - args.destOffset.toNat := rfl


-- @@ L57-60 verbatim
theorem writesAddress_iff (args : CallDataCopyArgs.Args) (addr : Nat) :
    writesAddress args addr ↔
      args.destOffset.toNat ≤ addr ∧ addr < args.destOffset.toNat + args.size.toNat := by
  rfl


-- @@ L62-68 verbatim
theorem writesAddress_at_destination_add
    {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    writesAddress args (destinationStart args + i) := by
  unfold writesAddress destinationEnd destinationStart CallDataCopyArgs.destinationOffsetNat
    CallDataCopyArgs.sizeNat
  omega


-- @@ L70-80 verbatim
theorem writesAddress_iff_exists_index
    (args : CallDataCopyArgs.Args) (addr : Nat) :
    writesAddress args addr ↔
      ∃ i, i < args.size.toNat ∧ addr = destinationStart args + i := by
  unfold writesAddress destinationEnd destinationStart CallDataCopyArgs.destinationOffsetNat
    CallDataCopyArgs.sizeNat
  constructor
  · intro h
    refine ⟨addr - args.destOffset.toNat, ?_, ?_⟩ <;> omega
  · rintro ⟨i, h_lt, rfl⟩
    omega


-- @@ L82-86 verbatim
theorem writeIndex_at_destination_add
    (args : CallDataCopyArgs.Args) (i : Nat) :
    writeIndex args (destinationStart args + i) = i := by
  unfold writeIndex
  omega


-- @@ L88-93 verbatim
theorem copyWriteByteAt_outside
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {addr : Nat}
    (h : ¬ writesAddress args addr) :
    copyWriteByteAt data args addr = 0 := by
  rw [copyWriteByteAt]
  rw [dif_neg h]


-- @@ L95-106 verbatim
theorem copyWriteByteAt_at_destination_add
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      (CallDataCopyExec.copiedBytesFromArgs data args)[i]'(by
        simpa [CallDataCopyExec.copiedBytesFromArgs_length] using h) := by
  rw [copyWriteByteAt]
  rw [dif_pos (writesAddress_at_destination_add h)]
  rw [writeIndex_at_destination_add]
  exact List.getD_eq_getElem
    (l := CallDataCopyExec.copiedBytesFromArgs data args) (d := 0)
    (by simpa [CallDataCopyExec.copiedBytesFromArgs_length] using h)


-- @@ L108-114 verbatim
theorem copyWriteByteAt_at_destination_add_eq_callDataByte
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    copyWriteByteAt data args (destinationStart args + i) =
      Calldata.callDataByte data (args.dataOffset.toNat + i) := by
  rw [copyWriteByteAt_at_destination_add h]
  exact CallDataCopyExec.copiedBytesFromArgs_get h


-- @@ L116-123 verbatim
theorem copyWriteByteAt_at_destination_add_of_in_bounds
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.dataOffset.toNat + i < data.length) :
    copyWriteByteAt data args (destinationStart args + i) =
      data[args.dataOffset.toNat + i] := by
  rw [copyWriteByteAt_at_destination_add_eq_callDataByte h]
  exact Calldata.callDataByte_of_lt hsrc


-- @@ L125-131 verbatim
theorem copyWriteByteAt_at_destination_add_of_out_of_bounds
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : data.length ≤ args.dataOffset.toNat + i) :
    copyWriteByteAt data args (destinationStart args + i) = 0 := by
  rw [copyWriteByteAt_at_destination_add_eq_callDataByte h]
  exact Calldata.callDataByte_of_ge hsrc


-- @@ L133-141 verbatim
@[simp] theorem copyWriteByteAt_zero_size
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) (addr : Nat) :
    copyWriteByteAt data (CallDataCopyArgs.copyArgs destOffset dataOffset 0) addr = 0 := by
  apply copyWriteByteAt_outside
  intro h
  unfold writesAddress destinationEnd destinationStart CallDataCopyArgs.destinationOffsetNat
    CallDataCopyArgs.sizeNat CallDataCopyArgs.copyArgs at h
  simp at h
  omega


-- @@ L143-143 verbatim
end CallDataCopyMemory

-- @@ L144-144 verbatim
end EvmAsm.Evm64
