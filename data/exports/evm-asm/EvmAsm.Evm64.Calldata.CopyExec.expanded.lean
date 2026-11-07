/-
  EvmAsm.Evm64.Calldata.CopyExec

  Bridge from CALLDATACOPY stack arguments to executable calldata bytes
  (GH #104).
-/

module

public import EvmAsm.Evm64.Calldata.Basic
public import EvmAsm.Evm64.Calldata.CopyArgs


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace CallDataCopyExec


-- @@ L18-23 verbatim
/-- Bytes written by CALLDATACOPY for a decoded stack-argument record.
    Distinctive token: CallDataCopyExec.copiedBytesFromArgs. -/
def copiedBytesFromArgs
    (data : List (BitVec 8)) (args : CallDataCopyArgs.Args) : List (BitVec 8) :=
  Calldata.callDataCopyBytes
    data (CallDataCopyArgs.sourceOffsetNat args) (CallDataCopyArgs.sizeNat args)


-- @@ L25-28 verbatim
theorem copiedBytesFromArgs_eq
    (data : List (BitVec 8)) (args : CallDataCopyArgs.Args) :
    copiedBytesFromArgs data args =
      Calldata.callDataCopyBytes data args.dataOffset.toNat args.size.toNat := rfl


-- @@ L30-33 verbatim
@[simp] theorem copiedBytesFromArgs_length
    (data : List (BitVec 8)) (args : CallDataCopyArgs.Args) :
    (copiedBytesFromArgs data args).length = args.size.toNat := by
  simp [copiedBytesFromArgs, CallDataCopyArgs.sizeNat]


-- @@ L35-39 verbatim
@[simp] theorem copiedBytesFromArgs_zero_size
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) :
    copiedBytesFromArgs data (CallDataCopyArgs.copyArgs destOffset dataOffset 0) = [] := by
  simp [copiedBytesFromArgs, CallDataCopyArgs.copyArgs,
    CallDataCopyArgs.sourceOffsetNat, CallDataCopyArgs.sizeNat]


-- @@ L41-48 verbatim
theorem copiedBytesFromArgs_get
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = Calldata.callDataByte data (args.dataOffset.toNat + i) := by
  unfold copiedBytesFromArgs CallDataCopyArgs.sourceOffsetNat CallDataCopyArgs.sizeNat
  exact Calldata.callDataCopyBytes_get h


-- @@ L50-57 verbatim
theorem copiedBytesFromArgs_get_of_in_bounds
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : args.dataOffset.toNat + i < data.length) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = data[args.dataOffset.toNat + i] := by
  rw [copiedBytesFromArgs_get h, Calldata.callDataByte_of_lt hsrc]


-- @@ L59-66 verbatim
theorem copiedBytesFromArgs_get_of_out_of_bounds
    {data : List (BitVec 8)} {args : CallDataCopyArgs.Args} {i : Nat}
    (h : i < args.size.toNat)
    (hsrc : data.length ≤ args.dataOffset.toNat + i) :
    (copiedBytesFromArgs data args)[i]'(by
      simpa [copiedBytesFromArgs_length] using h)
      = 0 := by
  rw [copiedBytesFromArgs_get h, Calldata.callDataByte_of_ge hsrc]


-- @@ L68-71 verbatim
@[simp] theorem copiedBytesFromArgs_nil
    (args : CallDataCopyArgs.Args) :
    copiedBytesFromArgs [] args = List.replicate args.size.toNat 0 := by
  simp [copiedBytesFromArgs_eq]


-- @@ L73-73 verbatim
end CallDataCopyExec

-- @@ L74-74 verbatim
end EvmAsm.Evm64
