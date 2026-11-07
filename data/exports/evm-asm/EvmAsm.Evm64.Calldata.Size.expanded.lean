/-
  EvmAsm.Evm64.Calldata.Size

  Pure CALLDATASIZE semantics for issue #104.
-/

module

public import EvmAsm.Evm64.EvmWord


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace Calldata


-- @@ L16-18 verbatim
/-- CALLDATASIZE pushes the calldata byte length as a 256-bit EVM word. -/
def callDataSizeWord (sizeBytes : Nat) : EvmWord :=
  BitVec.ofNat 256 sizeBytes


-- @@ L20-22 verbatim
/-- CALLDATASIZE semantics for a concrete calldata byte list. -/
def callDataSizeOf (data : List (BitVec 8)) : EvmWord :=
  callDataSizeWord data.length


-- @@ L24-25 verbatim
@[simp] theorem callDataSizeWord_zero :
    callDataSizeWord 0 = 0 := rfl


-- @@ L27-28 verbatim
@[simp] theorem callDataSizeOf_nil :
    callDataSizeOf [] = 0 := rfl


-- @@ L30-31 verbatim
theorem callDataSizeOf_eq_length (data : List (BitVec 8)) :
    callDataSizeOf data = BitVec.ofNat 256 data.length := rfl


-- @@ L33-35 verbatim
theorem callDataSizeOf_cons (b : BitVec 8) (data : List (BitVec 8)) :
    callDataSizeOf (b :: data) = callDataSizeWord (data.length + 1) := by
  simp [callDataSizeOf, callDataSizeWord, Nat.add_comm]


-- @@ L37-39 verbatim
theorem callDataSizeOf_append (xs ys : List (BitVec 8)) :
    callDataSizeOf (xs ++ ys) = callDataSizeWord (xs.length + ys.length) := by
  simp [callDataSizeOf, callDataSizeWord, List.length_append]


-- @@ L41-43 verbatim
theorem callDataSizeOf_append_nil (xs : List (BitVec 8)) :
    callDataSizeOf (xs ++ []) = callDataSizeOf xs := by
  simp [callDataSizeOf]


-- @@ L45-45 verbatim
end Calldata

-- @@ L46-46 verbatim
end EvmAsm.Evm64
