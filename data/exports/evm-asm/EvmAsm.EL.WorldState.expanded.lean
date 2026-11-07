/-
  EvmAsm.EL.WorldState

  Pure Ethereum world-state model (GH #123 slice 1). This module deliberately
  has no RISC-V dependency; later Evm64 storage/syscall slices can bridge this
  model to concrete ECALL interfaces and separation-logic assertions.
-/

module


-- @@ L11-11 verbatim
public section

-- @@ L12-12 verbatim
namespace EvmAsm.EL


-- @@ L14-14 verbatim
abbrev Byte := BitVec 8

-- @@ L15-15 verbatim
abbrev Address := BitVec 160

-- @@ L16-16 verbatim
abbrev Word256 := BitVec 256

-- @@ L17-17 verbatim
abbrev Hash256 := BitVec 256

-- @@ L18-18 verbatim
abbrev StorageKey := Word256


-- @@ L20-29 verbatim
/-- Ethereum account data relevant to the execution layer. Code bytes are kept
    with the account so CREATE/CALL-family slices can relate code hashes to the
    executable code region later. -/
structure Account where
  nonce : Nat
  balance : Word256
  storageRoot : Hash256
  codeHash : Hash256
  code : List Byte
  deriving Repr


-- @@ L31-31 verbatim
end EvmAsm.EL
