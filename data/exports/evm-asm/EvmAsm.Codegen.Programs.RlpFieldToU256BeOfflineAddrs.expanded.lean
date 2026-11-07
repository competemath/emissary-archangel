/-
  EvmAsm.Codegen.Programs.RlpFieldToU256BeOfflineAddrs

  Last-linked entry address for `rlp_field_to_u256_be`, retired from the
  production guest in #12386 after an ELF call-graph audit found no callers.
  The proof modules keep checking the Program against this ghost base; it is
  deliberately not a `GuestAddrs` pin and must not be re-linked.
-/

module


-- @@ L12-12 verbatim
@[expose] public section

-- @@ L13-13 verbatim
namespace EvmAsm.Codegen.RlpFieldToU256BeOfflineAddrs


-- @@ L15-16 verbatim
/-- Last linked entry of `rlp_field_to_u256_be` before #12386. -/
def rlp_field_to_u256_be : Nat := 0x80003fcc


-- @@ L18-18 verbatim
end EvmAsm.Codegen.RlpFieldToU256BeOfflineAddrs
