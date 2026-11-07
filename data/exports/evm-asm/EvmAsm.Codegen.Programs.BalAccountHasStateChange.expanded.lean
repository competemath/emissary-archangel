/-
  EvmAsm.Codegen.Programs.BalAccountHasStateChange

  Cheap BAL AccountChanges classifier for post-state-root replay.

  GH #10753 bridge module: the program itself lives in the leaf
  `BalAccountHasStateChangeProg.lean` parameterised over the abstract `GuestLayout`;
  this module applies the concrete `guestLayout` and re-exposes
  `balAccountHasStateChange_prog` with its original name and type, so every consumer
  (and the concrete-render drift gate, whose key is `emitProgram`
  `balAccountHasStateChange_prog`) compiles unchanged.
-/

module

public import EvmAsm.Rv64.Program
public import EvmAsm.Codegen.Emit
public import EvmAsm.Codegen.Programs.BalAccountHasStateChangeProg
public import EvmAsm.Codegen.GuestLayoutInstance


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.Codegen


-- @@ L25-25 verbatim
open EvmAsm.Rv64


-- @@ L27-35 verbatim
/-! ## bal_account_has_state_change -- detect state-affecting BAL rows

    a0 = AccountChanges RLP ptr   a1 = AccountChanges length
    a0 (output) = 0 no post-state change / 1 has post-state change / 2 parse fail.

    AccountChanges fields:
      [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]
    `storage_reads` are read-only, so only fields 1, 3, 4, and 5 can affect the
    post-state root. -/

-- @@ L36-36 verbatim
def balAccountHasStateChange_prog : Program := balAccountHasStateChange_prog_of guestLayout


-- @@ L38-39 verbatim
def ziskBalAccountHasStateChangeDataSection : String :=
  ".balign 8\n"


-- @@ L41-41 verbatim
end EvmAsm.Codegen
