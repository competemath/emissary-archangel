/-
  EvmAsm.EL.TerminatingArgsBridge

  Bridge from EVM RETURN/REVERT stack arguments to EL message-call results
  (GH #113).

  Mirrors the shape of `EvmAsm.EL.LogArgsBridge` and
  `EvmAsm.EL.CallArgsBridge`: a tiny pure layer that takes the loaded data
  byte slice, the post-execution `WorldState`, and the remaining gas, and
  produces a `CallResult` with the appropriate `CallStatus` (`.success` for
  RETURN, `.revert` for REVERT). The actual memory-load / state-update work
  belongs to the eventual handler specs — this bridge just packages the
  result.
-/

module

public import EvmAsm.EL.MessageCall
public import EvmAsm.Evm64.TerminatingArgs


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace EvmAsm.EL


-- @@ L25-25 verbatim
namespace TerminatingArgsBridge


-- @@ L27-27 verbatim
abbrev MemoryRange := EvmAsm.Evm64.TerminatingArgs.MemoryRange

-- @@ L28-28 verbatim
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args

-- @@ L29-29 verbatim
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind


-- @@ L31-33 verbatim
/-- Memory range projected from the terminating-args record. -/
def dataRange (args : TerminatingArgs) : MemoryRange :=
  EvmAsm.Evm64.TerminatingArgs.dataRange args


-- @@ L35-35 verbatim
end TerminatingArgsBridge


-- @@ L37-37 verbatim
end EvmAsm.EL
