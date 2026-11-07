/-
  EvmAsm.EL.MessageCallExecution

  Pure execution hooks for message-call processing (GH #121).
-/

module

public import EvmAsm.EL.Logs
public import EvmAsm.EL.MessageCall


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace MessageCallExecution

-- @@ L17-24 verbatim
/-- Side effects surfaced by the executable-spec `MessageCallOutput`. The
    output bytes and committed state remain in `CallResult`/`CallerVisibleResult`;
    this record tracks the auxiliary effects that are cleared on errors. -/
structure CallSideEffects where
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address


-- @@ L26-30 verbatim
def empty : CallSideEffects :=
  { refundCounter := 0
    logs := LogState.empty
    accountsToDelete := []
    touchedAccounts := [] }


-- @@ L32-32 verbatim
@[simp] theorem refundCounter_empty : empty.refundCounter = 0 := rfl

-- @@ L33-33 verbatim
@[simp] theorem logs_empty : empty.logs = LogState.empty := rfl

-- @@ L34-34 verbatim
@[simp] theorem accountsToDelete_empty : empty.accountsToDelete = [] := rfl

-- @@ L35-35 verbatim
@[simp] theorem touchedAccounts_empty : empty.touchedAccounts = [] := rfl



-- @@ L38-46 verbatim
/-- Executable-spec-shaped message-call output surface. Mirrors the Python
    `MessageCallOutput` fields while using `status` as the Lean error summary. -/
structure MessageCallOutput where
  gasLeft : Nat
  refundCounter : Nat
  logs : LogState
  accountsToDelete : List Address
  touchedAccounts : List Address
  status : CallStatus


-- @@ L48-48 verbatim
end MessageCallExecution


-- @@ L50-50 verbatim
end EvmAsm.EL
