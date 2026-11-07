/-
  EvmAsm.Evm64.PushHandlers

  Pure PUSH1-32 handler entries for the interpreter handler table
  (GH #101 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Push.ExecEffect


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64


-- @@ L17-17 verbatim
namespace PushHandlers


-- @@ L19-25 verbatim
/-- PUSHn handler over the abstract interpreter state. The handler uses the
    executable PUSH immediate bridge and advances the EVM PC by 1+n. -/
def pushHandler (n : Nat) : OpcodeHandler :=
  fun state =>
    (state.withPc
      (PushExecEffect.pcAfterPushFromCode state.code state.pc n)).withStack
      (PushExecEffect.stackAfterPush state.code state.pc n state.stack)


-- @@ L27-35 verbatim
/-- Lookup surface for generic PUSH1-32 handlers. Invalid widths stay
    unimplemented rather than installing nonsensical handlers. -/
def pushHandler? : EvmOpcode → Option OpcodeHandler
  | .PUSH n =>
      if EvmOpcode.validPushWidth n then
        some (pushHandler n)
      else
        none
  | _ => none


-- @@ L37-40 verbatim
/-- Handler table containing the generic PUSH1-32 entries.
    Distinctive token: PushHandlers.pushHandlerTable #101 #107. -/
def pushHandlerTable : HandlerTable :=
  pushHandler?


-- @@ L42-43 verbatim
@[simp] theorem pushHandlerTable_eq :
    pushHandlerTable = pushHandler? := rfl


-- @@ L45-48 verbatim
theorem pushHandler?_PUSH_of_valid {n : Nat}
    (h_valid : EvmOpcode.validPushWidth n = true) :
    pushHandler? (.PUSH n) = some (pushHandler n) := by
  simp [pushHandler?, h_valid]


-- @@ L50-53 verbatim
theorem pushHandler?_PUSH_of_invalid {n : Nat}
    (h_valid : EvmOpcode.validPushWidth n = false) :
    pushHandler? (.PUSH n) = none := by
  simp [pushHandler?, h_valid]


-- @@ L55-57 verbatim
@[simp] theorem eq_pushHandler_iff (n : Nat) (handler : OpcodeHandler) :
    pushHandler n = handler ↔ handler = pushHandler n := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L59-64 verbatim
theorem pushHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    pushHandler? opcode = some handler ↔
      ∃ n, opcode = .PUSH n ∧ EvmOpcode.validPushWidth n = true ∧
        handler = pushHandler n := by
  cases opcode <;> simp [pushHandler?]


-- @@ L66-70 verbatim
theorem pushHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    pushHandler? opcode = none ↔
      ∀ n, opcode = .PUSH n → EvmOpcode.validPushWidth n = false := by
  cases opcode <;> simp [pushHandler?]


-- @@ L72-74 verbatim
@[simp] theorem pushHandler_stack (n : Nat) (state : EvmState) :
    (pushHandler n state).stack =
      PushExecEffect.stackAfterPush state.code state.pc n state.stack := rfl


-- @@ L76-78 verbatim
@[simp] theorem pushHandler_pc (n : Nat) (state : EvmState) :
    (pushHandler n state).pc =
      PushExecEffect.pcAfterPushFromCode state.code state.pc n := rfl


-- @@ L80-81 verbatim
@[simp] theorem pushHandler_status (n : Nat) (state : EvmState) :
    (pushHandler n state).status = state.status := rfl


-- @@ L83-86 verbatim
theorem pushHandler_stack_eq
    (n : Nat) (state : EvmState) :
    (pushHandler n state).stack =
      PushExecEffect.pushedWordFromCode state.code state.pc n :: state.stack := rfl


-- @@ L88-90 verbatim
theorem pushHandler_pc_eq
    (n : Nat) (state : EvmState) :
    (pushHandler n state).pc = state.pc + 1 + n := rfl


-- @@ L92-105 verbatim
/--
The pure PUSH handler updates the interpreter state with the same stack and
program-counter components as the bundled executable PUSH effect.

Distinctive token:
PushHandlers.pushHandler_eq_effectFromCode #101 #107.
-/
theorem pushHandler_eq_effectFromCode
    (n : Nat) (state : EvmState) :
    (pushHandler n state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (pushHandler n state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  constructor <;> rfl


-- @@ L107-113 verbatim
theorem dispatchOpcode?_pushHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode? pushHandlerTable (.PUSH n) state =
      some (pushHandler n state) := by
  exact HandlerTable.dispatchOpcode?_some
    (pushHandler?_PUSH_of_valid h_valid) state


-- @@ L115-121 verbatim
theorem dispatchOpcode_pushHandlerTable_PUSH_of_valid
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    HandlerTable.dispatchOpcode pushHandlerTable (.PUSH n) state =
      pushHandler n state := by
  exact HandlerTable.dispatchOpcode_some
    (pushHandler?_PUSH_of_valid h_valid) state


-- @@ L123-129 verbatim
theorem dispatchOpcode_pushHandlerTable_PUSH_of_valid_status
    {n : Nat} (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchOpcode pushHandlerTable (.PUSH n) state).status =
      state.status := by
  rw [dispatchOpcode_pushHandlerTable_PUSH_of_valid h_valid state]
  exact pushHandler_status n state


-- @@ L131-131 verbatim
end PushHandlers


-- @@ L133-133 verbatim
end EvmAsm.Evm64
