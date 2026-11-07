/-
  EvmAsm.Evm64.CalldataHandlers

  Pure handler-table entries for calldata opcodes currently exposed by
  `EvmState` (GH #104 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Calldata.Size


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace CalldataHandlers


-- @@ L18-24 verbatim
/-- Pure CALLDATASIZE handler. The interpreter state already carries the
    calldata length in `env.callDataLen`; gas and PC charging belong to later
    wrapper layers. -/
def callDataSizeHandler : OpcodeHandler :=
  fun state =>
    state.withStack
      (Calldata.callDataSizeWord state.env.callDataLen.toNat :: state.stack)


-- @@ L26-31 verbatim
/-- Lookup surface for calldata opcode handlers currently supported at the
    pure `EvmState` level. Distinctive token:
    CalldataHandlers.callDataSizeHandlerTable #104 #107. -/
def calldataHandler? : EvmOpcode → Option OpcodeHandler
  | .CALLDATASIZE => some callDataSizeHandler
  | _ => none


-- @@ L33-35 verbatim
/-- Handler table containing currently supported calldata opcode entries. -/
def calldataHandlerTable : HandlerTable :=
  calldataHandler?


-- @@ L37-39 verbatim
@[simp] theorem callDataSizeHandler_stack (state : EvmState) :
    (callDataSizeHandler state).stack =
      Calldata.callDataSizeWord state.env.callDataLen.toNat :: state.stack := rfl


-- @@ L41-42 verbatim
@[simp] theorem callDataSizeHandler_status (state : EvmState) :
    (callDataSizeHandler state).status = state.status := rfl


-- @@ L44-45 verbatim
@[simp] theorem callDataSizeHandler_env (state : EvmState) :
    (callDataSizeHandler state).env = state.env := rfl


-- @@ L47-48 verbatim
@[simp] theorem calldataHandlerTable_eq :
    calldataHandlerTable = calldataHandler? := rfl


-- @@ L50-51 verbatim
@[simp] theorem calldataHandler?_CALLDATASIZE :
    calldataHandler? .CALLDATASIZE = some callDataSizeHandler := rfl


-- @@ L53-55 verbatim
@[simp] theorem eq_callDataSizeHandler_iff (handler : OpcodeHandler) :
    callDataSizeHandler = handler ↔ handler = callDataSizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L57-61 verbatim
theorem calldataHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    calldataHandler? opcode = some handler ↔
      opcode = .CALLDATASIZE ∧ handler = callDataSizeHandler := by
  cases opcode <;> simp [calldataHandler?]


-- @@ L63-66 verbatim
theorem calldataHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    calldataHandler? opcode = none ↔ opcode ≠ .CALLDATASIZE := by
  cases opcode <;> simp [calldataHandler?]


-- @@ L68-69 verbatim
@[simp] theorem calldataHandlerTable_CALLDATASIZE :
    calldataHandlerTable .CALLDATASIZE = some callDataSizeHandler := rfl


-- @@ L71-76 verbatim
theorem dispatchOpcode?_calldataHandlerTable_CALLDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? calldataHandlerTable .CALLDATASIZE state =
      some (callDataSizeHandler state) := by
  exact HandlerTable.dispatchOpcode?_some
    calldataHandlerTable_CALLDATASIZE state


-- @@ L78-83 verbatim
theorem dispatchOpcode_calldataHandlerTable_CALLDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode calldataHandlerTable .CALLDATASIZE state =
      callDataSizeHandler state := by
  exact HandlerTable.dispatchOpcode_some
    calldataHandlerTable_CALLDATASIZE state


-- @@ L85-90 verbatim
theorem dispatchOpcode_calldataHandlerTable_CALLDATASIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode calldataHandlerTable .CALLDATASIZE state).status =
      state.status := by
  rw [dispatchOpcode_calldataHandlerTable_CALLDATASIZE state]
  exact callDataSizeHandler_status state


-- @@ L92-92 verbatim
end CalldataHandlers

-- @@ L93-93 verbatim
end EvmAsm.Evm64
