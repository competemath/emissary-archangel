/-
  EvmAsm.Evm64.TerminatingHandlers

  Pure handler-table entries for terminating opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace TerminatingHandlers


-- @@ L16-18 verbatim
/-- STOP handler: terminate successfully without returndata. -/
def stopHandler : OpcodeHandler :=
  fun state => state.stop


-- @@ L20-22 verbatim
/-- INVALID handler: terminate with an error status. -/
def invalidHandler : OpcodeHandler :=
  fun state => state.invalid


-- @@ L24-30 verbatim
/-- Lookup surface for terminating opcodes that already need no additional
    stack or memory arguments. RETURN/REVERT/SELFDESTRUCT need separate
    argument bridges, so this first table only installs STOP and INVALID. -/
def terminatingHandler? : EvmOpcode → Option OpcodeHandler
  | .STOP => some stopHandler
  | .INVALID => some invalidHandler
  | _ => none


-- @@ L32-36 verbatim
/-- Handler table containing the currently argument-free terminating handlers. -/
def terminatingHandlerTable : HandlerTable :=
  HandlerTable.setHandler
    (HandlerTable.setHandler HandlerTable.empty .STOP stopHandler)
    .INVALID invalidHandler


-- @@ L38-39 verbatim
@[simp] theorem terminatingHandler?_STOP :
    terminatingHandler? .STOP = some stopHandler := rfl


-- @@ L41-42 verbatim
@[simp] theorem terminatingHandler?_INVALID :
    terminatingHandler? .INVALID = some invalidHandler := rfl


-- @@ L44-46 verbatim
@[simp] theorem eq_stopHandler_iff (handler : OpcodeHandler) :
    stopHandler = handler ↔ handler = stopHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L48-50 verbatim
@[simp] theorem eq_invalidHandler_iff (handler : OpcodeHandler) :
    invalidHandler = handler ↔ handler = invalidHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L52-57 verbatim
theorem terminatingHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    terminatingHandler? opcode = some handler ↔
      (opcode = .STOP ∧ handler = stopHandler) ∨
        (opcode = .INVALID ∧ handler = invalidHandler) := by
  cases opcode <;> simp [terminatingHandler?]


-- @@ L59-63 verbatim
theorem terminatingHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    terminatingHandler? opcode = none ↔
      opcode ≠ .STOP ∧ opcode ≠ .INVALID := by
  cases opcode <;> simp [terminatingHandler?]


-- @@ L65-66 verbatim
@[simp] theorem stopHandler_status (state : EvmState) :
    (stopHandler state).status = .stopped := rfl


-- @@ L68-69 verbatim
@[simp] theorem invalidHandler_status (state : EvmState) :
    (invalidHandler state).status = .error := rfl


-- @@ L71-73 verbatim
@[simp] theorem terminatingHandlerTable_STOP :
    terminatingHandlerTable .STOP = some stopHandler := by
  simp [terminatingHandlerTable, HandlerTable.setHandler]


-- @@ L75-77 verbatim
@[simp] theorem terminatingHandlerTable_INVALID :
    terminatingHandlerTable .INVALID = some invalidHandler := by
  simp [terminatingHandlerTable, HandlerTable.setHandler]


-- @@ L79-83 verbatim
@[simp] theorem dispatchOpcode?_terminatingHandlerTable_STOP
    (state : EvmState) :
    HandlerTable.dispatchOpcode? terminatingHandlerTable .STOP state =
      some (state.stop) := by
  simp [HandlerTable.dispatchOpcode?, stopHandler]


-- @@ L85-89 verbatim
@[simp] theorem dispatchOpcode_terminatingHandlerTable_STOP
    (state : EvmState) :
    HandlerTable.dispatchOpcode terminatingHandlerTable .STOP state =
      state.stop := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L91-95 verbatim
@[simp] theorem dispatchOpcode?_terminatingHandlerTable_INVALID
    (state : EvmState) :
    HandlerTable.dispatchOpcode? terminatingHandlerTable .INVALID state =
      some (state.invalid) := by
  simp [HandlerTable.dispatchOpcode?, invalidHandler]


-- @@ L97-101 verbatim
@[simp] theorem dispatchOpcode_terminatingHandlerTable_INVALID
    (state : EvmState) :
    HandlerTable.dispatchOpcode terminatingHandlerTable .INVALID state =
      state.invalid := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L103-107 verbatim
@[simp] theorem dispatchOpcode_terminatingHandlerTable_STOP_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode terminatingHandlerTable .STOP state).status =
      .stopped := by
  simp


-- @@ L109-113 verbatim
@[simp] theorem dispatchOpcode_terminatingHandlerTable_INVALID_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode terminatingHandlerTable .INVALID state).status =
      .error := by
  simp


-- @@ L115-115 verbatim
end TerminatingHandlers

-- @@ L116-116 verbatim
end EvmAsm.Evm64
