/-
  EvmAsm.Evm64.ReturnDataHandlers

  Pure RETURNDATASIZE handler-table entry for the interpreter handler layer
  (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace ReturnDataHandlers


-- @@ L18-20 verbatim
/-- EVM word pushed by RETURNDATASIZE for the current abstract state. -/
def returnDataSizeWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.env.returnDataSize.toNat


-- @@ L22-24 verbatim
/-- RETURNDATASIZE pushes the current returndata buffer length in bytes. -/
def returnDataSizeHandler : OpcodeHandler :=
  fun state => state.withStack (returnDataSizeWord state :: state.stack)


-- @@ L26-29 verbatim
/-- Lookup just the returndata handler introduced in this slice. -/
def returnDataHandler? : EvmOpcode → Option OpcodeHandler
  | .RETURNDATASIZE => some returnDataSizeHandler
  | _ => none


-- @@ L31-34 verbatim
/-- Handler table fragment containing the RETURNDATASIZE entry.
    Distinctive token: ReturnDataHandlers.returnDataSizeHandlerTable #107. -/
def returnDataSizeHandlerTable : HandlerTable :=
  returnDataHandler?


-- @@ L36-37 verbatim
@[simp] theorem returnDataHandler?_RETURNDATASIZE :
    returnDataHandler? .RETURNDATASIZE = some returnDataSizeHandler := rfl


-- @@ L39-41 verbatim
@[simp] theorem eq_returnDataSizeHandler_iff (handler : OpcodeHandler) :
    returnDataSizeHandler = handler ↔ handler = returnDataSizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L43-47 verbatim
theorem returnDataHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    returnDataHandler? opcode = some handler ↔
      opcode = .RETURNDATASIZE ∧ handler = returnDataSizeHandler := by
  cases opcode <;> simp [returnDataHandler?]


-- @@ L49-52 verbatim
theorem returnDataHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    returnDataHandler? opcode = none ↔ opcode ≠ .RETURNDATASIZE := by
  cases opcode <;> simp [returnDataHandler?]


-- @@ L54-56 verbatim
@[simp] theorem returnDataSizeHandler_stack (state : EvmState) :
    (returnDataSizeHandler state).stack =
      returnDataSizeWord state :: state.stack := rfl


-- @@ L58-59 verbatim
@[simp] theorem returnDataSizeHandler_status (state : EvmState) :
    (returnDataSizeHandler state).status = state.status := rfl


-- @@ L61-62 verbatim
@[simp] theorem returnDataSizeHandler_env (state : EvmState) :
    (returnDataSizeHandler state).env = state.env := rfl


-- @@ L64-66 verbatim
@[simp] theorem returnDataSizeHandlerTable_RETURNDATASIZE :
    returnDataSizeHandlerTable .RETURNDATASIZE =
      some returnDataSizeHandler := rfl


-- @@ L68-72 verbatim
@[simp] theorem dispatchOpcode?_returnDataSizeHandlerTable_RETURNDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? returnDataSizeHandlerTable .RETURNDATASIZE state =
      some (returnDataSizeHandler state) := by
  simp [HandlerTable.dispatchOpcode?]


-- @@ L74-78 verbatim
@[simp] theorem dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode returnDataSizeHandlerTable .RETURNDATASIZE state =
      returnDataSizeHandler state := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L80-85 verbatim
theorem dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode returnDataSizeHandlerTable .RETURNDATASIZE state).status =
      state.status := by
  rw [dispatchOpcode_returnDataSizeHandlerTable_RETURNDATASIZE state]
  exact returnDataSizeHandler_status state


-- @@ L87-87 verbatim
end ReturnDataHandlers


-- @@ L89-89 verbatim
end EvmAsm.Evm64
