/-
  EvmAsm.Evm64.CodeHandlers

  Pure handler-table entries for code-inspection opcodes currently exposed by
  `EvmState` (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace CodeHandlers


-- @@ L17-20 verbatim
/-- Pure CODESIZE handler. The interpreter state carries the bytecode length
    explicitly as `codeLen`; gas and PC charging belong to later wrappers. -/
def codeSizeHandler : OpcodeHandler :=
  fun state => state.withStack (BitVec.ofNat 256 state.codeLen :: state.stack)


-- @@ L22-27 verbatim
/-- Lookup surface for code-inspection opcode handlers currently supported at
    the pure `EvmState` level. Distinctive token:
    CodeHandlers.codeSizeHandlerTable #107. -/
def codeHandler? : EvmOpcode → Option OpcodeHandler
  | .CODESIZE => some codeSizeHandler
  | _ => none


-- @@ L29-31 verbatim
/-- Handler table containing currently supported code-inspection entries. -/
def codeHandlerTable : HandlerTable :=
  codeHandler?


-- @@ L33-35 verbatim
@[simp] theorem codeSizeHandler_stack (state : EvmState) :
    (codeSizeHandler state).stack =
      BitVec.ofNat 256 state.codeLen :: state.stack := rfl


-- @@ L37-38 verbatim
@[simp] theorem codeSizeHandler_status (state : EvmState) :
    (codeSizeHandler state).status = state.status := rfl


-- @@ L40-41 verbatim
@[simp] theorem codeSizeHandler_code (state : EvmState) :
    (codeSizeHandler state).code = state.code := rfl


-- @@ L43-44 verbatim
@[simp] theorem codeSizeHandler_codeLen (state : EvmState) :
    (codeSizeHandler state).codeLen = state.codeLen := rfl


-- @@ L46-47 verbatim
@[simp] theorem codeHandlerTable_eq :
    codeHandlerTable = codeHandler? := rfl


-- @@ L49-50 verbatim
@[simp] theorem codeHandler?_CODESIZE :
    codeHandler? .CODESIZE = some codeSizeHandler := rfl


-- @@ L52-54 verbatim
@[simp] theorem eq_codeSizeHandler_iff (handler : OpcodeHandler) :
    codeSizeHandler = handler ↔ handler = codeSizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L56-60 verbatim
theorem codeHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    codeHandler? opcode = some handler ↔
      opcode = .CODESIZE ∧ handler = codeSizeHandler := by
  cases opcode <;> simp [codeHandler?]


-- @@ L62-65 verbatim
theorem codeHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    codeHandler? opcode = none ↔ opcode ≠ .CODESIZE := by
  cases opcode <;> simp [codeHandler?]


-- @@ L67-68 verbatim
@[simp] theorem codeHandlerTable_CODESIZE :
    codeHandlerTable .CODESIZE = some codeSizeHandler := rfl


-- @@ L70-75 verbatim
theorem dispatchOpcode?_codeHandlerTable_CODESIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? codeHandlerTable .CODESIZE state =
      some (codeSizeHandler state) := by
  exact HandlerTable.dispatchOpcode?_some
    codeHandlerTable_CODESIZE state


-- @@ L77-82 verbatim
theorem dispatchOpcode_codeHandlerTable_CODESIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode codeHandlerTable .CODESIZE state =
      codeSizeHandler state := by
  exact HandlerTable.dispatchOpcode_some
    codeHandlerTable_CODESIZE state


-- @@ L84-89 verbatim
theorem dispatchOpcode_codeHandlerTable_CODESIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode codeHandlerTable .CODESIZE state).status =
      state.status := by
  rw [dispatchOpcode_codeHandlerTable_CODESIZE state]
  exact codeSizeHandler_status state


-- @@ L91-91 verbatim
end CodeHandlers

-- @@ L92-92 verbatim
end EvmAsm.Evm64
