/-
  EvmAsm.Evm64.MemoryHandlers

  Pure memory-metadata handler-table entries for the interpreter handler
  layer (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace MemoryHandlers


-- @@ L18-20 verbatim
/-- EVM word pushed by MSIZE for the current abstract state. -/
def msizeWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.memSize


-- @@ L22-24 verbatim
/-- MSIZE pushes the current EVM memory high-water mark in bytes. -/
def msizeHandler : OpcodeHandler :=
  fun state => state.withStack (msizeWord state :: state.stack)


-- @@ L26-29 verbatim
/-- Lookup just the memory-metadata handler introduced in this slice. -/
def memoryHandler? : EvmOpcode → Option OpcodeHandler
  | .MSIZE => some msizeHandler
  | _ => none


-- @@ L31-34 verbatim
/-- Handler table fragment containing the MSIZE entry.
    Distinctive token: MemoryHandlers.msizeHandlerTable #107. -/
def msizeHandlerTable : HandlerTable :=
  memoryHandler?


-- @@ L36-37 verbatim
@[simp] theorem memoryHandler?_MSIZE :
    memoryHandler? .MSIZE = some msizeHandler := rfl


-- @@ L39-41 verbatim
@[simp] theorem eq_msizeHandler_iff (handler : OpcodeHandler) :
    msizeHandler = handler ↔ handler = msizeHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L43-47 verbatim
theorem memoryHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    memoryHandler? opcode = some handler ↔
      opcode = .MSIZE ∧ handler = msizeHandler := by
  cases opcode <;> simp [memoryHandler?]


-- @@ L49-52 verbatim
theorem memoryHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    memoryHandler? opcode = none ↔ opcode ≠ .MSIZE := by
  cases opcode <;> simp [memoryHandler?]


-- @@ L54-55 verbatim
@[simp] theorem msizeHandler_stack (state : EvmState) :
    (msizeHandler state).stack = msizeWord state :: state.stack := rfl


-- @@ L57-58 verbatim
@[simp] theorem msizeHandler_status (state : EvmState) :
    (msizeHandler state).status = state.status := rfl


-- @@ L60-61 verbatim
@[simp] theorem msizeHandler_memSize (state : EvmState) :
    (msizeHandler state).memSize = state.memSize := rfl


-- @@ L63-64 verbatim
@[simp] theorem msizeHandlerTable_MSIZE :
    msizeHandlerTable .MSIZE = some msizeHandler := rfl


-- @@ L66-70 verbatim
@[simp] theorem dispatchOpcode?_msizeHandlerTable_MSIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode? msizeHandlerTable .MSIZE state =
      some (msizeHandler state) := by
  simp [HandlerTable.dispatchOpcode?]


-- @@ L72-76 verbatim
@[simp] theorem dispatchOpcode_msizeHandlerTable_MSIZE
    (state : EvmState) :
    HandlerTable.dispatchOpcode msizeHandlerTable .MSIZE state =
      msizeHandler state := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L78-83 verbatim
theorem dispatchOpcode_msizeHandlerTable_MSIZE_status
    (state : EvmState) :
    (HandlerTable.dispatchOpcode msizeHandlerTable .MSIZE state).status =
      state.status := by
  rw [dispatchOpcode_msizeHandlerTable_MSIZE state]
  exact msizeHandler_status state


-- @@ L85-85 verbatim
end MemoryHandlers


-- @@ L87-87 verbatim
end EvmAsm.Evm64
