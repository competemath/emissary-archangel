/-
  EvmAsm.Evm64.ControlHandlers

  Pure PC/GAS/JUMPDEST handler entries for the interpreter handler table
  (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
namespace ControlHandlers


-- @@ L18-20 verbatim
/-- EVM word pushed by the PC opcode for the current abstract state. -/
def pcWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.pc


-- @@ L22-24 verbatim
/-- EVM word pushed by the GAS opcode for the current abstract state. -/
def gasWord (state : EvmState) : EvmWord :=
  BitVec.ofNat 256 state.gas


-- @@ L26-28 verbatim
/-- PC pushes the current EVM program counter. -/
def pcHandler : OpcodeHandler :=
  fun state => state.withStack (pcWord state :: state.stack)


-- @@ L30-32 verbatim
/-- GAS pushes the current remaining-gas counter. -/
def gasHandler : OpcodeHandler :=
  fun state => state.withStack (gasWord state :: state.stack)


-- @@ L34-36 verbatim
/-- JUMPDEST is a marker opcode and leaves the abstract state unchanged. -/
def jumpdestHandler : OpcodeHandler :=
  fun state => state


-- @@ L38-43 verbatim
/-- Lookup just the control/metadata handlers introduced in this slice. -/
def controlHandler? : EvmOpcode → Option OpcodeHandler
  | .PC => some pcHandler
  | .GAS => some gasHandler
  | .JUMPDEST => some jumpdestHandler
  | _ => none


-- @@ L45-47 verbatim
@[simp] theorem eq_pcHandler_iff (handler : OpcodeHandler) :
    pcHandler = handler ↔ handler = pcHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L49-51 verbatim
@[simp] theorem eq_gasHandler_iff (handler : OpcodeHandler) :
    gasHandler = handler ↔ handler = gasHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L53-55 verbatim
@[simp] theorem eq_jumpdestHandler_iff (handler : OpcodeHandler) :
    jumpdestHandler = handler ↔ handler = jumpdestHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L57-60 verbatim
/-- Handler table fragment containing PC, GAS, and JUMPDEST entries.
    Distinctive token: ControlHandlers.controlHandlerTable #107. -/
def controlHandlerTable : HandlerTable :=
  controlHandler?


-- @@ L62-63 verbatim
@[simp] theorem controlHandler?_PC :
    controlHandler? .PC = some pcHandler := rfl


-- @@ L65-66 verbatim
@[simp] theorem controlHandler?_GAS :
    controlHandler? .GAS = some gasHandler := rfl


-- @@ L68-69 verbatim
@[simp] theorem controlHandler?_JUMPDEST :
    controlHandler? .JUMPDEST = some jumpdestHandler := rfl


-- @@ L71-77 verbatim
theorem controlHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    controlHandler? opcode = some handler ↔
      (opcode = .PC ∧ handler = pcHandler) ∨
        (opcode = .GAS ∧ handler = gasHandler) ∨
          (opcode = .JUMPDEST ∧ handler = jumpdestHandler) := by
  cases opcode <;> simp [controlHandler?]


-- @@ L79-83 verbatim
theorem controlHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    controlHandler? opcode = none ↔
      opcode ≠ .PC ∧ opcode ≠ .GAS ∧ opcode ≠ .JUMPDEST := by
  cases opcode <;> simp [controlHandler?]


-- @@ L85-86 verbatim
@[simp] theorem pcHandler_stack (state : EvmState) :
    (pcHandler state).stack = pcWord state :: state.stack := rfl


-- @@ L88-89 verbatim
@[simp] theorem gasHandler_stack (state : EvmState) :
    (gasHandler state).stack = gasWord state :: state.stack := rfl


-- @@ L91-92 verbatim
@[simp] theorem jumpdestHandler_eq (state : EvmState) :
    jumpdestHandler state = state := rfl


-- @@ L94-95 verbatim
@[simp] theorem pcHandler_status (state : EvmState) :
    (pcHandler state).status = state.status := rfl


-- @@ L97-98 verbatim
@[simp] theorem gasHandler_status (state : EvmState) :
    (gasHandler state).status = state.status := rfl


-- @@ L100-101 verbatim
@[simp] theorem controlHandlerTable_PC :
    controlHandlerTable .PC = some pcHandler := rfl


-- @@ L103-104 verbatim
@[simp] theorem controlHandlerTable_GAS :
    controlHandlerTable .GAS = some gasHandler := rfl


-- @@ L106-107 verbatim
@[simp] theorem controlHandlerTable_JUMPDEST :
    controlHandlerTable .JUMPDEST = some jumpdestHandler := rfl


-- @@ L109-112 verbatim
@[simp] theorem dispatchOpcode?_controlHandlerTable_PC (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .PC state =
      some (pcHandler state) := by
  simp [HandlerTable.dispatchOpcode?]


-- @@ L114-117 verbatim
@[simp] theorem dispatchOpcode_controlHandlerTable_PC (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .PC state =
      pcHandler state := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L119-122 verbatim
@[simp] theorem dispatchOpcode?_controlHandlerTable_GAS (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .GAS state =
      some (gasHandler state) := by
  simp [HandlerTable.dispatchOpcode?]


-- @@ L124-127 verbatim
@[simp] theorem dispatchOpcode_controlHandlerTable_GAS (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .GAS state =
      gasHandler state := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L129-132 verbatim
@[simp] theorem dispatchOpcode?_controlHandlerTable_JUMPDEST (state : EvmState) :
    HandlerTable.dispatchOpcode? controlHandlerTable .JUMPDEST state =
      some (jumpdestHandler state) := by
  simp [HandlerTable.dispatchOpcode?]


-- @@ L134-137 verbatim
@[simp] theorem dispatchOpcode_controlHandlerTable_JUMPDEST (state : EvmState) :
    HandlerTable.dispatchOpcode controlHandlerTable .JUMPDEST state =
      jumpdestHandler state := by
  simp [HandlerTable.dispatchOpcode]


-- @@ L139-143 verbatim
theorem dispatchOpcode_controlHandlerTable_PC_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .PC state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_PC state]
  exact pcHandler_status state


-- @@ L145-149 verbatim
theorem dispatchOpcode_controlHandlerTable_GAS_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .GAS state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_GAS state]
  exact gasHandler_status state


-- @@ L151-155 verbatim
theorem dispatchOpcode_controlHandlerTable_JUMPDEST_status (state : EvmState) :
    (HandlerTable.dispatchOpcode controlHandlerTable .JUMPDEST state).status =
      state.status := by
  rw [dispatchOpcode_controlHandlerTable_JUMPDEST state]
  rfl


-- @@ L157-157 verbatim
end ControlHandlers


-- @@ L159-159 verbatim
end EvmAsm.Evm64
