/-
  EvmAsm.Evm64.ArithmeticHandlers

  Pure handler-table entries for basic arithmetic opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.EvmWordArith.SDiv
public import EvmAsm.Evm64.EvmWordArith.SMod


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64

-- @@ L16-16 verbatim
namespace ArithmeticHandlers


-- @@ L18-24 verbatim
/-- Pure stack transform for binary arithmetic opcodes. Operand order matches
    the existing stack specs: top word `a`, next word `b`, result `op a b`. -/
def binaryStack? (op : EvmWord → EvmWord → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: b :: rest => some (op a b :: rest)
  | _ => none


-- @@ L26-31 verbatim
/-- Generic binary arithmetic handler over the abstract interpreter state. -/
def binaryHandler (op : EvmWord → EvmWord → EvmWord) : OpcodeHandler :=
  fun state =>
    match binaryStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L33-34 verbatim
def addHandler : OpcodeHandler :=
  binaryHandler (fun a b => a + b)


-- @@ L36-37 verbatim
def subHandler : OpcodeHandler :=
  binaryHandler (fun a b => a - b)


-- @@ L39-40 verbatim
def mulHandler : OpcodeHandler :=
  binaryHandler (fun a b => a * b)


-- @@ L42-43 verbatim
def sdivHandler : OpcodeHandler :=
  binaryHandler EvmWord.sdiv


-- @@ L45-46 verbatim
def smodHandler : OpcodeHandler :=
  binaryHandler EvmWord.smod


-- @@ L48-55 verbatim
/-- Lookup surface for the arithmetic handlers proved so far. -/
def arithmeticHandler? : EvmOpcode → Option OpcodeHandler
  | .ADD => some addHandler
  | .SUB => some subHandler
  | .MUL => some mulHandler
  | .SDIV => some sdivHandler
  | .SMOD => some smodHandler
  | _ => none


-- @@ L57-60 verbatim
/-- Handler table containing currently supported arithmetic entries.
    Distinctive token: ArithmeticHandlers.arithmeticHandlerTable #107. -/
def arithmeticHandlerTable : HandlerTable :=
  arithmeticHandler?


-- @@ L62-65 verbatim
@[simp] theorem binaryStack?_two
    (op : EvmWord → EvmWord → EvmWord)
    (a b : EvmWord) (rest : List EvmWord) :
    binaryStack? op (a :: b :: rest) = some (op a b :: rest) := rfl


-- @@ L67-69 verbatim
@[simp] theorem binaryStack?_nil
    (op : EvmWord → EvmWord → EvmWord) :
    binaryStack? op [] = none := rfl


-- @@ L71-73 verbatim
@[simp] theorem binaryStack?_singleton
    (op : EvmWord → EvmWord → EvmWord) (a : EvmWord) :
    binaryStack? op [a] = none := rfl


-- @@ L75-87 verbatim
theorem binaryStack?_eq_some_iff
    (op : EvmWord → EvmWord → EvmWord)
    (stack stack' : List EvmWord) :
    binaryStack? op stack = some stack' ↔
      ∃ a b rest, stack = a :: b :: rest ∧ stack' = op a b :: rest := by
  constructor
  · intro h_stack
    rcases stack with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
      simp [binaryStack?] at h_stack
    cases h_stack
    exact ⟨a, b, rest, rfl, rfl⟩
  · rintro ⟨a, b, rest, rfl, rfl⟩
    rfl


-- @@ L89-103 verbatim
theorem binaryStack?_eq_none_iff
    (op : EvmWord → EvmWord → EvmWord) (stack : List EvmWord) :
    binaryStack? op stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_stack
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp
    · simp
    · simp [binaryStack?] at h_stack
  · intro h_len
    rcases stack with _ | ⟨_, _ | ⟨_, _⟩⟩
    · rfl
    · rfl
    · simp at h_len
      omega


-- @@ L105-110 verbatim
theorem binaryHandler_stack_of_binaryStack?_some
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    {stack' : List EvmWord}
    (h_stack : binaryStack? op state.stack = some stack') :
    (binaryHandler op state).stack = stack' := by
  simp [binaryHandler, h_stack]


-- @@ L112-116 verbatim
theorem binaryHandler_status_of_binaryStack?_none
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    (h_stack : binaryStack? op state.stack = none) :
    (binaryHandler op state).status = .error := by
  simp [binaryHandler, h_stack]


-- @@ L118-121 verbatim
@[simp] theorem addHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (addHandler { state with stack := a :: b :: rest }).stack =
      (a + b) :: rest := rfl


-- @@ L123-126 verbatim
@[simp] theorem subHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (subHandler { state with stack := a :: b :: rest }).stack =
      (a - b) :: rest := rfl


-- @@ L128-131 verbatim
@[simp] theorem mulHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (mulHandler { state with stack := a :: b :: rest }).stack =
      (a * b) :: rest := rfl


-- @@ L133-136 verbatim
@[simp] theorem sdivHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sdivHandler { state with stack := a :: b :: rest }).stack =
      EvmWord.sdiv a b :: rest := rfl


-- @@ L138-141 verbatim
@[simp] theorem smodHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (smodHandler { state with stack := a :: b :: rest }).stack =
      EvmWord.smod a b :: rest := rfl


-- @@ L143-144 verbatim
@[simp] theorem arithmeticHandlerTable_eq :
    arithmeticHandlerTable = arithmeticHandler? := rfl


-- @@ L146-147 verbatim
@[simp] theorem arithmeticHandler?_ADD :
    arithmeticHandler? .ADD = some addHandler := rfl


-- @@ L149-150 verbatim
@[simp] theorem arithmeticHandler?_SUB :
    arithmeticHandler? .SUB = some subHandler := rfl


-- @@ L152-153 verbatim
@[simp] theorem arithmeticHandler?_MUL :
    arithmeticHandler? .MUL = some mulHandler := rfl


-- @@ L155-156 verbatim
@[simp] theorem arithmeticHandler?_SDIV :
    arithmeticHandler? .SDIV = some sdivHandler := rfl


-- @@ L158-159 verbatim
@[simp] theorem arithmeticHandler?_SMOD :
    arithmeticHandler? .SMOD = some smodHandler := rfl


-- @@ L161-163 verbatim
@[simp] theorem eq_addHandler_iff (handler : OpcodeHandler) :
    addHandler = handler ↔ handler = addHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L165-167 verbatim
@[simp] theorem eq_subHandler_iff (handler : OpcodeHandler) :
    subHandler = handler ↔ handler = subHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L169-171 verbatim
@[simp] theorem eq_mulHandler_iff (handler : OpcodeHandler) :
    mulHandler = handler ↔ handler = mulHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L173-175 verbatim
@[simp] theorem eq_sdivHandler_iff (handler : OpcodeHandler) :
    sdivHandler = handler ↔ handler = sdivHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L177-179 verbatim
@[simp] theorem eq_smodHandler_iff (handler : OpcodeHandler) :
    smodHandler = handler ↔ handler = smodHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L181-189 verbatim
theorem arithmeticHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    arithmeticHandler? opcode = some handler ↔
      (opcode = .ADD ∧ handler = addHandler) ∨
        (opcode = .SUB ∧ handler = subHandler) ∨
          (opcode = .MUL ∧ handler = mulHandler) ∨
            (opcode = .SDIV ∧ handler = sdivHandler) ∨
              (opcode = .SMOD ∧ handler = smodHandler) := by
  cases opcode <;> simp [arithmeticHandler?]


-- @@ L191-196 verbatim
theorem arithmeticHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    arithmeticHandler? opcode = none ↔
      opcode ≠ .ADD ∧ opcode ≠ .SUB ∧ opcode ≠ .MUL ∧
        opcode ≠ .SDIV ∧ opcode ≠ .SMOD := by
  cases opcode <;> simp [arithmeticHandler?]


-- @@ L198-202 verbatim
theorem dispatchOpcode?_arithmeticHandlerTable_ADD
    (state : EvmState) :
    HandlerTable.dispatchOpcode? arithmeticHandlerTable .ADD state =
      some (addHandler state) := by
  exact HandlerTable.dispatchOpcode?_some arithmeticHandler?_ADD state


-- @@ L204-208 verbatim
theorem dispatchOpcode?_arithmeticHandlerTable_SUB
    (state : EvmState) :
    HandlerTable.dispatchOpcode? arithmeticHandlerTable .SUB state =
      some (subHandler state) := by
  exact HandlerTable.dispatchOpcode?_some arithmeticHandler?_SUB state


-- @@ L210-214 verbatim
theorem dispatchOpcode?_arithmeticHandlerTable_MUL
    (state : EvmState) :
    HandlerTable.dispatchOpcode? arithmeticHandlerTable .MUL state =
      some (mulHandler state) := by
  exact HandlerTable.dispatchOpcode?_some arithmeticHandler?_MUL state


-- @@ L216-220 verbatim
theorem dispatchOpcode?_arithmeticHandlerTable_SDIV
    (state : EvmState) :
    HandlerTable.dispatchOpcode? arithmeticHandlerTable .SDIV state =
      some (sdivHandler state) := by
  exact HandlerTable.dispatchOpcode?_some arithmeticHandler?_SDIV state


-- @@ L222-226 verbatim
theorem dispatchOpcode?_arithmeticHandlerTable_SMOD
    (state : EvmState) :
    HandlerTable.dispatchOpcode? arithmeticHandlerTable .SMOD state =
      some (smodHandler state) := by
  exact HandlerTable.dispatchOpcode?_some arithmeticHandler?_SMOD state


-- @@ L228-232 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_ADD
    (state : EvmState) :
    HandlerTable.dispatchOpcode arithmeticHandlerTable .ADD state =
      addHandler state := by
  exact HandlerTable.dispatchOpcode_some arithmeticHandler?_ADD state


-- @@ L234-238 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SUB
    (state : EvmState) :
    HandlerTable.dispatchOpcode arithmeticHandlerTable .SUB state =
      subHandler state := by
  exact HandlerTable.dispatchOpcode_some arithmeticHandler?_SUB state


-- @@ L240-244 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_MUL
    (state : EvmState) :
    HandlerTable.dispatchOpcode arithmeticHandlerTable .MUL state =
      mulHandler state := by
  exact HandlerTable.dispatchOpcode_some arithmeticHandler?_MUL state


-- @@ L246-250 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SDIV
    (state : EvmState) :
    HandlerTable.dispatchOpcode arithmeticHandlerTable .SDIV state =
      sdivHandler state := by
  exact HandlerTable.dispatchOpcode_some arithmeticHandler?_SDIV state


-- @@ L252-256 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SMOD
    (state : EvmState) :
    HandlerTable.dispatchOpcode arithmeticHandlerTable .SMOD state =
      smodHandler state := by
  exact HandlerTable.dispatchOpcode_some arithmeticHandler?_SMOD state


-- @@ L258-264 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_ADD_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a + b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode arithmeticHandlerTable .ADD state).status =
      state.status := by
  rw [dispatchOpcode_arithmeticHandlerTable_ADD state]
  simp [addHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L266-272 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SUB_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a - b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode arithmeticHandlerTable .SUB state).status =
      state.status := by
  rw [dispatchOpcode_arithmeticHandlerTable_SUB state]
  simp [subHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L274-280 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_MUL_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a * b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode arithmeticHandlerTable .MUL state).status =
      state.status := by
  rw [dispatchOpcode_arithmeticHandlerTable_MUL state]
  simp [mulHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L282-288 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SDIV_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? EvmWord.sdiv state.stack = some stack') :
    (HandlerTable.dispatchOpcode arithmeticHandlerTable .SDIV state).status =
      state.status := by
  rw [dispatchOpcode_arithmeticHandlerTable_SDIV state]
  simp [sdivHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L290-296 verbatim
theorem dispatchOpcode_arithmeticHandlerTable_SMOD_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? EvmWord.smod state.stack = some stack') :
    (HandlerTable.dispatchOpcode arithmeticHandlerTable .SMOD state).status =
      state.status := by
  rw [dispatchOpcode_arithmeticHandlerTable_SMOD state]
  simp [smodHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L298-298 verbatim
end ArithmeticHandlers

-- @@ L299-299 verbatim
end EvmAsm.Evm64
