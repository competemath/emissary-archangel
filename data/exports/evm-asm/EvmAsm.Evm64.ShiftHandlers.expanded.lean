/-
  EvmAsm.Evm64.ShiftHandlers

  Pure handler-table entries for shift opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace ShiftHandlers


-- @@ L16-22 verbatim
/-- Pure stack transform for binary shift opcodes. The top stack word is the
    shift amount; the next word is the shifted value, matching the shift specs. -/
def shiftStack? (op : EvmWord → Nat → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | shift :: value :: rest => some (op value shift.toNat :: rest)
  | _ => none


-- @@ L24-28 verbatim
def shiftHandler (op : EvmWord → Nat → EvmWord) : OpcodeHandler :=
  fun state =>
    match shiftStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L30-31 verbatim
def shlHandler : OpcodeHandler :=
  shiftHandler (fun value n => value <<< n)


-- @@ L33-34 verbatim
def shrHandler : OpcodeHandler :=
  shiftHandler (fun value n => value >>> n)


-- @@ L36-37 verbatim
def sarHandler : OpcodeHandler :=
  shiftHandler (fun value n => BitVec.sshiftRight value n)


-- @@ L39-44 verbatim
/-- Lookup surface for shift handlers. -/
def shiftHandler? : EvmOpcode → Option OpcodeHandler
  | .SHL => some shlHandler
  | .SHR => some shrHandler
  | .SAR => some sarHandler
  | _ => none


-- @@ L46-49 verbatim
/-- Handler table containing SHL/SHR/SAR entries.
    Distinctive token: ShiftHandlers.shiftHandlerTable #107. -/
def shiftHandlerTable : HandlerTable :=
  shiftHandler?


-- @@ L51-55 verbatim
@[simp] theorem shiftStack?_two
    (op : EvmWord → Nat → EvmWord)
    (shift value : EvmWord) (rest : List EvmWord) :
    shiftStack? op (shift :: value :: rest) =
      some (op value shift.toNat :: rest) := rfl


-- @@ L57-59 verbatim
@[simp] theorem shiftStack?_nil
    (op : EvmWord → Nat → EvmWord) :
    shiftStack? op [] = none := rfl


-- @@ L61-63 verbatim
@[simp] theorem shiftStack?_singleton
    (op : EvmWord → Nat → EvmWord) (shift : EvmWord) :
    shiftStack? op [shift] = none := rfl


-- @@ L65-83 verbatim
theorem shiftStack?_eq_some_iff
    (op : EvmWord → Nat → EvmWord) (stack stack' : List EvmWord) :
    shiftStack? op stack = some stack' ↔
      ∃ shift value rest, stack = shift :: value :: rest ∧
        stack' = op value shift.toNat :: rest := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [shiftStack?] at h_stack
    | cons shift stackTail =>
        cases stackTail with
        | nil =>
            simp [shiftStack?] at h_stack
        | cons value rest =>
            simp [shiftStack?] at h_stack
            exact ⟨shift, value, rest, rfl, h_stack.symm⟩
  · rintro ⟨shift, value, rest, rfl, rfl⟩
    simp [shiftStack?]


-- @@ L85-110 verbatim
theorem shiftStack?_eq_none_iff
    (op : EvmWord → Nat → EvmWord) (stack : List EvmWord) :
    shiftStack? op stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp
    | cons shift stackTail =>
        cases stackTail with
        | nil =>
            simp
        | cons value rest =>
            simp [shiftStack?] at h_stack
  · intro h_len
    cases stack with
    | nil =>
        simp [shiftStack?]
    | cons shift stackTail =>
        cases stackTail with
        | nil =>
            simp [shiftStack?]
        | cons value rest =>
            exfalso
            simp at h_len
            omega


-- @@ L112-117 verbatim
theorem shiftHandler_stack_of_shiftStack?_some
    {op : EvmWord → Nat → EvmWord} {state : EvmState}
    {stack' : List EvmWord}
    (h_stack : shiftStack? op state.stack = some stack') :
    (shiftHandler op state).stack = stack' := by
  simp [shiftHandler, h_stack]


-- @@ L119-123 verbatim
theorem shiftHandler_status_of_shiftStack?_none
    {op : EvmWord → Nat → EvmWord} {state : EvmState}
    (h_stack : shiftStack? op state.stack = none) :
    (shiftHandler op state).status = .error := by
  simp [shiftHandler, h_stack]


-- @@ L125-128 verbatim
@[simp] theorem shlHandler_stack
    (shift value : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (shlHandler { state with stack := shift :: value :: rest }).stack =
      (value <<< shift.toNat) :: rest := rfl


-- @@ L130-133 verbatim
@[simp] theorem shrHandler_stack
    (shift value : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (shrHandler { state with stack := shift :: value :: rest }).stack =
      (value >>> shift.toNat) :: rest := rfl


-- @@ L135-138 verbatim
@[simp] theorem sarHandler_stack
    (shift value : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sarHandler { state with stack := shift :: value :: rest }).stack =
      BitVec.sshiftRight value shift.toNat :: rest := rfl


-- @@ L140-141 verbatim
@[simp] theorem shiftHandlerTable_eq :
    shiftHandlerTable = shiftHandler? := rfl


-- @@ L143-144 verbatim
@[simp] theorem shiftHandler?_SHL :
    shiftHandler? .SHL = some shlHandler := rfl


-- @@ L146-147 verbatim
@[simp] theorem shiftHandler?_SHR :
    shiftHandler? .SHR = some shrHandler := rfl


-- @@ L149-150 verbatim
@[simp] theorem shiftHandler?_SAR :
    shiftHandler? .SAR = some sarHandler := rfl


-- @@ L152-154 verbatim
@[simp] theorem eq_shlHandler_iff (handler : OpcodeHandler) :
    shlHandler = handler ↔ handler = shlHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L156-158 verbatim
@[simp] theorem eq_shrHandler_iff (handler : OpcodeHandler) :
    shrHandler = handler ↔ handler = shrHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L160-162 verbatim
@[simp] theorem eq_sarHandler_iff (handler : OpcodeHandler) :
    sarHandler = handler ↔ handler = sarHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L164-170 verbatim
theorem shiftHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    shiftHandler? opcode = some handler ↔
      (opcode = .SHL ∧ handler = shlHandler) ∨
        (opcode = .SHR ∧ handler = shrHandler) ∨
          (opcode = .SAR ∧ handler = sarHandler) := by
  cases opcode <;> simp [shiftHandler?]


-- @@ L172-176 verbatim
theorem shiftHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    shiftHandler? opcode = none ↔
      opcode ≠ .SHL ∧ opcode ≠ .SHR ∧ opcode ≠ .SAR := by
  cases opcode <;> simp [shiftHandler?]


-- @@ L178-182 verbatim
theorem dispatchOpcode?_shiftHandlerTable_SHL
    (state : EvmState) :
    HandlerTable.dispatchOpcode? shiftHandlerTable .SHL state =
      some (shlHandler state) := by
  exact HandlerTable.dispatchOpcode?_some shiftHandler?_SHL state


-- @@ L184-188 verbatim
theorem dispatchOpcode?_shiftHandlerTable_SHR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? shiftHandlerTable .SHR state =
      some (shrHandler state) := by
  exact HandlerTable.dispatchOpcode?_some shiftHandler?_SHR state


-- @@ L190-194 verbatim
theorem dispatchOpcode?_shiftHandlerTable_SAR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? shiftHandlerTable .SAR state =
      some (sarHandler state) := by
  exact HandlerTable.dispatchOpcode?_some shiftHandler?_SAR state


-- @@ L196-200 verbatim
theorem dispatchOpcode_shiftHandlerTable_SHL
    (state : EvmState) :
    HandlerTable.dispatchOpcode shiftHandlerTable .SHL state =
      shlHandler state := by
  exact HandlerTable.dispatchOpcode_some shiftHandler?_SHL state


-- @@ L202-206 verbatim
theorem dispatchOpcode_shiftHandlerTable_SHR
    (state : EvmState) :
    HandlerTable.dispatchOpcode shiftHandlerTable .SHR state =
      shrHandler state := by
  exact HandlerTable.dispatchOpcode_some shiftHandler?_SHR state


-- @@ L208-212 verbatim
theorem dispatchOpcode_shiftHandlerTable_SAR
    (state : EvmState) :
    HandlerTable.dispatchOpcode shiftHandlerTable .SAR state =
      sarHandler state := by
  exact HandlerTable.dispatchOpcode_some shiftHandler?_SAR state


-- @@ L214-221 verbatim
theorem dispatchOpcode_shiftHandlerTable_SHL_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : shiftStack? (fun value n => value <<< n) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode shiftHandlerTable .SHL state).status =
      state.status := by
  rw [dispatchOpcode_shiftHandlerTable_SHL state]
  simp [shlHandler, shiftHandler, h_stack, EvmState.withStack]


-- @@ L223-230 verbatim
theorem dispatchOpcode_shiftHandlerTable_SHR_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : shiftStack? (fun value n => value >>> n) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode shiftHandlerTable .SHR state).status =
      state.status := by
  rw [dispatchOpcode_shiftHandlerTable_SHR state]
  simp [shrHandler, shiftHandler, h_stack, EvmState.withStack]


-- @@ L232-240 verbatim
theorem dispatchOpcode_shiftHandlerTable_SAR_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack :
      shiftStack? (fun value n => BitVec.sshiftRight value n) state.stack =
        some stack') :
    (HandlerTable.dispatchOpcode shiftHandlerTable .SAR state).status =
      state.status := by
  rw [dispatchOpcode_shiftHandlerTable_SAR state]
  simp [sarHandler, shiftHandler, h_stack, EvmState.withStack]


-- @@ L242-242 verbatim
end ShiftHandlers

-- @@ L243-243 verbatim
end EvmAsm.Evm64
