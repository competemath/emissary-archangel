/-
  EvmAsm.Evm64.BitwiseHandlers

  Pure handler-table entries for bitwise opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace BitwiseHandlers


-- @@ L16-21 verbatim
/-- Pure stack transform for binary bitwise opcodes. -/
def binaryStack? (op : EvmWord → EvmWord → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: b :: rest => some (op a b :: rest)
  | _ => none


-- @@ L23-28 verbatim
/-- Pure stack transform for unary bitwise opcodes. -/
def unaryStack? (op : EvmWord → EvmWord)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: rest => some (op a :: rest)
  | [] => none


-- @@ L30-34 verbatim
def binaryHandler (op : EvmWord → EvmWord → EvmWord) : OpcodeHandler :=
  fun state =>
    match binaryStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L36-40 verbatim
def unaryHandler (op : EvmWord → EvmWord) : OpcodeHandler :=
  fun state =>
    match unaryStack? op state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L42-43 verbatim
def andHandler : OpcodeHandler :=
  binaryHandler (fun a b => a &&& b)


-- @@ L45-46 verbatim
def orHandler : OpcodeHandler :=
  binaryHandler (fun a b => a ||| b)


-- @@ L48-49 verbatim
def xorHandler : OpcodeHandler :=
  binaryHandler (fun a b => a ^^^ b)


-- @@ L51-52 verbatim
def notHandler : OpcodeHandler :=
  unaryHandler (fun a => ~~~a)


-- @@ L54-60 verbatim
/-- Lookup surface for bitwise handlers. -/
def bitwiseHandler? : EvmOpcode → Option OpcodeHandler
  | .AND => some andHandler
  | .OR => some orHandler
  | .XOR => some xorHandler
  | .NOT => some notHandler
  | _ => none


-- @@ L62-65 verbatim
/-- Handler table containing AND/OR/XOR/NOT entries.
    Distinctive token: BitwiseHandlers.bitwiseHandlerTable #107. -/
def bitwiseHandlerTable : HandlerTable :=
  bitwiseHandler?


-- @@ L67-70 verbatim
@[simp] theorem binaryStack?_two
    (op : EvmWord → EvmWord → EvmWord)
    (a b : EvmWord) (rest : List EvmWord) :
    binaryStack? op (a :: b :: rest) = some (op a b :: rest) := rfl


-- @@ L72-74 verbatim
@[simp] theorem unaryStack?_one
    (op : EvmWord → EvmWord) (a : EvmWord) (rest : List EvmWord) :
    unaryStack? op (a :: rest) = some (op a :: rest) := rfl


-- @@ L76-78 verbatim
@[simp] theorem binaryStack?_nil
    (op : EvmWord → EvmWord → EvmWord) :
    binaryStack? op [] = none := rfl


-- @@ L80-82 verbatim
@[simp] theorem unaryStack?_nil
    (op : EvmWord → EvmWord) :
    unaryStack? op [] = none := rfl


-- @@ L84-101 verbatim
theorem binaryStack?_eq_some_iff
    (op : EvmWord → EvmWord → EvmWord) (stack stack' : List EvmWord) :
    binaryStack? op stack = some stack' ↔
      ∃ a b rest, stack = a :: b :: rest ∧ stack' = op a b :: rest := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [binaryStack?] at h_stack
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp [binaryStack?] at h_stack
        | cons b rest =>
            simp [binaryStack?] at h_stack
            exact ⟨a, b, rest, rfl, h_stack.symm⟩
  · rintro ⟨a, b, rest, rfl, rfl⟩
    simp [binaryStack?]


-- @@ L103-128 verbatim
theorem binaryStack?_eq_none_iff
    (op : EvmWord → EvmWord → EvmWord) (stack : List EvmWord) :
    binaryStack? op stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp
        | cons b rest =>
            simp [binaryStack?] at h_stack
  · intro h_len
    cases stack with
    | nil =>
        simp [binaryStack?]
    | cons a stackTail =>
        cases stackTail with
        | nil =>
            simp [binaryStack?]
        | cons b rest =>
            exfalso
            simp at h_len
            omega


-- @@ L130-143 verbatim
theorem unaryStack?_eq_some_iff
    (op : EvmWord → EvmWord) (stack stack' : List EvmWord) :
    unaryStack? op stack = some stack' ↔
      ∃ a rest, stack = a :: rest ∧ stack' = op a :: rest := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp [unaryStack?] at h_stack
    | cons a rest =>
        simp [unaryStack?] at h_stack
        exact ⟨a, rest, rfl, h_stack.symm⟩
  · rintro ⟨a, rest, rfl, rfl⟩
    simp [unaryStack?]


-- @@ L145-160 verbatim
theorem unaryStack?_eq_none_iff
    (op : EvmWord → EvmWord) (stack : List EvmWord) :
    unaryStack? op stack = none ↔ stack.length < 1 := by
  constructor
  · intro h_stack
    cases stack with
    | nil =>
        simp
    | cons a rest =>
        simp [unaryStack?] at h_stack
  · intro h_len
    cases stack with
    | nil =>
        simp [unaryStack?]
    | cons a rest =>
        simp at h_len


-- @@ L162-167 verbatim
theorem binaryHandler_stack_of_binaryStack?_some
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    {stack' : List EvmWord}
    (h_stack : binaryStack? op state.stack = some stack') :
    (binaryHandler op state).stack = stack' := by
  simp [binaryHandler, h_stack]


-- @@ L169-173 verbatim
theorem unaryHandler_stack_of_unaryStack?_some
    {op : EvmWord → EvmWord} {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? op state.stack = some stack') :
    (unaryHandler op state).stack = stack' := by
  simp [unaryHandler, h_stack]


-- @@ L175-179 verbatim
theorem binaryHandler_status_of_binaryStack?_none
    {op : EvmWord → EvmWord → EvmWord} {state : EvmState}
    (h_stack : binaryStack? op state.stack = none) :
    (binaryHandler op state).status = .error := by
  simp [binaryHandler, h_stack]


-- @@ L181-185 verbatim
theorem unaryHandler_status_of_unaryStack?_none
    {op : EvmWord → EvmWord} {state : EvmState}
    (h_stack : unaryStack? op state.stack = none) :
    (unaryHandler op state).status = .error := by
  simp [unaryHandler, h_stack]


-- @@ L187-190 verbatim
@[simp] theorem andHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (andHandler { state with stack := a :: b :: rest }).stack =
      (a &&& b) :: rest := rfl


-- @@ L192-195 verbatim
@[simp] theorem orHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (orHandler { state with stack := a :: b :: rest }).stack =
      (a ||| b) :: rest := rfl


-- @@ L197-200 verbatim
@[simp] theorem xorHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (xorHandler { state with stack := a :: b :: rest }).stack =
      (a ^^^ b) :: rest := rfl


-- @@ L202-205 verbatim
@[simp] theorem notHandler_stack
    (a : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (notHandler { state with stack := a :: rest }).stack =
      (~~~a) :: rest := rfl


-- @@ L207-208 verbatim
@[simp] theorem bitwiseHandlerTable_eq :
    bitwiseHandlerTable = bitwiseHandler? := rfl


-- @@ L210-211 verbatim
@[simp] theorem bitwiseHandler?_AND :
    bitwiseHandler? .AND = some andHandler := rfl


-- @@ L213-214 verbatim
@[simp] theorem bitwiseHandler?_OR :
    bitwiseHandler? .OR = some orHandler := rfl


-- @@ L216-217 verbatim
@[simp] theorem bitwiseHandler?_XOR :
    bitwiseHandler? .XOR = some xorHandler := rfl


-- @@ L219-220 verbatim
@[simp] theorem bitwiseHandler?_NOT :
    bitwiseHandler? .NOT = some notHandler := rfl


-- @@ L222-224 verbatim
@[simp] theorem eq_andHandler_iff (handler : OpcodeHandler) :
    andHandler = handler ↔ handler = andHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L226-228 verbatim
@[simp] theorem eq_orHandler_iff (handler : OpcodeHandler) :
    orHandler = handler ↔ handler = orHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L230-232 verbatim
@[simp] theorem eq_xorHandler_iff (handler : OpcodeHandler) :
    xorHandler = handler ↔ handler = xorHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L234-236 verbatim
@[simp] theorem eq_notHandler_iff (handler : OpcodeHandler) :
    notHandler = handler ↔ handler = notHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L238-245 verbatim
theorem bitwiseHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    bitwiseHandler? opcode = some handler ↔
      (opcode = .AND ∧ handler = andHandler) ∨
        (opcode = .OR ∧ handler = orHandler) ∨
          (opcode = .XOR ∧ handler = xorHandler) ∨
            (opcode = .NOT ∧ handler = notHandler) := by
  cases opcode <;> simp [bitwiseHandler?]


-- @@ L247-251 verbatim
theorem bitwiseHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    bitwiseHandler? opcode = none ↔
      opcode ≠ .AND ∧ opcode ≠ .OR ∧ opcode ≠ .XOR ∧ opcode ≠ .NOT := by
  cases opcode <;> simp [bitwiseHandler?]


-- @@ L253-257 verbatim
theorem dispatchOpcode?_bitwiseHandlerTable_AND
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .AND state =
      some (andHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_AND state


-- @@ L259-263 verbatim
theorem dispatchOpcode?_bitwiseHandlerTable_OR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .OR state =
      some (orHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_OR state


-- @@ L265-269 verbatim
theorem dispatchOpcode?_bitwiseHandlerTable_XOR
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .XOR state =
      some (xorHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_XOR state


-- @@ L271-275 verbatim
theorem dispatchOpcode?_bitwiseHandlerTable_NOT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? bitwiseHandlerTable .NOT state =
      some (notHandler state) := by
  exact HandlerTable.dispatchOpcode?_some bitwiseHandler?_NOT state


-- @@ L277-281 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_AND
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .AND state =
      andHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_AND state


-- @@ L283-287 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_OR
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .OR state =
      orHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_OR state


-- @@ L289-293 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_XOR
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .XOR state =
      xorHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_XOR state


-- @@ L295-299 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_NOT
    (state : EvmState) :
    HandlerTable.dispatchOpcode bitwiseHandlerTable .NOT state =
      notHandler state := by
  exact HandlerTable.dispatchOpcode_some bitwiseHandler?_NOT state


-- @@ L301-307 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_AND_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a &&& b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode bitwiseHandlerTable .AND state).status =
      state.status := by
  rw [dispatchOpcode_bitwiseHandlerTable_AND state]
  simp [andHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L309-315 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_OR_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a ||| b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode bitwiseHandlerTable .OR state).status =
      state.status := by
  rw [dispatchOpcode_bitwiseHandlerTable_OR state]
  simp [orHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L317-323 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_XOR_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => a ^^^ b) state.stack = some stack') :
    (HandlerTable.dispatchOpcode bitwiseHandlerTable .XOR state).status =
      state.status := by
  rw [dispatchOpcode_bitwiseHandlerTable_XOR state]
  simp [xorHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L325-331 verbatim
theorem dispatchOpcode_bitwiseHandlerTable_NOT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? (fun a => ~~~a) state.stack = some stack') :
    (HandlerTable.dispatchOpcode bitwiseHandlerTable .NOT state).status =
      state.status := by
  rw [dispatchOpcode_bitwiseHandlerTable_NOT state]
  simp [notHandler, unaryHandler, h_stack, EvmState.withStack]


-- @@ L333-333 verbatim
end BitwiseHandlers

-- @@ L334-334 verbatim
end EvmAsm.Evm64
