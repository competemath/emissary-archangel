/-
  EvmAsm.Evm64.ComparisonHandlers

  Pure handler-table entries for comparison opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64

-- @@ L14-14 verbatim
namespace ComparisonHandlers


-- @@ L16-18 verbatim
/-- Convert a comparison flag to the EVM 0/1 word result. -/
def boolWord (p : Bool) : EvmWord :=
  if p then 1 else 0


-- @@ L20-25 verbatim
/-- Pure stack transform for binary comparison opcodes. -/
def binaryStack? (cmp : EvmWord → EvmWord → Bool)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: b :: rest => some (boolWord (cmp a b) :: rest)
  | _ => none


-- @@ L27-32 verbatim
/-- Pure stack transform for unary comparison opcodes. -/
def unaryStack? (cmp : EvmWord → Bool)
    (stack : List EvmWord) : Option (List EvmWord) :=
  match stack with
  | a :: rest => some (boolWord (cmp a) :: rest)
  | [] => none


-- @@ L34-38 verbatim
def binaryHandler (cmp : EvmWord → EvmWord → Bool) : OpcodeHandler :=
  fun state =>
    match binaryStack? cmp state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L40-44 verbatim
def unaryHandler (cmp : EvmWord → Bool) : OpcodeHandler :=
  fun state =>
    match unaryStack? cmp state.stack with
    | some stack' => state.withStack stack'
    | none => state.invalid


-- @@ L46-47 verbatim
def ltHandler : OpcodeHandler :=
  binaryHandler BitVec.ult


-- @@ L49-50 verbatim
def gtHandler : OpcodeHandler :=
  binaryHandler (fun a b => BitVec.ult b a)


-- @@ L52-53 verbatim
def sltHandler : OpcodeHandler :=
  binaryHandler BitVec.slt


-- @@ L55-56 verbatim
def sgtHandler : OpcodeHandler :=
  binaryHandler (fun a b => BitVec.slt b a)


-- @@ L58-59 verbatim
def eqHandler : OpcodeHandler :=
  binaryHandler (fun a b => decide (a = b))


-- @@ L61-62 verbatim
def iszeroHandler : OpcodeHandler :=
  unaryHandler (fun a => decide (a = 0))


-- @@ L64-72 verbatim
/-- Lookup surface for comparison handlers. -/
def comparisonHandler? : EvmOpcode → Option OpcodeHandler
  | .LT => some ltHandler
  | .GT => some gtHandler
  | .SLT => some sltHandler
  | .SGT => some sgtHandler
  | .EQ => some eqHandler
  | .ISZERO => some iszeroHandler
  | _ => none


-- @@ L74-77 verbatim
/-- Handler table containing LT/GT/SLT/SGT/EQ/ISZERO entries.
    Distinctive token: ComparisonHandlers.comparisonHandlerTable #107. -/
def comparisonHandlerTable : HandlerTable :=
  comparisonHandler?


-- @@ L79-79 verbatim
@[simp] theorem boolWord_true : boolWord true = 1 := rfl


-- @@ L81-81 verbatim
@[simp] theorem boolWord_false : boolWord false = 0 := rfl


-- @@ L83-87 verbatim
@[simp] theorem binaryStack?_two
    (cmp : EvmWord → EvmWord → Bool)
    (a b : EvmWord) (rest : List EvmWord) :
    binaryStack? cmp (a :: b :: rest) = some (boolWord (cmp a b) :: rest) :=
  rfl


-- @@ L89-92 verbatim
@[simp] theorem unaryStack?_one
    (cmp : EvmWord → Bool)
    (a : EvmWord) (rest : List EvmWord) :
    unaryStack? cmp (a :: rest) = some (boolWord (cmp a) :: rest) := rfl


-- @@ L94-96 verbatim
@[simp] theorem binaryStack?_nil
    (cmp : EvmWord → EvmWord → Bool) :
    binaryStack? cmp [] = none := rfl


-- @@ L98-100 verbatim
@[simp] theorem unaryStack?_nil
    (cmp : EvmWord → Bool) :
    unaryStack? cmp [] = none := rfl


-- @@ L102-120 verbatim
theorem binaryStack?_eq_some_iff
    (cmp : EvmWord → EvmWord → Bool) (stack stack' : List EvmWord) :
    binaryStack? cmp stack = some stack' ↔
      ∃ a b rest, stack = a :: b :: rest ∧
        stack' = boolWord (cmp a b) :: rest := by
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


-- @@ L122-147 verbatim
theorem binaryStack?_eq_none_iff
    (cmp : EvmWord → EvmWord → Bool) (stack : List EvmWord) :
    binaryStack? cmp stack = none ↔ stack.length < 2 := by
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


-- @@ L149-162 verbatim
theorem unaryStack?_eq_some_iff
    (cmp : EvmWord → Bool) (stack stack' : List EvmWord) :
    unaryStack? cmp stack = some stack' ↔
      ∃ a rest, stack = a :: rest ∧ stack' = boolWord (cmp a) :: rest := by
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


-- @@ L164-179 verbatim
theorem unaryStack?_eq_none_iff
    (cmp : EvmWord → Bool) (stack : List EvmWord) :
    unaryStack? cmp stack = none ↔ stack.length < 1 := by
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


-- @@ L181-186 verbatim
theorem binaryHandler_stack_of_binaryStack?_some
    {cmp : EvmWord → EvmWord → Bool}
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? cmp state.stack = some stack') :
    (binaryHandler cmp state).stack = stack' := by
  simp [binaryHandler, h_stack]


-- @@ L188-193 verbatim
theorem unaryHandler_stack_of_unaryStack?_some
    {cmp : EvmWord → Bool}
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? cmp state.stack = some stack') :
    (unaryHandler cmp state).stack = stack' := by
  simp [unaryHandler, h_stack]


-- @@ L195-200 verbatim
theorem binaryHandler_status_of_binaryStack?_none
    {cmp : EvmWord → EvmWord → Bool}
    {state : EvmState}
    (h_stack : binaryStack? cmp state.stack = none) :
    (binaryHandler cmp state).status = .error := by
  simp [binaryHandler, h_stack]


-- @@ L202-206 verbatim
theorem unaryHandler_status_of_unaryStack?_none
    {cmp : EvmWord → Bool} {state : EvmState}
    (h_stack : unaryStack? cmp state.stack = none) :
    (unaryHandler cmp state).status = .error := by
  simp [unaryHandler, h_stack]


-- @@ L208-211 verbatim
@[simp] theorem ltHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (ltHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.ult a b) :: rest := rfl


-- @@ L213-216 verbatim
@[simp] theorem gtHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (gtHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.ult b a) :: rest := rfl


-- @@ L218-221 verbatim
@[simp] theorem sltHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sltHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.slt a b) :: rest := rfl


-- @@ L223-226 verbatim
@[simp] theorem sgtHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (sgtHandler { state with stack := a :: b :: rest }).stack =
      boolWord (BitVec.slt b a) :: rest := rfl


-- @@ L228-231 verbatim
@[simp] theorem eqHandler_stack
    (a b : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (eqHandler { state with stack := a :: b :: rest }).stack =
      boolWord (decide (a = b)) :: rest := rfl


-- @@ L233-236 verbatim
@[simp] theorem iszeroHandler_stack
    (a : EvmWord) (rest : List EvmWord) (state : EvmState) :
    (iszeroHandler { state with stack := a :: rest }).stack =
      boolWord (decide (a = 0)) :: rest := rfl


-- @@ L238-239 verbatim
@[simp] theorem comparisonHandlerTable_eq :
    comparisonHandlerTable = comparisonHandler? := rfl


-- @@ L241-242 verbatim
@[simp] theorem comparisonHandler?_LT :
    comparisonHandler? .LT = some ltHandler := rfl


-- @@ L244-245 verbatim
@[simp] theorem comparisonHandler?_GT :
    comparisonHandler? .GT = some gtHandler := rfl


-- @@ L247-248 verbatim
@[simp] theorem comparisonHandler?_SLT :
    comparisonHandler? .SLT = some sltHandler := rfl


-- @@ L250-251 verbatim
@[simp] theorem comparisonHandler?_SGT :
    comparisonHandler? .SGT = some sgtHandler := rfl


-- @@ L253-254 verbatim
@[simp] theorem comparisonHandler?_EQ :
    comparisonHandler? .EQ = some eqHandler := rfl


-- @@ L256-257 verbatim
@[simp] theorem comparisonHandler?_ISZERO :
    comparisonHandler? .ISZERO = some iszeroHandler := rfl


-- @@ L259-261 verbatim
@[simp] theorem eq_ltHandler_iff (handler : OpcodeHandler) :
    ltHandler = handler ↔ handler = ltHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L263-265 verbatim
@[simp] theorem eq_gtHandler_iff (handler : OpcodeHandler) :
    gtHandler = handler ↔ handler = gtHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L267-269 verbatim
@[simp] theorem eq_sltHandler_iff (handler : OpcodeHandler) :
    sltHandler = handler ↔ handler = sltHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L271-273 verbatim
@[simp] theorem eq_sgtHandler_iff (handler : OpcodeHandler) :
    sgtHandler = handler ↔ handler = sgtHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L275-277 verbatim
@[simp] theorem eq_eqHandler_iff (handler : OpcodeHandler) :
    eqHandler = handler ↔ handler = eqHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L279-281 verbatim
@[simp] theorem eq_iszeroHandler_iff (handler : OpcodeHandler) :
    iszeroHandler = handler ↔ handler = iszeroHandler := by
  constructor <;> intro h_eq <;> exact h_eq.symm


-- @@ L283-292 verbatim
theorem comparisonHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    comparisonHandler? opcode = some handler ↔
      (opcode = .LT ∧ handler = ltHandler) ∨
        (opcode = .GT ∧ handler = gtHandler) ∨
          (opcode = .SLT ∧ handler = sltHandler) ∨
            (opcode = .SGT ∧ handler = sgtHandler) ∨
              (opcode = .EQ ∧ handler = eqHandler) ∨
                (opcode = .ISZERO ∧ handler = iszeroHandler) := by
  cases opcode <;> simp [comparisonHandler?]


-- @@ L294-299 verbatim
theorem comparisonHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    comparisonHandler? opcode = none ↔
      opcode ≠ .LT ∧ opcode ≠ .GT ∧ opcode ≠ .SLT ∧
        opcode ≠ .SGT ∧ opcode ≠ .EQ ∧ opcode ≠ .ISZERO := by
  cases opcode <;> simp [comparisonHandler?]


-- @@ L301-305 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_LT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .LT state =
      some (ltHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_LT state


-- @@ L307-311 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_GT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .GT state =
      some (gtHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_GT state


-- @@ L313-317 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_SLT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .SLT state =
      some (sltHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_SLT state


-- @@ L319-323 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_SGT
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .SGT state =
      some (sgtHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_SGT state


-- @@ L325-329 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_EQ
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .EQ state =
      some (eqHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_EQ state


-- @@ L331-335 verbatim
theorem dispatchOpcode?_comparisonHandlerTable_ISZERO
    (state : EvmState) :
    HandlerTable.dispatchOpcode? comparisonHandlerTable .ISZERO state =
      some (iszeroHandler state) := by
  exact HandlerTable.dispatchOpcode?_some comparisonHandler?_ISZERO state


-- @@ L337-341 verbatim
theorem dispatchOpcode_comparisonHandlerTable_LT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .LT state =
      ltHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_LT state


-- @@ L343-347 verbatim
theorem dispatchOpcode_comparisonHandlerTable_GT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .GT state =
      gtHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_GT state


-- @@ L349-353 verbatim
theorem dispatchOpcode_comparisonHandlerTable_SLT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .SLT state =
      sltHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_SLT state


-- @@ L355-359 verbatim
theorem dispatchOpcode_comparisonHandlerTable_SGT
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .SGT state =
      sgtHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_SGT state


-- @@ L361-365 verbatim
theorem dispatchOpcode_comparisonHandlerTable_EQ
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .EQ state =
      eqHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_EQ state


-- @@ L367-371 verbatim
theorem dispatchOpcode_comparisonHandlerTable_ISZERO
    (state : EvmState) :
    HandlerTable.dispatchOpcode comparisonHandlerTable .ISZERO state =
      iszeroHandler state := by
  exact HandlerTable.dispatchOpcode_some comparisonHandler?_ISZERO state


-- @@ L373-379 verbatim
theorem dispatchOpcode_comparisonHandlerTable_LT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? BitVec.ult state.stack = some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .LT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_LT state]
  simp [ltHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L381-388 verbatim
theorem dispatchOpcode_comparisonHandlerTable_GT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => BitVec.ult b a) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .GT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_GT state]
  simp [gtHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L390-396 verbatim
theorem dispatchOpcode_comparisonHandlerTable_SLT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? BitVec.slt state.stack = some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .SLT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_SLT state]
  simp [sltHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L398-405 verbatim
theorem dispatchOpcode_comparisonHandlerTable_SGT_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => BitVec.slt b a) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .SGT state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_SGT state]
  simp [sgtHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L407-414 verbatim
theorem dispatchOpcode_comparisonHandlerTable_EQ_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : binaryStack? (fun a b => decide (a = b)) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .EQ state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_EQ state]
  simp [eqHandler, binaryHandler, h_stack, EvmState.withStack]


-- @@ L416-425 verbatim
theorem dispatchOpcode_comparisonHandlerTable_ISZERO_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : unaryStack? (fun a => decide (a = (0 : EvmWord))) state.stack =
      some stack') :
    (HandlerTable.dispatchOpcode comparisonHandlerTable .ISZERO state).status =
      state.status := by
  rw [dispatchOpcode_comparisonHandlerTable_ISZERO state]
  cases h_stack_state : state.stack <;>
    simp [unaryStack?, iszeroHandler, unaryHandler, EvmState.withStack,
      h_stack_state] at h_stack ⊢


-- @@ L427-427 verbatim
end ComparisonHandlers

-- @@ L428-428 verbatim
end EvmAsm.Evm64
