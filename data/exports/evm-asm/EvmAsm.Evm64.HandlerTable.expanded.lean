/-
  EvmAsm.Evm64.HandlerTable

  Pure opcode-handler table surface for the interpreter layer (GH #107).
-/

module

public import EvmAsm.Evm64.Gas
public import EvmAsm.Evm64.Termination


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-17 verbatim
/-- A pure opcode handler transforms an abstract EVM interpreter state. -/
abbrev OpcodeHandler := EvmState → EvmState


-- @@ L19-22 verbatim
/-- Partial table of opcode handlers. Missing entries are handled by
    `dispatchOpcode` as INVALID/error, matching the executable interpreter's
    conservative default while wrappers land one family at a time. -/
abbrev HandlerTable := EvmOpcode → Option OpcodeHandler


-- @@ L24-24 verbatim
namespace HandlerTable


-- @@ L26-28 verbatim
/-- Empty table: every opcode is currently unimplemented. -/
def empty : HandlerTable :=
  fun _ => none


-- @@ L30-33 verbatim
/-- Extend or replace one opcode handler. -/
def setHandler (table : HandlerTable) (opcode : EvmOpcode)
    (handler : OpcodeHandler) : HandlerTable :=
  fun opcode' => if opcode' = opcode then some handler else table opcode'


-- @@ L35-40 verbatim
/-- Try to dispatch an opcode through a partial handler table. -/
def dispatchOpcode? (table : HandlerTable) (opcode : EvmOpcode)
    (state : EvmState) : Option EvmState :=
  match table opcode with
  | some handler => some (handler state)
  | none => none


-- @@ L42-47 verbatim
/-- Total dispatch surface: absent handlers execute the INVALID/error path. -/
def dispatchOpcode (table : HandlerTable) (opcode : EvmOpcode)
    (state : EvmState) : EvmState :=
  match dispatchOpcode? table opcode state with
  | some state' => state'
  | none => state.invalid


-- @@ L49-50 verbatim
@[simp] theorem empty_apply (opcode : EvmOpcode) :
    empty opcode = none := rfl


-- @@ L52-53 verbatim
@[simp] theorem dispatchOpcode?_empty (opcode : EvmOpcode) (state : EvmState) :
    dispatchOpcode? empty opcode state = none := rfl


-- @@ L55-56 verbatim
@[simp] theorem dispatchOpcode_empty (opcode : EvmOpcode) (state : EvmState) :
    dispatchOpcode empty opcode state = state.invalid := rfl


-- @@ L58-61 verbatim
@[simp] theorem setHandler_same (table : HandlerTable) (opcode : EvmOpcode)
    (handler : OpcodeHandler) :
    setHandler table opcode handler opcode = some handler := by
  simp [setHandler]


-- @@ L63-66 verbatim
theorem setHandler_ne (table : HandlerTable) {opcode opcode' : EvmOpcode}
    (handler : OpcodeHandler) (h_ne : opcode' ≠ opcode) :
    setHandler table opcode handler opcode' = table opcode' := by
  simp [setHandler, h_ne]


-- @@ L68-78 verbatim
theorem setHandler_eq_some_iff
    (table : HandlerTable) (opcode opcode' : EvmOpcode)
    (handler handler' : OpcodeHandler) :
    setHandler table opcode handler opcode' = some handler' ↔
      (opcode' = opcode ∧ handler = handler') ∨
        (opcode' ≠ opcode ∧ table opcode' = some handler') := by
  unfold setHandler
  by_cases h_eq : opcode' = opcode
  · subst h_eq
    simp
  · simp [h_eq]


-- @@ L80-89 verbatim
theorem setHandler_eq_none_iff
    (table : HandlerTable) (opcode opcode' : EvmOpcode)
    (handler : OpcodeHandler) :
    setHandler table opcode handler opcode' = none ↔
      opcode' ≠ opcode ∧ table opcode' = none := by
  unfold setHandler
  by_cases h_eq : opcode' = opcode
  · subst h_eq
    simp
  · simp [h_eq]


-- @@ L91-95 verbatim
@[simp] theorem dispatchOpcode?_setHandler_same (table : HandlerTable)
    (opcode : EvmOpcode) (handler : OpcodeHandler) (state : EvmState) :
    dispatchOpcode? (setHandler table opcode handler) opcode state =
      some (handler state) := by
  simp [dispatchOpcode?]


-- @@ L97-101 verbatim
@[simp] theorem dispatchOpcode_setHandler_same (table : HandlerTable)
    (opcode : EvmOpcode) (handler : OpcodeHandler) (state : EvmState) :
    dispatchOpcode (setHandler table opcode handler) opcode state =
      handler state := by
  simp [dispatchOpcode]


-- @@ L103-108 verbatim
theorem dispatchOpcode?_setHandler_ne (table : HandlerTable)
    {opcode opcode' : EvmOpcode} (handler : OpcodeHandler) (state : EvmState)
    (h_ne : opcode' ≠ opcode) :
    dispatchOpcode? (setHandler table opcode handler) opcode' state =
      dispatchOpcode? table opcode' state := by
  simp [dispatchOpcode?, setHandler_ne table handler h_ne]


-- @@ L110-115 verbatim
theorem dispatchOpcode_setHandler_ne (table : HandlerTable)
    {opcode opcode' : EvmOpcode} (handler : OpcodeHandler) (state : EvmState)
    (h_ne : opcode' ≠ opcode) :
    dispatchOpcode (setHandler table opcode handler) opcode' state =
      dispatchOpcode table opcode' state := by
  simp [dispatchOpcode, dispatchOpcode?_setHandler_ne table handler state h_ne]


-- @@ L117-121 verbatim
theorem dispatchOpcode?_some {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    dispatchOpcode? table opcode state = some (handler state) := by
  simp [dispatchOpcode?, h_lookup]


-- @@ L123-126 verbatim
theorem dispatchOpcode?_none {table : HandlerTable} {opcode : EvmOpcode}
    (h_lookup : table opcode = none) (state : EvmState) :
    dispatchOpcode? table opcode state = none := by
  simp [dispatchOpcode?, h_lookup]


-- @@ L128-137 verbatim
theorem dispatchOpcode?_eq_some_iff {table : HandlerTable}
    {opcode : EvmOpcode} {state state' : EvmState} :
    dispatchOpcode? table opcode state = some state' ↔
      ∃ handler, table opcode = some handler ∧ handler state = state' := by
  unfold dispatchOpcode?
  cases h_lookup : table opcode with
  | none =>
      simp
  | some handler =>
      simp


-- @@ L139-143 verbatim
theorem dispatchOpcode?_eq_none_iff {table : HandlerTable}
    {opcode : EvmOpcode} {state : EvmState} :
    dispatchOpcode? table opcode state = none ↔ table opcode = none := by
  unfold dispatchOpcode?
  cases table opcode <;> simp


-- @@ L145-149 verbatim
theorem dispatchOpcode_some {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    dispatchOpcode table opcode state = handler state := by
  simp [dispatchOpcode, dispatchOpcode?_some h_lookup]


-- @@ L151-155 verbatim
theorem dispatchOpcode_some_status {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    (dispatchOpcode table opcode state).status = (handler state).status := by
  rw [dispatchOpcode_some h_lookup state]


-- @@ L157-161 verbatim
theorem dispatchOpcode_some_pc {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    (dispatchOpcode table opcode state).pc = (handler state).pc := by
  rw [dispatchOpcode_some h_lookup state]


-- @@ L163-167 verbatim
theorem dispatchOpcode_some_gas {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    (dispatchOpcode table opcode state).gas = (handler state).gas := by
  rw [dispatchOpcode_some h_lookup state]


-- @@ L169-173 verbatim
theorem dispatchOpcode_some_stack {table : HandlerTable} {opcode : EvmOpcode}
    {handler : OpcodeHandler} (h_lookup : table opcode = some handler)
    (state : EvmState) :
    (dispatchOpcode table opcode state).stack = (handler state).stack := by
  rw [dispatchOpcode_some h_lookup state]


-- @@ L175-182 verbatim
theorem dispatchOpcode_some_preserves_status
    {table : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : table opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status)
    (state : EvmState) :
    (dispatchOpcode table opcode state).status = state.status := by
  rw [dispatchOpcode_some_status h_lookup state]
  exact h_status state


-- @@ L184-192 verbatim
theorem dispatchOpcode_some_preserves_codeLenMatches
    {table : HandlerTable} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_lookup : table opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (dispatchOpcode table opcode state).codeLenMatches := by
  rw [dispatchOpcode_some h_lookup state]
  exact h_codeLen state h_state


-- @@ L194-197 verbatim
theorem dispatchOpcode_none {table : HandlerTable} {opcode : EvmOpcode}
    (h_lookup : table opcode = none) (state : EvmState) :
    dispatchOpcode table opcode state = state.invalid := by
  simp [dispatchOpcode, dispatchOpcode?_none h_lookup]


-- @@ L199-203 verbatim
theorem dispatchOpcode_none_status {table : HandlerTable} {opcode : EvmOpcode}
    (h_lookup : table opcode = none) (state : EvmState) :
    (dispatchOpcode table opcode state).status = .error := by
  rw [dispatchOpcode_none h_lookup state]
  exact EvmState.invalid_status state


-- @@ L205-205 verbatim
end HandlerTable


-- @@ L207-207 verbatim
end EvmAsm.Evm64
