/-
  EvmAsm.Evm64.EnvHandlers

  Generic pure handler-table entries for simple environment opcodes (GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTable
public import EvmAsm.Evm64.Env.Gas


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace EnvHandlers


-- @@ L17-17 verbatim
abbrev SimpleEnvField := Env.SimpleEnvField


-- @@ L19-34 verbatim
/-- Decode handler-table opcodes back to the simple environment field surface. -/
def fieldOfOpcode? : EvmOpcode → Option SimpleEnvField
  | .ADDRESS => some .address
  | .ORIGIN => some .origin
  | .CALLER => some .caller
  | .CALLVALUE => some .callValue
  | .GASPRICE => some .gasPrice
  | .COINBASE => some .coinbase
  | .TIMESTAMP => some .timestamp
  | .NUMBER => some .number
  | .PREVRANDAO => some .prevrandao
  | .GASLIMIT => some .gasLimit
  | .CHAINID => some .chainId
  | .SELFBALANCE => some .selfBalance
  | .BASEFEE => some .baseFee
  | _ => none


-- @@ L36-39 verbatim
/-- Pure simple-environment handler. It pushes the field value exposed by the
    executable environment spec; gas/pc charging belongs to later wrappers. -/
def simpleEnvHandler (field : SimpleEnvField) : OpcodeHandler :=
  fun state => state.withStack (field.value state.env :: state.stack)


-- @@ L41-45 verbatim
/-- Lookup surface for simple environment opcode handlers. -/
def simpleEnvHandler? (opcode : EvmOpcode) : Option OpcodeHandler :=
  match fieldOfOpcode? opcode with
  | some field => some (simpleEnvHandler field)
  | none => none


-- @@ L47-62 verbatim
theorem simpleEnvHandler?_eq_some_iff
    (opcode : EvmOpcode) (handler : OpcodeHandler) :
    simpleEnvHandler? opcode = some handler ↔
      ∃ field, fieldOfOpcode? opcode = some field ∧
        handler = simpleEnvHandler field := by
  constructor
  · intro h_handler
    unfold simpleEnvHandler? at h_handler
    cases h_field : fieldOfOpcode? opcode with
    | none =>
        simp [h_field] at h_handler
    | some field =>
        simp [h_field] at h_handler
        exact ⟨field, rfl, h_handler.symm⟩
  · rintro ⟨field, h_field, rfl⟩
    simp [simpleEnvHandler?, h_field]


-- @@ L64-72 verbatim
theorem simpleEnvHandler?_eq_none_iff
    (opcode : EvmOpcode) :
    simpleEnvHandler? opcode = none ↔ fieldOfOpcode? opcode = none := by
  unfold simpleEnvHandler?
  cases h_field : fieldOfOpcode? opcode with
  | none =>
      simp
  | some field =>
      simp


-- @@ L74-77 verbatim
/-- Handler table containing the generic simple environment opcode entries.
    Distinctive token: EnvHandlers.simpleEnvHandlerTable #107. -/
def simpleEnvHandlerTable : HandlerTable :=
  simpleEnvHandler?


-- @@ L79-82 verbatim
@[simp] theorem simpleEnvHandler_stack
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).stack =
      field.value state.env :: state.stack := rfl


-- @@ L84-86 verbatim
@[simp] theorem simpleEnvHandler_status
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).status = state.status := rfl


-- @@ L88-90 verbatim
@[simp] theorem simpleEnvHandler_env
    (field : SimpleEnvField) (state : EvmState) :
    (simpleEnvHandler field state).env = state.env := rfl


-- @@ L92-93 verbatim
@[simp] theorem simpleEnvHandlerTable_eq :
    simpleEnvHandlerTable = simpleEnvHandler? := rfl


-- @@ L95-97 verbatim
theorem fieldOfOpcode?_of_field (field : SimpleEnvField) :
    fieldOfOpcode? field.opcode = some field := by
  cases field <;> rfl


-- @@ L99-101 verbatim
theorem simpleEnvHandler?_of_field (field : SimpleEnvField) :
    simpleEnvHandler? field.opcode = some (simpleEnvHandler field) := by
  simp [simpleEnvHandler?, fieldOfOpcode?_of_field]


-- @@ L103-108 verbatim
theorem dispatchOpcode?_simpleEnvHandlerTable_of_field
    (field : SimpleEnvField) (state : EvmState) :
    HandlerTable.dispatchOpcode? simpleEnvHandlerTable field.opcode state =
      some (simpleEnvHandler field state) := by
  exact HandlerTable.dispatchOpcode?_some
    (simpleEnvHandler?_of_field field) state


-- @@ L110-115 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_of_field
    (field : SimpleEnvField) (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable field.opcode state =
      simpleEnvHandler field state := by
  exact HandlerTable.dispatchOpcode_some
    (simpleEnvHandler?_of_field field) state


-- @@ L117-122 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_of_field_status
    (field : SimpleEnvField) (state : EvmState) :
    (HandlerTable.dispatchOpcode simpleEnvHandlerTable field.opcode state).status =
      state.status := by
  rw [dispatchOpcode_simpleEnvHandlerTable_of_field field state]
  exact simpleEnvHandler_status field state


-- @@ L124-125 verbatim
@[simp] theorem fieldOfOpcode?_ADDRESS :
    fieldOfOpcode? .ADDRESS = some .address := rfl


-- @@ L127-128 verbatim
@[simp] theorem fieldOfOpcode?_ORIGIN :
    fieldOfOpcode? .ORIGIN = some .origin := rfl


-- @@ L130-131 verbatim
@[simp] theorem fieldOfOpcode?_CALLER :
    fieldOfOpcode? .CALLER = some .caller := rfl


-- @@ L133-134 verbatim
@[simp] theorem fieldOfOpcode?_CALLVALUE :
    fieldOfOpcode? .CALLVALUE = some .callValue := rfl


-- @@ L136-137 verbatim
@[simp] theorem fieldOfOpcode?_SELFBALANCE :
    fieldOfOpcode? .SELFBALANCE = some .selfBalance := rfl


-- @@ L139-143 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_ADDRESS
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .ADDRESS state =
      simpleEnvHandler .address state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .address state


-- @@ L145-149 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_ORIGIN
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .ORIGIN state =
      simpleEnvHandler .origin state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .origin state


-- @@ L151-155 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_CALLER
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .CALLER state =
      simpleEnvHandler .caller state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .caller state


-- @@ L157-161 verbatim
theorem dispatchOpcode_simpleEnvHandlerTable_CALLVALUE
    (state : EvmState) :
    HandlerTable.dispatchOpcode simpleEnvHandlerTable .CALLVALUE state =
      simpleEnvHandler .callValue state :=
  dispatchOpcode_simpleEnvHandlerTable_of_field .callValue state


-- @@ L163-163 verbatim
end EnvHandlers

-- @@ L164-164 verbatim
end EvmAsm.Evm64
