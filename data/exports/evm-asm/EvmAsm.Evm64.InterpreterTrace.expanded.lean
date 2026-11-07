/-
  EvmAsm.Evm64.InterpreterTrace

  Decoded-opcode trace bridge for the pure interpreter loop (GH #108).
-/

module

public import EvmAsm.Evm64.InterpreterLoop


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace InterpreterTrace


-- @@ L17-17 verbatim
abbrev Handler := InterpreterLoop.Handler


-- @@ L19-35 verbatim
/--
Trace the supported opcodes decoded by `InterpreterLoop.loopFuel`. EOF or an
unsupported byte contributes no opcode and transitions through the loop's
`invalid` branch.

Distinctive token: InterpreterTrace.loopTrace #108.
-/
def loopTrace (handler : Handler) : Nat → EvmState → List EvmOpcode
  | 0, _ => []
  | nSteps + 1, state =>
      match state.status with
      | .running =>
          match InterpreterLoop.decodeCurrentOpcode? state with
          | some opcode =>
              opcode :: loopTrace handler nSteps (InterpreterLoop.stepWithHandler handler state)
          | none => []
      | _ => []


-- @@ L37-38 verbatim
@[simp] theorem loopTrace_zero (handler : Handler) (state : EvmState) :
    loopTrace handler 0 state = [] := rfl


-- @@ L40-46 verbatim
theorem loopTrace_succ_decode
    (handler : Handler) (nSteps : Nat) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    loopTrace handler (nSteps + 1) state =
      opcode :: loopTrace handler nSteps (InterpreterLoop.stepWithHandler handler state) := by
  simp [loopTrace, h_status, h_decode]


-- @@ L48-54 verbatim
theorem loopTrace_one_decode
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    loopTrace handler 1 state = [opcode] := by
  rw [loopTrace_succ_decode handler 0 h_status h_decode]
  rfl


-- @@ L56-62 verbatim
theorem loopTrace_one_decode_length
    (handler : Handler) {state : EvmState} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = some opcode) :
    (loopTrace handler 1 state).length = 1 := by
  rw [loopTrace_one_decode handler h_status h_decode]
  rfl


-- @@ L64-69 verbatim
theorem loopTrace_succ_unsupported
    (handler : Handler) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    loopTrace handler (nSteps + 1) state = [] := by
  simp [loopTrace, h_status, h_decode]


-- @@ L71-76 verbatim
theorem loopTrace_one_unsupported
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    loopTrace handler 1 state = [] := by
  exact loopTrace_succ_unsupported handler 0 h_status h_decode


-- @@ L78-84 verbatim
theorem loopTrace_one_unsupported_length
    (handler : Handler) {state : EvmState}
    (h_status : state.status = .running)
    (h_decode : InterpreterLoop.decodeCurrentOpcode? state = none) :
    (loopTrace handler 1 state).length = 0 := by
  rw [loopTrace_one_unsupported handler h_status h_decode]
  rfl


-- @@ L86-90 verbatim
theorem loopTrace_succ_stopped
    (handler : Handler) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .stopped) :
    loopTrace handler (nSteps + 1) state = [] := by
  simp [loopTrace, h_status]


-- @@ L92-97 verbatim
theorem loopTrace_succ_stopped_length
    (handler : Handler) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .stopped) :
    (loopTrace handler (nSteps + 1) state).length = 0 := by
  rw [loopTrace_succ_stopped handler nSteps h_status]
  rfl


-- @@ L99-103 verbatim
theorem loopTrace_succ_returned
    (handler : Handler) (nSteps : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .returned data) :
    loopTrace handler (nSteps + 1) state = [] := by
  simp [loopTrace, h_status]


-- @@ L105-110 verbatim
theorem loopTrace_succ_returned_length
    (handler : Handler) (nSteps : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .returned data) :
    (loopTrace handler (nSteps + 1) state).length = 0 := by
  rw [loopTrace_succ_returned handler nSteps h_status]
  rfl


-- @@ L112-116 verbatim
theorem loopTrace_succ_reverted
    (handler : Handler) (nSteps : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .reverted data) :
    loopTrace handler (nSteps + 1) state = [] := by
  simp [loopTrace, h_status]


-- @@ L118-123 verbatim
theorem loopTrace_succ_reverted_length
    (handler : Handler) (nSteps : Nat) {state : EvmState} {data : List (BitVec 8)}
    (h_status : state.status = .reverted data) :
    (loopTrace handler (nSteps + 1) state).length = 0 := by
  rw [loopTrace_succ_reverted handler nSteps h_status]
  rfl


-- @@ L125-129 verbatim
theorem loopTrace_succ_error
    (handler : Handler) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .error) :
    loopTrace handler (nSteps + 1) state = [] := by
  simp [loopTrace, h_status]


-- @@ L131-136 verbatim
theorem loopTrace_succ_error_length
    (handler : Handler) (nSteps : Nat) {state : EvmState}
    (h_status : state.status = .error) :
    (loopTrace handler (nSteps + 1) state).length = 0 := by
  rw [loopTrace_succ_error handler nSteps h_status]
  rfl


-- @@ L138-150 verbatim
theorem loopTrace_length_le_fuel (handler : Handler) :
    ∀ (nSteps : Nat) (state : EvmState), (loopTrace handler nSteps state).length ≤ nSteps
  | 0, _ => Nat.zero_le 0
  | nSteps + 1, state => by
      cases h_status : state.status <;>
        simp [loopTrace, h_status]
      cases h_decode : InterpreterLoop.decodeCurrentOpcode? state with
      | none =>
          simp
      | some opcode =>
          simp [
            Nat.succ_le_succ (loopTrace_length_le_fuel handler nSteps
              (InterpreterLoop.stepWithHandler handler state))]


-- @@ L152-152 verbatim
end InterpreterTrace


-- @@ L154-154 verbatim
end EvmAsm.Evm64
