/-
  EvmAsm.Evm64.InterpreterLoopSimulation

  Whole-loop simulation relation for the pure interpreter loop (GH #109).
-/

module

public import EvmAsm.Evm64.InterpreterSimulation


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
namespace InterpreterLoopSimulation


-- @@ L17-17 verbatim
abbrev Handler := InterpreterLoop.Handler


-- @@ L19-23 verbatim
/-- Whole-loop result agreement for all fuel budgets and starting states. -/
def LoopResultsMatch (impl spec : Handler) : Prop :=
  ∀ (fuel : Nat) (state : EvmState),
    InterpreterLoop.loopFuel impl fuel state =
      InterpreterLoop.loopFuel spec fuel state


-- @@ L25-28 verbatim
theorem LoopResultsMatch.refl (handler : Handler) :
    LoopResultsMatch handler handler := by
  intro fuel state
  rfl


-- @@ L30-34 verbatim
theorem LoopResultsMatch.symm
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec) :
    LoopResultsMatch spec impl := by
  intro fuel state
  exact (h_match fuel state).symm


-- @@ L36-42 verbatim
theorem LoopResultsMatch.trans
    {impl mid spec : Handler}
    (h_left : LoopResultsMatch impl mid)
    (h_right : LoopResultsMatch mid spec) :
    LoopResultsMatch impl spec := by
  intro fuel state
  exact (h_left fuel state).trans (h_right fuel state)


-- @@ L44-50 verbatim
/-- Distinctive token: InterpreterLoopSimulation.loopResultsMatch_of_handlerMatchesSpec #109. -/
theorem loopResultsMatch_of_handlerMatchesSpec
    {impl spec : Handler}
    (h_match : InterpreterSimulation.HandlerMatchesSpec impl spec) :
    LoopResultsMatch impl spec := by
  intro fuel state
  exact InterpreterSimulation.loopFuel_matchesSpec h_match fuel state


-- @@ L52-57 verbatim
theorem loopFuel_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    InterpreterLoop.loopFuel impl fuel state =
      InterpreterLoop.loopFuel spec fuel state :=
  h_match fuel state


-- @@ L59-64 verbatim
theorem loopFuel_status_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).status =
      (InterpreterLoop.loopFuel spec fuel state).status := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L66-71 verbatim
theorem loopFuel_pc_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).pc =
      (InterpreterLoop.loopFuel spec fuel state).pc := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L73-78 verbatim
theorem loopFuel_gas_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).gas =
      (InterpreterLoop.loopFuel spec fuel state).gas := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L80-85 verbatim
theorem loopFuel_stack_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).stack =
      (InterpreterLoop.loopFuel spec fuel state).stack := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L87-92 verbatim
theorem loopFuel_memoryCells_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).memoryCells =
      (InterpreterLoop.loopFuel spec fuel state).memoryCells := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L94-99 verbatim
theorem loopFuel_memory_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) (addr : Nat) :
    (InterpreterLoop.loopFuel impl fuel state).memory addr =
      (InterpreterLoop.loopFuel spec fuel state).memory addr := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L101-106 verbatim
theorem loopFuel_memSize_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).memSize =
      (InterpreterLoop.loopFuel spec fuel state).memSize := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L108-113 verbatim
theorem loopFuel_code_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).code =
      (InterpreterLoop.loopFuel spec fuel state).code := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L115-120 verbatim
theorem loopFuel_codeLen_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).codeLen =
      (InterpreterLoop.loopFuel spec fuel state).codeLen := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L122-127 verbatim
theorem loopFuel_codeLenMatches_iff_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).codeLenMatches ↔
      (InterpreterLoop.loopFuel spec fuel state).codeLenMatches := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L129-135 verbatim
theorem loopFuel_codeLenMatches_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel spec fuel state).codeLenMatches) :
    (InterpreterLoop.loopFuel impl fuel state).codeLenMatches := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]
  exact h_codeLen


-- @@ L137-143 verbatim
theorem loopFuel_codeLenMatches_spec_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState)
    (h_codeLen : (InterpreterLoop.loopFuel impl fuel state).codeLenMatches) :
    (InterpreterLoop.loopFuel spec fuel state).codeLenMatches := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state] at h_codeLen
  exact h_codeLen


-- @@ L145-150 verbatim
theorem loopFuel_env_eq_of_loopResultsMatch
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (fuel : Nat) (state : EvmState) :
    (InterpreterLoop.loopFuel impl fuel state).env =
      (InterpreterLoop.loopFuel spec fuel state).env := by
  rw [loopFuel_eq_of_loopResultsMatch h_match fuel state]


-- @@ L152-158 verbatim
theorem loopResultsMatch_of_eq
    {impl spec : Handler}
    (h_eq : ∀ (opcode : EvmOpcode) (state : EvmState), impl opcode state = spec opcode state) :
    LoopResultsMatch impl spec := by
  apply loopResultsMatch_of_handlerMatchesSpec
  intro opcode state _h_decode
  exact h_eq opcode state


-- @@ L160-165 verbatim
theorem loopResultsMatch_step_one
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (state : EvmState) :
    InterpreterLoop.loopFuel impl 1 state =
      InterpreterLoop.loopFuel spec 1 state :=
  h_match 1 state


-- @@ L167-172 verbatim
theorem loopResultsMatch_step_one_status
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    (state : EvmState) :
    (InterpreterLoop.loopFuel impl 1 state).status =
      (InterpreterLoop.loopFuel spec 1 state).status := by
  rw [loopResultsMatch_step_one h_match state]


-- @@ L174-182 verbatim
theorem stepWithHandler_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    InterpreterLoop.stepWithHandler impl state =
      InterpreterLoop.stepWithHandler spec state := by
  have h_loop := loopResultsMatch_step_one h_match state
  rw [InterpreterLoop.loopFuel_succ_running impl 0 state h_status] at h_loop
  rw [InterpreterLoop.loopFuel_succ_running spec 0 state h_status] at h_loop
  exact h_loop


-- @@ L184-189 verbatim
theorem stepWithHandler_status_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).status =
      (InterpreterLoop.stepWithHandler spec state).status := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L191-196 verbatim
theorem stepWithHandler_pc_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).pc =
      (InterpreterLoop.stepWithHandler spec state).pc := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L198-203 verbatim
theorem stepWithHandler_gas_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).gas =
      (InterpreterLoop.stepWithHandler spec state).gas := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L205-210 verbatim
theorem stepWithHandler_stack_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).stack =
      (InterpreterLoop.stepWithHandler spec state).stack := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L212-217 verbatim
theorem stepWithHandler_memoryCells_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).memoryCells =
      (InterpreterLoop.stepWithHandler spec state).memoryCells := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L219-224 verbatim
theorem stepWithHandler_memory_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) (addr : Nat) :
    (InterpreterLoop.stepWithHandler impl state).memory addr =
      (InterpreterLoop.stepWithHandler spec state).memory addr := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L226-231 verbatim
theorem stepWithHandler_memSize_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).memSize =
      (InterpreterLoop.stepWithHandler spec state).memSize := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L233-238 verbatim
theorem stepWithHandler_code_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).code =
      (InterpreterLoop.stepWithHandler spec state).code := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L240-245 verbatim
theorem stepWithHandler_codeLen_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).codeLen =
      (InterpreterLoop.stepWithHandler spec state).codeLen := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L247-252 verbatim
theorem stepWithHandler_codeLenMatches_iff_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).codeLenMatches ↔
      (InterpreterLoop.stepWithHandler spec state).codeLenMatches := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L254-260 verbatim
theorem stepWithHandler_codeLenMatches_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running)
    (h_codeLen : (InterpreterLoop.stepWithHandler spec state).codeLenMatches) :
    (InterpreterLoop.stepWithHandler impl state).codeLenMatches := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]
  exact h_codeLen


-- @@ L262-268 verbatim
theorem stepWithHandler_codeLenMatches_spec_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running)
    (h_codeLen : (InterpreterLoop.stepWithHandler impl state).codeLenMatches) :
    (InterpreterLoop.stepWithHandler spec state).codeLenMatches := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status] at h_codeLen
  exact h_codeLen


-- @@ L270-275 verbatim
theorem stepWithHandler_env_eq_of_loopResultsMatch_running
    {impl spec : Handler} (h_match : LoopResultsMatch impl spec)
    {state : EvmState} (h_status : state.status = .running) :
    (InterpreterLoop.stepWithHandler impl state).env =
      (InterpreterLoop.stepWithHandler spec state).env := by
  rw [stepWithHandler_eq_of_loopResultsMatch_running h_match h_status]


-- @@ L277-277 verbatim
end InterpreterLoopSimulation


-- @@ L279-279 verbatim
end EvmAsm.Evm64
