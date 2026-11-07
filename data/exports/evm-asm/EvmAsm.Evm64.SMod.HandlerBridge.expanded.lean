/-
  EvmAsm.Evm64.SMod.HandlerBridge

  Connects the pure SMOD opcode handler to the SMOD stack-execution bridge.
-/

module

public import EvmAsm.Evm64.ArithmeticHandlers
public import EvmAsm.Evm64.SMod.StackExecutionBridge


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64

-- @@ L15-15 verbatim
namespace SModStackExecutionBridge


-- @@ L17-22 verbatim
theorem smodHandler_pc
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).pc = state.pc := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L24-29 verbatim
theorem smodHandler_gas
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).gas = state.gas := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L31-37 verbatim
theorem smodHandler_memoryCells
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memoryCells =
      state.memoryCells := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L39-44 verbatim
theorem smodHandler_memory
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memory = state.memory := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L46-51 verbatim
theorem smodHandler_memSize
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).memSize = state.memSize := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L53-58 verbatim
theorem smodHandler_code
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).code = state.code := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L60-65 verbatim
theorem smodHandler_codeLen
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).codeLen = state.codeLen := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L67-72 verbatim
theorem smodHandler_env
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler state).env = state.env := by
  cases h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack <;>
    simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
      EvmState.withStack, EvmState.invalid, EvmState.withStatus, h_stack]


-- @@ L74-79 verbatim
theorem smodHandler_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (ArithmeticHandlers.smodHandler state).codeLenMatches := by
  unfold EvmState.codeLenMatches at h_codeLen ⊢
  rw [smodHandler_codeLen, smodHandler_code]
  exact h_codeLen


-- @@ L81-91 verbatim
theorem smodHandler_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  subst h_out
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    SModArgs.smodResultFromArgs_eq, SModArgs.smodArgs, h_stack]


-- @@ L93-101 verbatim
theorem smodHandler_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).status = state.status := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    EvmState.withStack, h_stack]


-- @@ L103-118 verbatim
theorem smodHandler_status_of_runSModStack?_none
    {state : EvmState}
    (h_run : runSModStack? { stack := state.stack } = none) :
    (ArithmeticHandlers.smodHandler state).status = .error := by
  cases h_stack : state.stack with
  | nil =>
      simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
        h_stack]
  | cons dividend tail =>
      cases h_tail : tail with
      | nil =>
          simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
            h_stack, h_tail]
      | cons divisor rest =>
          simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
            stackRestAfterSMod?, Option.bind, h_stack, h_tail] at h_run


-- @@ L120-124 verbatim
theorem smodHandler_status_empty_stack
    (state : EvmState) :
    (ArithmeticHandlers.smodHandler { state with stack := [] }).status =
      .error := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]


-- @@ L126-130 verbatim
theorem smodHandler_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := [dividend] }).status = .error := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]


-- @@ L132-138 verbatim
theorem smodHandler_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_zero_right


-- @@ L140-146 verbatim
theorem smodHandler_stack_intMin_neg_one
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest }).stack =
        0 :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_intMin_neg_one


-- @@ L148-154 verbatim
theorem smodHandler_stack_neg_pos_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (-3 : EvmWord) :: 2 :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_neg_pos_sign


-- @@ L156-162 verbatim
theorem smodHandler_stack_pos_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_pos_neg_sign


-- @@ L164-170 verbatim
theorem smodHandler_stack_neg_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (ArithmeticHandlers.smodHandler
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler]
  exact EvmWord.smod_neg_neg_sign


-- @@ L172-172 verbatim
end SModStackExecutionBridge

-- @@ L173-173 verbatim
end EvmAsm.Evm64
