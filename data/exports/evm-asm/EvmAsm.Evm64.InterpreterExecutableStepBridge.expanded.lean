/-
  EvmAsm.Evm64.InterpreterExecutableStepBridge

  Lift executable-spec byte fetch/decode facts through one running interpreter
  loop step (GH #109).
-/

module

public import EvmAsm.Evm64.InterpreterExecutableFetchBridge
public import EvmAsm.Evm64.SupportedLoopBridge


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64


-- @@ L17-17 verbatim
namespace InterpreterExecutableStepBridge


-- @@ L19-35 verbatim
/--
An executable-spec opcode byte at the current PC drives one running loop step
to the same handler result as direct opcode dispatch.

Distinctive token: InterpreterExecutableStepBridge.loopFuel_one_of_execSpecByte #109.
-/
theorem loopFuel_one_of_execSpecByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecByte
    handler h_pc h_code h_decode


-- @@ L37-47 verbatim
theorem loopFuel_one_of_roundtrip
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8} {opcode : EvmOpcode}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_roundtrip :
      EvmOpcode.byte? opcode = some byte.toNat ∧
        EvmOpcode.decodeByte? byte.toNat = some opcode) :
    InterpreterLoop.loopFuel handler 1 state = handler opcode state := by
  exact loopFuel_one_of_execSpecByte handler h_status h_pc h_code h_roundtrip.2


-- @@ L49-69 verbatim
/--
One-step running-loop bridge for executable-spec `PUSH1` through `PUSH32`
bytes.

Distinctive token:
InterpreterExecutableStepBridge.loopFuel_one_of_execSpecPushByte #109 #101.
-/
theorem loopFuel_one_of_execSpecPushByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {n : Nat}
    (h_status : state.status = .running)
    (h_low : 1 ≤ n) (h_high : n ≤ 32)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecPushByte n : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler (EvmOpcode.PUSH n) state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecPushByte
    handler h_low h_high h_pc h_code


-- @@ L71-89 verbatim
/--
One-step running-loop bridge for executable-spec `LOG0` through `LOG4` bytes.

Distinctive token:
InterpreterExecutableStepBridge.loopFuel_one_of_execSpecLogByte #109 #112.
-/
theorem loopFuel_one_of_execSpecLogByte
    (handler : InterpreterLoop.Handler)
    {state : EvmState} (kind : LogArgs.Kind)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.execSpecLogByte kind : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler (EvmOpcode.LOG kind) state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpecLogByte
    handler kind h_pc h_code


-- @@ L91-103 verbatim
theorem loopFuel_one_of_execSpec_SDIV
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler EvmOpcode.SDIV state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpec_SDIV
    handler h_pc h_code


-- @@ L105-117 verbatim
theorem loopFuel_one_of_execSpec_SMOD
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    InterpreterLoop.loopFuel handler 1 state =
      handler EvmOpcode.SMOD state := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterExecutableFetchBridge.stepWithHandler_of_execSpec_SMOD
    handler h_pc h_code


-- @@ L119-132 verbatim
theorem loopFuel_one_supported_execSpec_SDIV
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1 state =
      ArithmeticHandlers.sdivHandler state := by
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  exact SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV state


-- @@ L134-147 verbatim
theorem loopFuel_one_supported_execSpec_SMOD
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1 state =
      ArithmeticHandlers.smodHandler state := by
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  exact SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD state


-- @@ L149-159 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_pc
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).pc = state.pc := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_pc state


-- @@ L161-171 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_pc
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).pc = state.pc := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_pc state


-- @@ L173-183 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_gas
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).gas = state.gas := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_gas state


-- @@ L185-195 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_gas
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).gas = state.gas := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_gas state


-- @@ L197-207 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_code
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).code = state.code := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_code state


-- @@ L209-219 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_code
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).code = state.code := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_code state


-- @@ L221-231 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_codeLen
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).codeLen = state.codeLen := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_codeLen state


-- @@ L233-243 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_codeLen
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).codeLen = state.codeLen := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_codeLen state


-- @@ L245-255 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_env
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).env = state.env := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_env state


-- @@ L257-267 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_env
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).env = state.env := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_env state


-- @@ L269-280 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_codeLenMatches
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8))
    (h_codeLen : state.codeLenMatches) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).codeLenMatches := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_codeLenMatches state h_codeLen


-- @@ L282-293 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_codeLenMatches
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8))
    (h_codeLen : state.codeLenMatches) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).codeLenMatches := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_codeLenMatches state h_codeLen


-- @@ L295-305 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_memoryCells
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memoryCells = state.memoryCells := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_memoryCells state


-- @@ L307-317 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_memory
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memory = state.memory := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_memory state


-- @@ L319-329 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_memSize
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memSize = state.memSize := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_memSize state


-- @@ L331-341 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_memoryCells
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memoryCells = state.memoryCells := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_memoryCells state


-- @@ L343-353 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_memory
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memory = state.memory := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_memory state


-- @@ L355-365 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_memSize
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).memSize = state.memSize := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_memSize state


-- @@ L367-384 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8))
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack =
      some stack') :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = state.status := by
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]


-- @@ L386-403 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8))
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack =
      some stack') :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = state.status := by
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]


-- @@ L405-423 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8))
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).stack = out.effects.stackWords ++ out.stack := by
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_stack_of_runSDivStack?_some
    h_run


-- @@ L425-443 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8))
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).stack = out.effects.stackWords ++ out.stack := by
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_stack_of_runSModStack?_some
    h_run


-- @@ L445-459 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8))
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = state.status := by
  rw [loopFuel_one_supported_execSpec_SDIV h_status h_pc h_code]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_some
    h_run


-- @@ L461-475 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8))
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = state.status := by
  rw [loopFuel_one_supported_execSpec_SMOD h_status h_pc h_code]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_some
    h_run


-- @@ L477-494 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_status_of_none
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8))
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } = none) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = .error := by
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_none
    h_run


-- @@ L496-513 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_status_of_none
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8))
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } = none) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      state).status = .error := by
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status h_pc h_code]
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_none
    h_run


-- @@ L515-537 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_status_empty_stack
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := [] }).status = .error := by
  have h_status' :
      ({ state with stack := [] } : EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := [] } : EvmState).pc <
        ({ state with stack := [] } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := [] } : EvmState).code[
        ({ state with stack := [] } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_supported_execSpec_SDIV h_status' h_pc' h_code']
  exact SDivStackExecutionBridge.sdivHandler_status_empty_stack state


-- @@ L539-563 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_status_singleton_stack
    {state : EvmState} (dividend : EvmWord)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := [dividend] }).status = .error := by
  have h_status' :
      ({ state with stack := [dividend] } : EvmState).status =
        .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := [dividend] } : EvmState).pc <
        ({ state with stack := [dividend] } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := [dividend] } : EvmState).code[
        ({ state with stack := [dividend] } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_supported_execSpec_SDIV h_status' h_pc' h_code']
  exact SDivStackExecutionBridge.sdivHandler_status_singleton_stack
    state dividend


-- @@ L565-587 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_status_empty_stack
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := [] }).status = .error := by
  have h_status' :
      ({ state with stack := [] } : EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := [] } : EvmState).pc <
        ({ state with stack := [] } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := [] } : EvmState).code[
        ({ state with stack := [] } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_supported_execSpec_SMOD h_status' h_pc' h_code']
  exact SModStackExecutionBridge.smodHandler_status_empty_stack state


-- @@ L589-613 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_status_singleton_stack
    {state : EvmState} (dividend : EvmWord)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := [dividend] }).status = .error := by
  have h_status' :
      ({ state with stack := [dividend] } : EvmState).status =
        .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := [dividend] } : EvmState).pc <
        ({ state with stack := [dividend] } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := [dividend] } : EvmState).code[
        ({ state with stack := [dividend] } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_supported_execSpec_SMOD h_status' h_pc' h_code']
  exact SModStackExecutionBridge.smodHandler_status_singleton_stack
    state dividend


-- @@ L615-644 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_stack_zero_divisor
    {state : EvmState} (dividend : EvmWord) (rest : List EvmWord)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  have h_status' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).status =
        .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).pc <
        ({ state with stack := dividend :: 0 :: rest } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).code[
        ({ state with stack := dividend :: 0 :: rest } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_stack_zero_divisor
    state dividend rest


-- @@ L646-679 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_stack_intMin_neg_one
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack }).stack =
        BitVec.intMin 256 :: state.stack := by
  have h_status' :
      ({ state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } :
        EvmState).pc <
        ({ state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } :
        EvmState).code[
        ({ state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_stack_intMin_neg_one
    state state.stack


-- @@ L681-714 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_stack_neg_one_two
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := (-1 : EvmWord) :: 2 :: state.stack }).stack =
        0 :: state.stack := by
  have h_status' :
      ({ state with stack := (-1 : EvmWord) :: 2 :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := (-1 : EvmWord) :: 2 :: state.stack } :
        EvmState).pc <
        ({ state with stack := (-1 : EvmWord) :: 2 :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := (-1 : EvmWord) :: 2 :: state.stack } :
        EvmState).code[
        ({ state with stack := (-1 : EvmWord) :: 2 :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_stack_neg_one_two
    state state.stack


-- @@ L716-749 verbatim
theorem loopFuel_one_supported_execSpec_SDIV_stack_pos_neg_trunc
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (-3 : EvmWord) :: state.stack := by
  have h_status' :
      ({ state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).pc <
        ({ state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).code[
        ({ state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SDIV : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SDIV SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SDIV]
  exact SDivStackExecutionBridge.sdivHandler_stack_pos_neg_trunc
    state state.stack


-- @@ L751-780 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_stack_zero_divisor
    {state : EvmState} (dividend : EvmWord) (rest : List EvmWord)
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  have h_status' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).status =
        .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).pc <
        ({ state with stack := dividend :: 0 :: rest } : EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := dividend :: 0 :: rest } : EvmState).code[
        ({ state with stack := dividend :: 0 :: rest } : EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_stack_zero_divisor
    state dividend rest


-- @@ L782-815 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_stack_neg_pos_sign
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := (-3 : EvmWord) :: 2 :: state.stack }).stack =
        (-1 : EvmWord) :: state.stack := by
  have h_status' :
      ({ state with stack := (-3 : EvmWord) :: 2 :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := (-3 : EvmWord) :: 2 :: state.stack } :
        EvmState).pc <
        ({ state with stack := (-3 : EvmWord) :: 2 :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := (-3 : EvmWord) :: 2 :: state.stack } :
        EvmState).code[
        ({ state with stack := (-3 : EvmWord) :: 2 :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_stack_neg_pos_sign
    state state.stack


-- @@ L817-850 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_stack_pos_neg_sign
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (1 : EvmWord) :: state.stack := by
  have h_status' :
      ({ state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).pc <
        ({ state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).code[
        ({ state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_stack_pos_neg_sign
    state state.stack


-- @@ L852-885 verbatim
theorem loopFuel_one_supported_execSpec_SMOD_stack_neg_neg_sign
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code :
      state.code[state.pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8)) :
    (InterpreterLoop.loopFuel SupportedLoopBridge.supportedLoopHandler 1
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack }).stack =
        (-1 : EvmWord) :: state.stack := by
  have h_status' :
      ({ state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).status = .running := by
    simpa using h_status
  have h_pc' :
      ({ state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).pc <
        ({ state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).code.length := by
    simpa using h_pc
  have h_code' :
      ({ state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
        EvmState).code[
        ({ state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: state.stack } :
          EvmState).pc] =
        (ExecutableSpecOpcodeBridge.Ops.SMOD : BitVec 8) := by
    simpa using h_code
  rw [loopFuel_one_of_execSpec_SMOD SupportedLoopBridge.supportedLoopHandler
    h_status' h_pc' h_code']
  rw [SupportedLoopBridge.supportedLoopHandler_apply]
  rw [SupportedHandlers.dispatchOpcode_of_lookup
    SupportedHandlers.supportedHandlerTable_SMOD]
  exact SModStackExecutionBridge.smodHandler_stack_neg_neg_sign
    state state.stack


-- @@ L887-898 verbatim
theorem loopFuel_one_of_unsupported
    (handler : InterpreterLoop.Handler)
    {state : EvmState} {byte : BitVec 8}
    (h_status : state.status = .running)
    (h_pc : state.pc < state.code.length)
    (h_code : state.code[state.pc] = byte)
    (h_decode : EvmOpcode.decodeByte? byte.toNat = none) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterLoop.stepWithHandler_of_unsupported handler (by
    simp [InterpreterLoop.decodeCurrentOpcode?,
      InterpreterLoop.fetchOpcodeByte?, h_pc, h_code, h_decode])


-- @@ L900-907 verbatim
theorem loopFuel_one_of_eof
    (handler : InterpreterLoop.Handler)
    {state : EvmState}
    (h_status : state.status = .running)
    (h_pc : state.code.length ≤ state.pc) :
    InterpreterLoop.loopFuel handler 1 state = state.invalid := by
  rw [InterpreterLoop.loopFuel_succ_running handler 0 state h_status]
  exact InterpreterLoop.stepWithHandler_eof_invalid handler h_pc


-- @@ L909-909 verbatim
end InterpreterExecutableStepBridge


-- @@ L911-911 verbatim
end EvmAsm.Evm64
