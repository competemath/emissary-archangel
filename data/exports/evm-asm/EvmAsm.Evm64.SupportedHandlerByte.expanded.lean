/-
  EvmAsm.Evm64.SupportedHandlerByte

  Raw-byte dispatch bridge for the combined supported interpreter handler
  table (GH #106 / GH #107).
-/

module

public import EvmAsm.Evm64.HandlerTableByte
public import EvmAsm.Evm64.SDiv.HandlerBridge
public import EvmAsm.Evm64.SMod.HandlerBridge
public import EvmAsm.Evm64.SupportedHandlers


-- @@ L15-15 verbatim
public section


-- @@ L17-17 verbatim
namespace EvmAsm.Evm64

-- @@ L18-18 verbatim
namespace SupportedHandlerByte


-- @@ L20-30 verbatim
theorem dispatchByte_supported_of_lookup
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      handler state := by
  rw [HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode]
  exact SupportedHandlers.dispatchOpcode_of_lookup h_lookup state


-- @@ L32-40 verbatim
theorem dispatchByte_supported_of_lookup_status
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (handler state).status := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L42-50 verbatim
theorem dispatchByte_supported_of_lookup_pc
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).pc =
      (handler state).pc := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L52-60 verbatim
theorem dispatchByte_supported_of_lookup_gas
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).gas =
      (handler state).gas := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L62-70 verbatim
theorem dispatchByte_supported_of_lookup_stack
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).stack =
      (handler state).stack := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L72-80 verbatim
theorem dispatchByte_supported_of_lookup_memoryCells
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memoryCells =
      (handler state).memoryCells := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L82-90 verbatim
theorem dispatchByte_supported_of_lookup_memory
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) (addr : Nat) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memory addr =
      (handler state).memory addr := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L92-100 verbatim
theorem dispatchByte_supported_of_lookup_memSize
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).memSize =
      (handler state).memSize := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L102-110 verbatim
theorem dispatchByte_supported_of_lookup_code
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).code =
      (handler state).code := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L112-120 verbatim
theorem dispatchByte_supported_of_lookup_codeLen
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).codeLen =
      (handler state).codeLen := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L122-130 verbatim
theorem dispatchByte_supported_of_lookup_env
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).env =
      (handler state).env := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]


-- @@ L132-148 verbatim
/--
Decoded byte dispatch through the supported table preserves status whenever the
looked-up handler does.

Distinctive token: supportedByteLookupPreservesStatus #107.
-/
theorem dispatchByte_supported_of_lookup_preserves_status
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (h_status : ∀ state : EvmState, (handler state).status = state.status)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      state.status := by
  rw [dispatchByte_supported_of_lookup_status h_decode h_lookup state]
  exact h_status state


-- @@ L150-166 verbatim
/--
Decoded byte dispatch through the supported table preserves `codeLenMatches`
whenever the looked-up handler does.

Distinctive token: supportedByteLookupPreservesCodeLenMatches #107.
-/
theorem dispatchByte_supported_of_lookup_preserves_codeLenMatches
    {b : Fin 256} {opcode : EvmOpcode} {handler : OpcodeHandler}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (h_lookup :
      SupportedHandlers.supportedHandlerTable opcode = some handler)
    (h_codeLen : ∀ state : EvmState,
      state.codeLenMatches → (handler state).codeLenMatches)
    (state : EvmState) (h_state : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).codeLenMatches := by
  rw [dispatchByte_supported_of_lookup h_decode h_lookup state]
  exact h_codeLen state h_state


-- @@ L168-176 verbatim
theorem dispatchByte_supported_of_decode
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state := by
  exact HandlerTable.dispatchByte_decoded
    SupportedHandlers.supportedHandlerTable b opcode state h_decode


-- @@ L178-185 verbatim
theorem dispatchByte_supported_of_decode_status
    {b : Fin 256} {opcode : EvmOpcode}
    (h_decode : EvmOpcode.decodeByte? b.val = some opcode)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      (HandlerTable.dispatchOpcode SupportedHandlers.supportedHandlerTable
        opcode state).status := by
  rw [dispatchByte_supported_of_decode h_decode state]


-- @@ L187-206 verbatim
/--
Byte-level dispatch of a decoded valid PUSH opcode through the combined
supported-handler table has the same program-counter and stack effect as the
executable PUSH bridge.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_effectFromCode #101 #107.
-/
theorem dispatchByte_supported_PUSH_effectFromCode
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).pc =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).pc ∧
      (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).stack =
        (PushExecEffect.effectFromCode state.code state.pc n state.stack).stack := by
  rw [dispatchByte_supported_of_decode h_decode state]
  exact SupportedHandlers.dispatchOpcode_supportedHandlerTable_PUSH_effectFromCode
    h_valid state


-- @@ L208-225 verbatim
/--
Status projection for byte-level dispatch of a decoded valid PUSH opcode
through the combined supported-handler table.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_PUSH_status #101 #107.
-/
theorem dispatchByte_supported_PUSH_status
    {b : Fin 256} {n : Nat}
    (h_decode : EvmOpcode.decodeByte? b.val = some (EvmOpcode.PUSH n))
    (h_valid : EvmOpcode.validPushWidth n = true)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      state.status := by
  rw [dispatchByte_supported_of_decode h_decode state]
  rw [HandlerTable.dispatchOpcode_some
    (SupportedHandlers.supportedHandlerTable_PUSH_of_valid h_valid) state]
  exact PushHandlers.pushHandler_status n state


-- @@ L227-239 verbatim
/--
Concrete STOP byte dispatch through the combined supported-handler table
terminates the state successfully.

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_byte #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state = state.stop := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_STOP
    SupportedHandlers.supportedHandlerTable_STOP state


-- @@ L241-246 verbatim
@[simp] theorem dispatchByte_supported_STOP_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x00, by decide⟩ : Fin 256) state).status = .stopped := by
  rw [dispatchByte_supported_STOP_byte]
  exact EvmState.stop_status state


-- @@ L248-253 verbatim
theorem dispatchByte_supported_INVALID_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state = state.invalid := by
  exact dispatchByte_supported_of_lookup EvmOpcode.decodeByte?_INVALID
    SupportedHandlers.supportedHandlerTable_INVALID state


-- @@ L255-260 verbatim
@[simp] theorem dispatchByte_supported_INVALID_byte_status
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0xfe, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_INVALID_byte]
  exact EvmState.invalid_status state


-- @@ L262-268 verbatim
theorem dispatchByte_supported_SDIV_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state =
        ArithmeticHandlers.sdivHandler state := by
  exact dispatchByte_supported_of_lookup rfl
    SupportedHandlers.supportedHandlerTable_SDIV state


-- @@ L270-276 verbatim
theorem dispatchByte_supported_SMOD_byte
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state =
        ArithmeticHandlers.smodHandler state := by
  exact dispatchByte_supported_of_lookup rfl
    SupportedHandlers.supportedHandlerTable_SMOD state


-- @@ L278-283 verbatim
theorem dispatchByte_supported_SDIV_byte_pc
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).pc = state.pc := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_pc state


-- @@ L285-290 verbatim
theorem dispatchByte_supported_SMOD_byte_pc
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).pc = state.pc := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_pc state


-- @@ L292-297 verbatim
theorem dispatchByte_supported_SDIV_byte_gas
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).gas = state.gas := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_gas state


-- @@ L299-304 verbatim
theorem dispatchByte_supported_SMOD_byte_gas
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).gas = state.gas := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_gas state


-- @@ L306-311 verbatim
theorem dispatchByte_supported_SDIV_byte_code
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).code = state.code := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_code state


-- @@ L313-318 verbatim
theorem dispatchByte_supported_SMOD_byte_code
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).code = state.code := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_code state


-- @@ L320-326 verbatim
theorem dispatchByte_supported_SDIV_byte_codeLen
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).codeLen =
        state.codeLen := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_codeLen state


-- @@ L328-334 verbatim
theorem dispatchByte_supported_SMOD_byte_codeLen
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).codeLen =
        state.codeLen := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_codeLen state


-- @@ L336-341 verbatim
theorem dispatchByte_supported_SDIV_byte_env
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).env = state.env := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_env state


-- @@ L343-348 verbatim
theorem dispatchByte_supported_SMOD_byte_env
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).env = state.env := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_env state


-- @@ L350-355 verbatim
theorem dispatchByte_supported_SDIV_byte_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).codeLenMatches := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_codeLenMatches state h_codeLen


-- @@ L357-362 verbatim
theorem dispatchByte_supported_SMOD_byte_codeLenMatches
    (state : EvmState) (h_codeLen : state.codeLenMatches) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).codeLenMatches := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_codeLenMatches state h_codeLen


-- @@ L364-370 verbatim
theorem dispatchByte_supported_SDIV_byte_memoryCells
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memoryCells =
        state.memoryCells := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memoryCells state


-- @@ L372-377 verbatim
theorem dispatchByte_supported_SDIV_byte_memory
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memory = state.memory := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memory state


-- @@ L379-385 verbatim
theorem dispatchByte_supported_SDIV_byte_memSize
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).memSize =
        state.memSize := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_memSize state


-- @@ L387-393 verbatim
theorem dispatchByte_supported_SMOD_byte_memoryCells
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memoryCells =
        state.memoryCells := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memoryCells state


-- @@ L395-400 verbatim
theorem dispatchByte_supported_SMOD_byte_memory
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memory = state.memory := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memory state


-- @@ L402-408 verbatim
theorem dispatchByte_supported_SMOD_byte_memSize
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).memSize =
        state.memSize := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_memSize state


-- @@ L410-418 verbatim
theorem dispatchByte_supported_SDIV_byte_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_zero_divisor
    state dividend rest


-- @@ L420-427 verbatim
theorem dispatchByte_supported_SDIV_byte_stack_intMin_neg_one
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest }).stack =
        BitVec.intMin 256 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_intMin_neg_one state rest


-- @@ L429-436 verbatim
theorem dispatchByte_supported_SDIV_byte_stack_neg_one_two
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := (-1 : EvmWord) :: 2 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_neg_one_two state rest


-- @@ L438-445 verbatim
theorem dispatchByte_supported_SDIV_byte_stack_pos_neg_trunc
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := (7 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-3 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_pos_neg_trunc state rest


-- @@ L447-455 verbatim
theorem dispatchByte_supported_SMOD_byte_stack_zero_divisor
    (state : EvmState) (dividend : EvmWord) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := dividend :: 0 :: rest }).stack =
        0 :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_zero_divisor
    state dividend rest


-- @@ L457-464 verbatim
theorem dispatchByte_supported_SMOD_byte_stack_neg_pos_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (-3 : EvmWord) :: 2 :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_neg_pos_sign state rest


-- @@ L466-473 verbatim
theorem dispatchByte_supported_SMOD_byte_stack_pos_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_pos_neg_sign state rest


-- @@ L475-482 verbatim
theorem dispatchByte_supported_SMOD_byte_stack_neg_neg_sign
    (state : EvmState) (rest : List EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := (-3 : EvmWord) :: (-2 : EvmWord) :: rest }).stack =
        (-1 : EvmWord) :: rest := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_neg_neg_sign state rest


-- @@ L484-494 verbatim
theorem dispatchByte_supported_SDIV_byte_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).stack =
        out.effects.stackWords ++ out.stack := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_stack_of_runSDivStack?_some
    h_run


-- @@ L496-506 verbatim
theorem dispatchByte_supported_SMOD_byte_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).stack =
        out.effects.stackWords ++ out.stack := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_stack_of_runSModStack?_some
    h_run


-- @@ L508-518 verbatim
theorem dispatchByte_supported_SDIV_byte_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackExecutionBridge.SDivStackResult}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status =
        state.status := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_some
    h_run


-- @@ L520-530 verbatim
theorem dispatchByte_supported_SMOD_byte_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackExecutionBridge.SModStackResult}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        some out) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status =
        state.status := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_some
    h_run


-- @@ L532-538 verbatim
theorem dispatchByte_supported_SDIV_byte_status_empty_stack
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := [] }).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_empty_stack state


-- @@ L540-547 verbatim
theorem dispatchByte_supported_SDIV_byte_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256)
      { state with stack := [dividend] }).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_singleton_stack
    state dividend


-- @@ L549-555 verbatim
theorem dispatchByte_supported_SMOD_byte_status_empty_stack
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := [] }).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_empty_stack state


-- @@ L557-564 verbatim
theorem dispatchByte_supported_SMOD_byte_status_singleton_stack
    (state : EvmState) (dividend : EvmWord) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256)
      { state with stack := [dividend] }).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_singleton_stack
    state dividend


-- @@ L566-575 verbatim
theorem dispatchByte_supported_SDIV_byte_status_of_runSDivStack?_none
    {state : EvmState}
    (h_run :
      SDivStackExecutionBridge.runSDivStack? { stack := state.stack } =
        none) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_SDIV_byte]
  exact SDivStackExecutionBridge.sdivHandler_status_of_runSDivStack?_none
    h_run


-- @@ L577-586 verbatim
theorem dispatchByte_supported_SMOD_byte_status_of_runSModStack?_none
    {state : EvmState}
    (h_run :
      SModStackExecutionBridge.runSModStack? { stack := state.stack } =
        none) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status = .error := by
  rw [dispatchByte_supported_SMOD_byte]
  exact SModStackExecutionBridge.smodHandler_status_of_runSModStack?_none
    h_run


-- @@ L588-596 verbatim
@[simp] theorem dispatchByte_supported_SDIV_byte_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.sdiv state.stack =
      some stack') :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x05, by decide⟩ : Fin 256) state).status = state.status := by
  rw [dispatchByte_supported_SDIV_byte]
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]


-- @@ L598-606 verbatim
@[simp] theorem dispatchByte_supported_SMOD_byte_status_of_some
    {state : EvmState} {stack' : List EvmWord}
    (h_stack : ArithmeticHandlers.binaryStack? EvmWord.smod state.stack =
      some stack') :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable
      (⟨0x07, by decide⟩ : Fin 256) state).status = state.status := by
  rw [dispatchByte_supported_SMOD_byte]
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    h_stack, EvmState.withStack]


-- @@ L608-614 verbatim
theorem dispatchByte_supported_undecoded
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  exact HandlerTable.dispatchByte_undecoded
    SupportedHandlers.supportedHandlerTable b state h_decode


-- @@ L616-622 verbatim
theorem dispatchByte_supported_undecoded_status
    {b : Fin 256} (h_decode : EvmOpcode.decodeByte? b.val = none)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  exact HandlerTable.dispatchByte_undecoded_status
    SupportedHandlers.supportedHandlerTable b state h_decode


-- @@ L624-640 verbatim
/--
Byte-level dispatch of any byte that decodes to STOP through the combined
supported-handler table executes the `state.stop` step. Generalises the
concrete `dispatchByte_supported_STOP_byte` (which is the `b = 0x00` instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_STOP_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_STOP_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.stop := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_STOP state]
  rfl


-- @@ L642-650 verbatim
/-- Status projection of `dispatchByte_supported_STOP_of_decode`. -/
theorem dispatchByte_supported_STOP_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .STOP)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .stopped := by
  rw [dispatchByte_supported_STOP_of_decode h_decode state]
  exact EvmState.stop_status state


-- @@ L652-669 verbatim
/--
Byte-level dispatch of any byte that decodes to INVALID through the combined
supported-handler table executes the `state.invalid` step. Generalises the
concrete `dispatchByte_supported_INVALID_byte` (which is the `b = 0xfe`
instance).

Distinctive token:
SupportedHandlerByte.dispatchByte_supported_INVALID_of_decode #106 #107 #113.
-/
theorem dispatchByte_supported_INVALID_of_decode
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state =
      state.invalid := by
  rw [dispatchByte_supported_of_lookup h_decode
    SupportedHandlers.supportedHandlerTable_INVALID state]
  rfl


-- @@ L671-679 verbatim
/-- Status projection of `dispatchByte_supported_INVALID_of_decode`. -/
theorem dispatchByte_supported_INVALID_of_decode_status
    {b : Fin 256}
    (h_decode : EvmOpcode.decodeByte? b.val = some .INVALID)
    (state : EvmState) :
    (HandlerTable.dispatchByte SupportedHandlers.supportedHandlerTable b state).status =
      .error := by
  rw [dispatchByte_supported_INVALID_of_decode h_decode state]
  exact EvmState.invalid_status state


-- @@ L681-681 verbatim
end SupportedHandlerByte

-- @@ L682-682 verbatim
end EvmAsm.Evm64
