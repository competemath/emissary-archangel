/-
  EvmAsm.EL.Secp256r1VerifyEcallBridge

  Pure zkVM secp256r1 signature-verification accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Secp256r1VerifyInputBridge
public import EvmAsm.EL.Secp256r1VerifyResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Secp256r1VerifyEcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the secp256r1 verify accelerator ECALL surface. -/
def secp256r1VerifySelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.secp256r1_verify


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM secp256r1 verify accelerator. -/
structure Secp256r1VerifyRequest where
  selector : Rv64Word
  input : Secp256r1VerifyInputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM secp256r1 verify accelerator. -/
structure Secp256r1VerifyResult where
  status : ZkvmStatus
  output : Secp256r1VerifyResultBridge.AcceleratorOutput


-- @@ L35-39 verbatim
/-- Build the secp256r1 verify request from already-loaded input. -/
def requestFromInput
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    Secp256r1VerifyRequest :=
  { selector := secp256r1VerifySelector, input := input }


-- @@ L41-43 verbatim
/-- Stack/precompile success word exposed by a successful secp256r1 verify result. -/
def successWordFromResult (result : Secp256r1VerifyResult) : BitVec 256 :=
  Secp256r1VerifyResultBridge.successWordFromVerified result.output.verified


-- @@ L45-55 verbatim
/--
Pure execution boundary for the secp256r1 verify ECALL. The signature
verification itself is supplied by the accelerator model; this bridge fixes
the request/result shape, selector, status code, and verified flag.
-/
def executeSecp256r1VerifyEcall
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) : Secp256r1VerifyResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L57-59 verbatim
theorem requestFromInput_selector
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = secp256r1VerifySelector := rfl


-- @@ L61-63 verbatim
theorem requestFromInput_input
    (input : Secp256r1VerifyInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L65-70 verbatim
theorem executeSecp256r1VerifyEcall_status
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    (executeSecp256r1VerifyEcall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L72-77 verbatim
theorem executeSecp256r1VerifyEcall_output
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    (executeSecp256r1VerifyEcall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L79-85 verbatim
theorem executeSecp256r1VerifyEcall_successWord
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (request : Secp256r1VerifyRequest) :
    successWordFromResult (executeSecp256r1VerifyEcall accelerator request) =
      Secp256r1VerifyResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl


-- @@ L87-100 verbatim
theorem executeSecp256r1VerifyEcall_fromMemory_successWord
    (accelerator : Secp256r1VerifyInputBridge.AcceleratorInput →
      Secp256r1VerifyResultBridge.AcceleratorResult)
    (memory : Secp256r1VerifyInputBridge.MemoryReader)
    (msgStart sigStart pubkeyStart : Nat) :
    successWordFromResult
        (executeSecp256r1VerifyEcall accelerator
          (requestFromInput
            (Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
              memory msgStart sigStart pubkeyStart))) =
      Secp256r1VerifyResultBridge.successWordFromVerified
        (accelerator
          (Secp256r1VerifyInputBridge.secp256r1VerifyInputFromMemory
            memory msgStart sigStart pubkeyStart)).output.verified := rfl


-- @@ L102-102 verbatim
end Secp256r1VerifyEcallBridge


-- @@ L104-104 verbatim
end EvmAsm.EL
