/-
  EvmAsm.EL.KzgPointEvalEcallBridge

  Pure zkVM KZG point-evaluation accelerator ECALL surface.
-/

module

public import EvmAsm.EL.KzgPointEvalInputBridge
public import EvmAsm.EL.KzgPointEvalResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace KzgPointEvalEcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the KZG point-eval accelerator ECALL surface. -/
def kzgPointEvalSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.kzg_point_eval


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM KZG point-eval accelerator. -/
structure KzgPointEvalRequest where
  selector : Rv64Word
  input : KzgPointEvalInputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM KZG point-eval accelerator. -/
structure KzgPointEvalResult where
  status : ZkvmStatus
  output : KzgPointEvalResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the KZG point-eval accelerator request from already-loaded inputs. -/
def requestFromInput
    (input : KzgPointEvalInputBridge.AcceleratorInput) : KzgPointEvalRequest :=
  { selector := kzgPointEvalSelector, input := input }


-- @@ L40-42 verbatim
/-- Stack/precompile success word exposed by a successful KZG point-eval result. -/
def successWordFromResult (result : KzgPointEvalResult) : BitVec 256 :=
  KzgPointEvalResultBridge.successWordFromVerified result.output.verified


-- @@ L44-54 verbatim
/--
Pure execution boundary for the KZG point-eval ECALL. The proof verification
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and verified flag.
-/
def executeKzgPointEvalEcall
    (accelerator : KzgPointEvalInputBridge.AcceleratorInput →
      KzgPointEvalResultBridge.AcceleratorResult)
    (request : KzgPointEvalRequest) : KzgPointEvalResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L56-58 verbatim
theorem requestFromInput_selector
    (input : KzgPointEvalInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = kzgPointEvalSelector := rfl


-- @@ L60-62 verbatim
theorem requestFromInput_input
    (input : KzgPointEvalInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L64-69 verbatim
theorem executeKzgPointEvalEcall_status
    (accelerator : KzgPointEvalInputBridge.AcceleratorInput →
      KzgPointEvalResultBridge.AcceleratorResult)
    (request : KzgPointEvalRequest) :
    (executeKzgPointEvalEcall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L71-76 verbatim
theorem executeKzgPointEvalEcall_output
    (accelerator : KzgPointEvalInputBridge.AcceleratorInput →
      KzgPointEvalResultBridge.AcceleratorResult)
    (request : KzgPointEvalRequest) :
    (executeKzgPointEvalEcall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L78-84 verbatim
theorem executeKzgPointEvalEcall_successWord
    (accelerator : KzgPointEvalInputBridge.AcceleratorInput →
      KzgPointEvalResultBridge.AcceleratorResult)
    (request : KzgPointEvalRequest) :
    successWordFromResult (executeKzgPointEvalEcall accelerator request) =
      KzgPointEvalResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl


-- @@ L86-99 verbatim
theorem executeKzgPointEvalEcall_fromMemory_successWord
    (accelerator : KzgPointEvalInputBridge.AcceleratorInput →
      KzgPointEvalResultBridge.AcceleratorResult)
    (memory : KzgPointEvalInputBridge.MemoryReader)
    (commitmentStart zStart yStart proofStart : Nat) :
    successWordFromResult
        (executeKzgPointEvalEcall accelerator
          (requestFromInput
            (KzgPointEvalInputBridge.kzgPointEvalInputFromMemory
              memory commitmentStart zStart yStart proofStart))) =
      KzgPointEvalResultBridge.successWordFromVerified
        (accelerator
          (KzgPointEvalInputBridge.kzgPointEvalInputFromMemory
            memory commitmentStart zStart yStart proofStart)).output.verified := rfl


-- @@ L101-101 verbatim
end KzgPointEvalEcallBridge


-- @@ L103-103 verbatim
end EvmAsm.EL
