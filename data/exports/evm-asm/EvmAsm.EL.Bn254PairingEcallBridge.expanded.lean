/-
  EvmAsm.EL.Bn254PairingEcallBridge

  Pure zkVM BN254 pairing accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bn254PairingInputBridge
public import EvmAsm.EL.Bn254PairingResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bn254PairingEcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the BN254 pairing accelerator ECALL surface. -/
def bn254PairingSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bn254_pairing


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM BN254 pairing accelerator. -/
structure Bn254PairingRequest where
  selector : Rv64Word
  input : Bn254PairingInputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM BN254 pairing accelerator. -/
structure Bn254PairingResult where
  status : ZkvmStatus
  output : Bn254PairingResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the BN254 pairing accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bn254PairingInputBridge.AcceleratorInput) : Bn254PairingRequest :=
  { selector := bn254PairingSelector, input := input }


-- @@ L40-42 verbatim
/-- Stack/precompile success word exposed by a successful BN254 pairing result. -/
def successWordFromResult (result : Bn254PairingResult) : BitVec 256 :=
  Bn254PairingResultBridge.successWordFromVerified result.output.verified


-- @@ L44-54 verbatim
/--
Pure execution boundary for the BN254 pairing ECALL. The pairing check itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, selector, status code, and verified flag.
-/
def executeBn254PairingEcall
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) : Bn254PairingResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L56-58 verbatim
theorem requestFromInput_selector
    (input : Bn254PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bn254PairingSelector := rfl


-- @@ L60-62 verbatim
theorem requestFromInput_input
    (input : Bn254PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L64-69 verbatim
theorem executeBn254PairingEcall_status
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    (executeBn254PairingEcall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L71-76 verbatim
theorem executeBn254PairingEcall_output
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    (executeBn254PairingEcall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L78-84 verbatim
theorem executeBn254PairingEcall_successWord
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (request : Bn254PairingRequest) :
    successWordFromResult (executeBn254PairingEcall accelerator request) =
      Bn254PairingResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl


-- @@ L86-99 verbatim
theorem executeBn254PairingEcall_fromMemory_successWord
    (accelerator : Bn254PairingInputBridge.AcceleratorInput →
      Bn254PairingResultBridge.AcceleratorResult)
    (memory : Bn254PairingInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    successWordFromResult
        (executeBn254PairingEcall accelerator
          (requestFromInput
            (Bn254PairingInputBridge.bn254PairingInputFromMemory
              memory pairsStart numPairs))) =
      Bn254PairingResultBridge.successWordFromVerified
        (accelerator
          (Bn254PairingInputBridge.bn254PairingInputFromMemory
            memory pairsStart numPairs)).output.verified := rfl


-- @@ L101-101 verbatim
end Bn254PairingEcallBridge


-- @@ L103-103 verbatim
end EvmAsm.EL
