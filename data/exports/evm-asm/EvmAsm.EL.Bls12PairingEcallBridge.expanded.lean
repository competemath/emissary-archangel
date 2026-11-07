/-
  EvmAsm.EL.Bls12PairingEcallBridge

  Pure zkVM BLS12-381 pairing accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12PairingInputBridge
public import EvmAsm.EL.Bls12PairingResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12PairingEcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the BLS12-381 pairing accelerator ECALL surface. -/
def bls12PairingSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_pairing


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM BLS12-381 pairing accelerator. -/
structure Bls12PairingRequest where
  selector : Rv64Word
  input : Bls12PairingInputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM BLS12-381 pairing accelerator. -/
structure Bls12PairingResult where
  status : ZkvmStatus
  output : Bls12PairingResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the BLS12-381 pairing accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bls12PairingInputBridge.AcceleratorInput) : Bls12PairingRequest :=
  { selector := bls12PairingSelector, input := input }


-- @@ L40-42 verbatim
/-- Stack/precompile success word exposed by a successful BLS12-381 pairing result. -/
def successWordFromResult (result : Bls12PairingResult) : BitVec 256 :=
  Bls12PairingResultBridge.successWordFromVerified result.output.verified


-- @@ L44-54 verbatim
/--
Pure execution boundary for the BLS12-381 pairing ECALL. The pairing check
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and verified flag.
-/
def executeBls12PairingEcall
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) : Bls12PairingResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L56-58 verbatim
theorem requestFromInput_selector
    (input : Bls12PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12PairingSelector := rfl


-- @@ L60-62 verbatim
theorem requestFromInput_input
    (input : Bls12PairingInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L64-69 verbatim
theorem executeBls12PairingEcall_status
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    (executeBls12PairingEcall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L71-76 verbatim
theorem executeBls12PairingEcall_output
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    (executeBls12PairingEcall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L78-84 verbatim
theorem executeBls12PairingEcall_successWord
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (request : Bls12PairingRequest) :
    successWordFromResult (executeBls12PairingEcall accelerator request) =
      Bls12PairingResultBridge.successWordFromVerified
        (accelerator request.input).output.verified := rfl


-- @@ L86-99 verbatim
theorem executeBls12PairingEcall_fromMemory_successWord
    (accelerator : Bls12PairingInputBridge.AcceleratorInput →
      Bls12PairingResultBridge.AcceleratorResult)
    (memory : Bls12PairingInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    successWordFromResult
        (executeBls12PairingEcall accelerator
          (requestFromInput
            (Bls12PairingInputBridge.bls12PairingInputFromMemory
              memory pairsStart numPairs))) =
      Bls12PairingResultBridge.successWordFromVerified
        (accelerator
          (Bls12PairingInputBridge.bls12PairingInputFromMemory
            memory pairsStart numPairs)).output.verified := rfl


-- @@ L101-101 verbatim
end Bls12PairingEcallBridge


-- @@ L103-103 verbatim
end EvmAsm.EL
