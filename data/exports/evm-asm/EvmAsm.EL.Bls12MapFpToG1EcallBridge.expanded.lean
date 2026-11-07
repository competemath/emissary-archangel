/-
  EvmAsm.EL.Bls12MapFpToG1EcallBridge

  Pure zkVM BLS12-381 map-Fp-to-G1 accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12MapFpToG1InputBridge
public import EvmAsm.EL.Bls12MapFpToG1ResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12MapFpToG1EcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the BLS12-381 map-Fp-to-G1 accelerator ECALL surface. -/
def bls12MapFpToG1Selector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_map_fp_to_g1


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM BLS12-381 map-Fp-to-G1 accelerator. -/
structure Bls12MapFpToG1Request where
  selector : Rv64Word
  input : Bls12MapFpToG1InputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM BLS12-381 map-Fp-to-G1 accelerator. -/
structure Bls12MapFpToG1Result where
  status : ZkvmStatus
  output : Bls12MapFpToG1ResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the BLS12-381 map-Fp-to-G1 accelerator request from an already-loaded input. -/
def requestFromInput
    (input : Bls12MapFpToG1InputBridge.AcceleratorInput) : Bls12MapFpToG1Request :=
  { selector := bls12MapFpToG1Selector, input := input }


-- @@ L40-43 verbatim
/-- Project the output point exposed by a successful BLS12-381 map-Fp-to-G1 result. -/
def outputPointFromResult (result : Bls12MapFpToG1Result) :
    Bls12MapFpToG1ResultBridge.G1PointBytes :=
  result.output.point


-- @@ L45-55 verbatim
/--
Pure execution boundary for the BLS12-381 map-Fp-to-G1 ECALL. The curve operation
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12MapFpToG1Ecall
    (accelerator : Bls12MapFpToG1InputBridge.AcceleratorInput →
      Bls12MapFpToG1ResultBridge.AcceleratorResult)
    (request : Bls12MapFpToG1Request) : Bls12MapFpToG1Result :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L57-59 verbatim
theorem requestFromInput_selector
    (input : Bls12MapFpToG1InputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12MapFpToG1Selector := rfl


-- @@ L61-63 verbatim
theorem requestFromInput_input
    (input : Bls12MapFpToG1InputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L65-70 verbatim
theorem executeBls12MapFpToG1Ecall_status
    (accelerator : Bls12MapFpToG1InputBridge.AcceleratorInput →
      Bls12MapFpToG1ResultBridge.AcceleratorResult)
    (request : Bls12MapFpToG1Request) :
    (executeBls12MapFpToG1Ecall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L72-77 verbatim
theorem executeBls12MapFpToG1Ecall_output
    (accelerator : Bls12MapFpToG1InputBridge.AcceleratorInput →
      Bls12MapFpToG1ResultBridge.AcceleratorResult)
    (request : Bls12MapFpToG1Request) :
    (executeBls12MapFpToG1Ecall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L79-84 verbatim
theorem executeBls12MapFpToG1Ecall_outputPoint
    (accelerator : Bls12MapFpToG1InputBridge.AcceleratorInput →
      Bls12MapFpToG1ResultBridge.AcceleratorResult)
    (request : Bls12MapFpToG1Request) :
    outputPointFromResult (executeBls12MapFpToG1Ecall accelerator request) =
      (accelerator request.input).output.point := rfl


-- @@ L86-98 verbatim
theorem executeBls12MapFpToG1Ecall_fromMemory_outputPoint
    (accelerator : Bls12MapFpToG1InputBridge.AcceleratorInput →
      Bls12MapFpToG1ResultBridge.AcceleratorResult)
    (memory : Bls12MapFpToG1InputBridge.MemoryReader)
    (fpStart : Nat) :
    outputPointFromResult
        (executeBls12MapFpToG1Ecall accelerator
          (requestFromInput
            (Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory
              memory fpStart))) =
      (accelerator
        (Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory
          memory fpStart)).output.point := rfl


-- @@ L100-100 verbatim
end Bls12MapFpToG1EcallBridge


-- @@ L102-102 verbatim
end EvmAsm.EL
