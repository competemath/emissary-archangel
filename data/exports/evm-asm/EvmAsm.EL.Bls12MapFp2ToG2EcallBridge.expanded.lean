/-
  EvmAsm.EL.Bls12MapFp2ToG2EcallBridge

  Pure zkVM BLS12-381 map-Fp2-to-G2 accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12MapFp2ToG2InputBridge
public import EvmAsm.EL.Bls12MapFp2ToG2ResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12MapFp2ToG2EcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the BLS12-381 map-Fp2-to-G2 accelerator ECALL surface. -/
def bls12MapFp2ToG2Selector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_map_fp2_to_g2


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM BLS12-381 map-Fp2-to-G2 accelerator. -/
structure Bls12MapFp2ToG2Request where
  selector : Rv64Word
  input : Bls12MapFp2ToG2InputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM BLS12-381 map-Fp2-to-G2 accelerator. -/
structure Bls12MapFp2ToG2Result where
  status : ZkvmStatus
  output : Bls12MapFp2ToG2ResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the BLS12-381 map-Fp2-to-G2 request from already-loaded input. -/
def requestFromInput
    (input : Bls12MapFp2ToG2InputBridge.AcceleratorInput) : Bls12MapFp2ToG2Request :=
  { selector := bls12MapFp2ToG2Selector, input := input }


-- @@ L40-43 verbatim
/-- Project the output point exposed by a successful BLS12-381 map-Fp2-to-G2 result. -/
def outputPointFromResult (result : Bls12MapFp2ToG2Result) :
    Bls12MapFp2ToG2ResultBridge.G2PointBytes :=
  result.output.point


-- @@ L45-55 verbatim
/--
Pure execution boundary for the BLS12-381 map-Fp2-to-G2 ECALL. The map
operation itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12MapFp2ToG2Ecall
    (accelerator : Bls12MapFp2ToG2InputBridge.AcceleratorInput →
      Bls12MapFp2ToG2ResultBridge.AcceleratorResult)
    (request : Bls12MapFp2ToG2Request) : Bls12MapFp2ToG2Result :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L57-59 verbatim
theorem requestFromInput_selector
    (input : Bls12MapFp2ToG2InputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12MapFp2ToG2Selector := rfl


-- @@ L61-63 verbatim
theorem requestFromInput_input
    (input : Bls12MapFp2ToG2InputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L65-70 verbatim
theorem executeBls12MapFp2ToG2Ecall_status
    (accelerator : Bls12MapFp2ToG2InputBridge.AcceleratorInput →
      Bls12MapFp2ToG2ResultBridge.AcceleratorResult)
    (request : Bls12MapFp2ToG2Request) :
    (executeBls12MapFp2ToG2Ecall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L72-77 verbatim
theorem executeBls12MapFp2ToG2Ecall_output
    (accelerator : Bls12MapFp2ToG2InputBridge.AcceleratorInput →
      Bls12MapFp2ToG2ResultBridge.AcceleratorResult)
    (request : Bls12MapFp2ToG2Request) :
    (executeBls12MapFp2ToG2Ecall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L79-84 verbatim
theorem executeBls12MapFp2ToG2Ecall_outputPoint
    (accelerator : Bls12MapFp2ToG2InputBridge.AcceleratorInput →
      Bls12MapFp2ToG2ResultBridge.AcceleratorResult)
    (request : Bls12MapFp2ToG2Request) :
    outputPointFromResult (executeBls12MapFp2ToG2Ecall accelerator request) =
      (accelerator request.input).output.point := rfl


-- @@ L86-98 verbatim
theorem executeBls12MapFp2ToG2Ecall_fromMemory_outputPoint
    (accelerator : Bls12MapFp2ToG2InputBridge.AcceleratorInput →
      Bls12MapFp2ToG2ResultBridge.AcceleratorResult)
    (memory : Bls12MapFp2ToG2InputBridge.MemoryReader)
    (fp2Start : Nat) :
    outputPointFromResult
        (executeBls12MapFp2ToG2Ecall accelerator
          (requestFromInput
            (Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory
              memory fp2Start))) =
      (accelerator
        (Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory
          memory fp2Start)).output.point := rfl


-- @@ L100-100 verbatim
end Bls12MapFp2ToG2EcallBridge


-- @@ L102-102 verbatim
end EvmAsm.EL
