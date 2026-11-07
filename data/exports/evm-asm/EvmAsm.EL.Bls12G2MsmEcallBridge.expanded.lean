/-
  EvmAsm.EL.Bls12G2MsmEcallBridge

  Pure zkVM BLS12-381 G2 MSM accelerator ECALL surface.
-/

module

public import EvmAsm.EL.Bls12G2MsmInputBridge
public import EvmAsm.EL.Bls12G2MsmResultBridge
public import EvmAsm.Evm64.Accelerators.SyscallIds


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12G2MsmEcallBridge


-- @@ L19-19 verbatim
abbrev Rv64Word := BitVec 64

-- @@ L20-20 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L22-23 verbatim
/-- Selector reserved for the BLS12-381 G2 MSM accelerator ECALL surface. -/
def bls12G2MsmSelector : Rv64Word := EvmAsm.Rv64.SyscallIdWord.bls12_g2_msm


-- @@ L25-28 verbatim
/-- ECALL request passed to the zkVM BLS12-381 G2 MSM accelerator. -/
structure Bls12G2MsmRequest where
  selector : Rv64Word
  input : Bls12G2MsmInputBridge.AcceleratorInput


-- @@ L30-33 verbatim
/-- ECALL result returned by the zkVM BLS12-381 G2 MSM accelerator. -/
structure Bls12G2MsmResult where
  status : ZkvmStatus
  output : Bls12G2MsmResultBridge.AcceleratorOutput


-- @@ L35-38 verbatim
/-- Build the BLS12-381 G2 MSM accelerator request from already-loaded input pairs. -/
def requestFromInput
    (input : Bls12G2MsmInputBridge.AcceleratorInput) : Bls12G2MsmRequest :=
  { selector := bls12G2MsmSelector, input := input }


-- @@ L40-43 verbatim
/-- Project the output point exposed by a successful BLS12-381 G2 MSM result. -/
def outputPointFromResult (result : Bls12G2MsmResult) :
    Bls12G2MsmInputBridge.G2PointBytes :=
  result.output.point


-- @@ L45-55 verbatim
/--
Pure execution boundary for the BLS12-381 G2 MSM ECALL. The curve operation
itself is supplied by the accelerator model; this bridge fixes the
request/result shape, selector, status code, and output buffer.
-/
def executeBls12G2MsmEcall
    (accelerator : Bls12G2MsmInputBridge.AcceleratorInput →
      Bls12G2MsmResultBridge.AcceleratorResult)
    (request : Bls12G2MsmRequest) : Bls12G2MsmResult :=
  let result := accelerator request.input
  { status := result.status, output := result.output }


-- @@ L57-59 verbatim
theorem requestFromInput_selector
    (input : Bls12G2MsmInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = bls12G2MsmSelector := rfl


-- @@ L61-63 verbatim
theorem requestFromInput_input
    (input : Bls12G2MsmInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl


-- @@ L65-70 verbatim
theorem executeBls12G2MsmEcall_status
    (accelerator : Bls12G2MsmInputBridge.AcceleratorInput →
      Bls12G2MsmResultBridge.AcceleratorResult)
    (request : Bls12G2MsmRequest) :
    (executeBls12G2MsmEcall accelerator request).status =
      (accelerator request.input).status := rfl


-- @@ L72-77 verbatim
theorem executeBls12G2MsmEcall_output
    (accelerator : Bls12G2MsmInputBridge.AcceleratorInput →
      Bls12G2MsmResultBridge.AcceleratorResult)
    (request : Bls12G2MsmRequest) :
    (executeBls12G2MsmEcall accelerator request).output =
      (accelerator request.input).output := rfl


-- @@ L79-84 verbatim
theorem executeBls12G2MsmEcall_outputPoint
    (accelerator : Bls12G2MsmInputBridge.AcceleratorInput →
      Bls12G2MsmResultBridge.AcceleratorResult)
    (request : Bls12G2MsmRequest) :
    outputPointFromResult (executeBls12G2MsmEcall accelerator request) =
      (accelerator request.input).output.point := rfl


-- @@ L86-98 verbatim
theorem executeBls12G2MsmEcall_fromMemory_outputPoint
    (accelerator : Bls12G2MsmInputBridge.AcceleratorInput →
      Bls12G2MsmResultBridge.AcceleratorResult)
    (memory : Bls12G2MsmInputBridge.MemoryReader)
    (pairsStart numPairs : Nat) :
    outputPointFromResult
        (executeBls12G2MsmEcall accelerator
          (requestFromInput
            (Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory
              memory pairsStart numPairs))) =
      (accelerator
        (Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory
          memory pairsStart numPairs)).output.point := rfl


-- @@ L100-100 verbatim
end Bls12G2MsmEcallBridge


-- @@ L102-102 verbatim
end EvmAsm.EL
