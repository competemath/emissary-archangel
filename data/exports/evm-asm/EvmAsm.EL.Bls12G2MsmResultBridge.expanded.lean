/-
  EvmAsm.EL.Bls12G2MsmResultBridge

  Bridge from the `zkvm_bls12_g2_msm` accelerator output to the executable
  precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12G2MsmResultBridge


-- @@ L19-19 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

-- @@ L20-20 verbatim
abbrev G2PointBytes := Fin 192 → Byte


-- @@ L22-24 verbatim
/-- Accelerator output payload for `zkvm_bls12_g2_msm`. -/
structure AcceleratorOutput where
  point : G2PointBytes


-- @@ L26-29 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L31-32 verbatim
def g2PointBytesList (point : G2PointBytes) : List Byte :=
  List.ofFn point


-- @@ L34-37 verbatim
theorem g2PointBytesList_length (point : G2PointBytes) :
    (g2PointBytesList point).length = 192 := by
  unfold g2PointBytesList
  exact List.length_ofFn


-- @@ L39-40 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L42-43 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L45-47 verbatim
theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g2PointBytesList output.point).length = 192 :=
  g2PointBytesList_length output.point


-- @@ L49-49 verbatim
end Bls12G2MsmResultBridge


-- @@ L51-51 verbatim
end EvmAsm.EL
