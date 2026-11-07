/-
  EvmAsm.EL.Bn254G1MulResultBridge

  Bridge from the `zkvm_bn254_g1_mul` accelerator output to the executable
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
namespace Bn254G1MulResultBridge


-- @@ L19-19 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus

-- @@ L20-20 verbatim
abbrev G1PointBytes := Fin 64 → Byte


-- @@ L22-24 verbatim
/-- Accelerator output payload for `zkvm_bn254_g1_mul`. -/
structure AcceleratorOutput where
  point : G1PointBytes


-- @@ L26-29 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L31-32 verbatim
def g1PointBytesList (point : G1PointBytes) : List Byte :=
  List.ofFn point


-- @@ L34-36 verbatim
theorem g1PointBytesList_length (point : G1PointBytes) :
    (g1PointBytesList point).length = 64 := by
  simp [g1PointBytesList]


-- @@ L38-39 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L41-42 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L44-46 verbatim
theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g1PointBytesList output.point).length = 64 :=
  g1PointBytesList_length output.point


-- @@ L48-48 verbatim
end Bn254G1MulResultBridge


-- @@ L50-50 verbatim
end EvmAsm.EL
