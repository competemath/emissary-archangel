/-
  EvmAsm.EL.Bls12MapFpToG1ResultBridge

  Bridge from the `zkvm_bls12_map_fp_to_g1` accelerator output to the executable
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
namespace Bls12MapFpToG1ResultBridge


-- @@ L19-19 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L21-22 verbatim
/-- The result is `zkvm_bls12_381_g1_point` (96 bytes). -/
abbrev G1PointBytes := Fin 96 → Byte


-- @@ L24-26 verbatim
/-- Accelerator output payload for `zkvm_bls12_map_fp_to_g1`. -/
structure AcceleratorOutput where
  point : G1PointBytes


-- @@ L28-31 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L33-34 verbatim
def g1PointBytesList (point : G1PointBytes) : List Byte :=
  List.ofFn point


-- @@ L36-38 verbatim
theorem g1PointBytesList_length (point : G1PointBytes) :
    (g1PointBytesList point).length = 96 := by
  simp [g1PointBytesList]


-- @@ L40-41 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L43-44 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L46-48 verbatim
theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g1PointBytesList output.point).length = 96 :=
  g1PointBytesList_length output.point


-- @@ L50-50 verbatim
end Bls12MapFpToG1ResultBridge


-- @@ L52-52 verbatim
end EvmAsm.EL
