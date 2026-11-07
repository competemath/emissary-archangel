/-
  EvmAsm.EL.Bls12MapFp2ToG2ResultBridge

  Bridge from the `zkvm_bls12_map_fp2_to_g2` accelerator output to the
  executable precompile-result surface.
-/

module

public import EvmAsm.Evm64.Accelerators.Status
public import EvmAsm.EL.WorldState


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace EvmAsm.EL


-- @@ L17-17 verbatim
namespace Bls12MapFp2ToG2ResultBridge


-- @@ L19-19 verbatim
abbrev ZkvmStatus := EvmAsm.Accelerators.ZkvmStatus


-- @@ L21-23 verbatim
/-- A BLS12-381 G2 point as represented by `zkvm_bls12_381_g2_point`
(`zkvm_bytes_192`). -/
abbrev G2PointBytes := Fin 192 → Byte


-- @@ L25-27 verbatim
/-- Accelerator output payload for `zkvm_bls12_map_fp2_to_g2`. -/
structure AcceleratorOutput where
  point : G2PointBytes


-- @@ L29-32 verbatim
/-- Full ECALL result: status code plus output buffer contents. -/
structure AcceleratorResult where
  status : ZkvmStatus
  output : AcceleratorOutput


-- @@ L34-35 verbatim
def g2PointBytesList (point : G2PointBytes) : List Byte :=
  List.ofFn point


-- @@ L37-39 verbatim
theorem g2PointBytesList_length (point : G2PointBytes) :
    (g2PointBytesList point).length = 192 := by
  exact List.length_ofFn (f := point)


-- @@ L41-42 verbatim
theorem acceleratorResult_status (result : AcceleratorResult) :
    result.status = result.status := rfl


-- @@ L44-45 verbatim
theorem acceleratorResult_output (result : AcceleratorResult) :
    result.output = result.output := rfl


-- @@ L47-49 verbatim
theorem acceleratorOutput_point_length (output : AcceleratorOutput) :
    (g2PointBytesList output.point).length = 192 :=
  g2PointBytesList_length output.point


-- @@ L51-51 verbatim
end Bls12MapFp2ToG2ResultBridge


-- @@ L53-53 verbatim
end EvmAsm.EL
