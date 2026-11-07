/-
  EvmAsm.EL.Bn254G1AddResultBridge

  Bridge from the zkVM `zkvm_bn254_g1_add` accelerator output buffer (a single
  64-byte `zkvm_bn254_g1_point` written through the `result` pointer) to the
  byte-list view consumed by EL precompile return-data assembly. Mirrors the
  SHA256/RIPEMD160 result-bridge skeleton; we do NOT compute a stack word
  here because the BN254 G1 point is 64 bytes (does not fit into one EVM
  stack word) — precompile-output framing is left to a downstream slice.
-/

module

public import EvmAsm.EL.WorldState


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace EvmAsm.EL


-- @@ L20-20 verbatim
namespace Bn254G1AddResultBridge


-- @@ L22-23 verbatim
/-- The 64-byte BN254 G1 point payload (`zkvm_bn254_g1_point`). -/
abbrev PointBytes := Fin 64 → Byte


-- @@ L25-27 verbatim
/-- Accelerator output payload for `zkvm_bn254_g1_add`. -/
structure AcceleratorOutput where
  result : PointBytes


-- @@ L29-31 verbatim
/-- Materialise the output point as a byte list (length 64). -/
def pointBytesList (point : PointBytes) : List Byte :=
  List.ofFn point


-- @@ L33-35 verbatim
/-- Distinctive token: Bn254G1AddResultBridge.outputBytesList. -/
def outputBytesList (output : AcceleratorOutput) : List Byte :=
  pointBytesList output.result


-- @@ L37-39 verbatim
theorem pointBytesList_length (point : PointBytes) :
    (pointBytesList point).length = 64 := by
  simp [pointBytesList]


-- @@ L41-43 verbatim
theorem outputBytesList_length (output : AcceleratorOutput) :
    (outputBytesList output).length = 64 := by
  simp [outputBytesList, pointBytesList_length]


-- @@ L45-46 verbatim
theorem outputBytesList_eq (output : AcceleratorOutput) :
    outputBytesList output = pointBytesList output.result := rfl


-- @@ L48-48 verbatim
end Bn254G1AddResultBridge


-- @@ L50-50 verbatim
end EvmAsm.EL
