/-
  EvmAsm.EL.KzgPointEvalInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_kzg_point_eval` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace KzgPointEvalInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A KZG commitment/proof as represented by `zkvm_bytes_48`. -/
abbrev Bytes48 := Fin 48 → Byte


-- @@ L24-25 verbatim
/-- A KZG field element as represented by `zkvm_bytes_32`. -/
abbrev Bytes32 := Fin 32 → Byte


-- @@ L27-32 verbatim
/-- Input payload passed to `zkvm_kzg_point_eval(commitment, z, y, proof, verified)`. -/
structure AcceleratorInput where
  commitment : Bytes48
  z : Bytes32
  y : Bytes32
  proof : Bytes48


-- @@ L34-36 verbatim
/-- Read one fixed-width 48-byte KZG payload from executable memory. -/
def bytes48FromMemory (memory : MemoryReader) (start : Nat) : Bytes48 :=
  fun i => memory (start + i.toNat)


-- @@ L38-40 verbatim
/-- Read one fixed-width 32-byte KZG field element from executable memory. -/
def bytes32FromMemory (memory : MemoryReader) (start : Nat) : Bytes32 :=
  fun i => memory (start + i.toNat)


-- @@ L42-51 verbatim
/--
Distinctive token: KzgPointEvalInputBridge.kzgPointEvalInputFromMemory.
-/
def kzgPointEvalInputFromMemory
    (memory : MemoryReader)
    (commitmentStart zStart yStart proofStart : Nat) : AcceleratorInput :=
  { commitment := bytes48FromMemory memory commitmentStart
    z := bytes32FromMemory memory zStart
    y := bytes32FromMemory memory yStart
    proof := bytes48FromMemory memory proofStart }


-- @@ L53-55 verbatim
theorem bytes48FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 48) :
    bytes48FromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L57-59 verbatim
theorem bytes32FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    bytes32FromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L61-64 verbatim
theorem kzgPointEvalInputFromMemory_commitment
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).commitment =
      bytes48FromMemory memory commitmentStart := rfl


-- @@ L66-69 verbatim
theorem kzgPointEvalInputFromMemory_z
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).z =
      bytes32FromMemory memory zStart := rfl


-- @@ L71-74 verbatim
theorem kzgPointEvalInputFromMemory_y
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).y =
      bytes32FromMemory memory yStart := rfl


-- @@ L76-79 verbatim
theorem kzgPointEvalInputFromMemory_proof
    (memory : MemoryReader) (commitmentStart zStart yStart proofStart : Nat) :
    (kzgPointEvalInputFromMemory memory commitmentStart zStart yStart proofStart).proof =
      bytes48FromMemory memory proofStart := rfl


-- @@ L81-81 verbatim
end KzgPointEvalInputBridge


-- @@ L83-83 verbatim
end EvmAsm.EL
