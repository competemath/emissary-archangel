/-
  EvmAsm.EL.Bn254G1AddInputBridge

  Bridge from BN254 G1-addition precompile call data to the byte-buffer input
  consumed by the zkVM `zkvm_bn254_g1_add` accelerator. The accelerator C
  signature is

      zkvm_status zkvm_bn254_g1_add(const zkvm_bn254_g1_point* p1,
                                    const zkvm_bn254_g1_point* p2,
                                    zkvm_bn254_g1_point* result);

  where `zkvm_bn254_g1_point` is `zkvm_bytes_64`. This module fixes the input
  payload shape (two 64-byte points read from memory) and provides the
  per-field memory-read decompositions; the result-buffer shape and pure
  execution boundary live in the sibling `Result`/`Ecall` bridges.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace EvmAsm.EL


-- @@ L26-26 verbatim
namespace Bn254G1AddInputBridge


-- @@ L28-29 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L31-32 verbatim
/-- The 64-byte BN254 G1 point payload (`zkvm_bn254_g1_point`). -/
abbrev PointBytes := Fin 64 → Byte


-- @@ L34-42 verbatim
/--
Input payload passed to the
`zkvm_bn254_g1_add(p1, p2, result)` accelerator.

Distinctive token: Bn254G1AddInputBridge.AcceleratorInput zkvm_bn254_g1_add.
-/
structure AcceleratorInput where
  p1 : PointBytes
  p2 : PointBytes


-- @@ L44-46 verbatim
/-- Read a fixed `n`-byte block starting at `start` from a `MemoryReader`. -/
def readFixed (n : Nat) (memory : MemoryReader) (start : Nat) : Fin n → Byte :=
  fun i => memory (start + i.val)


-- @@ L48-50 verbatim
/-- Build the `p1` G1-point payload by reading 64 bytes from memory. -/
def p1BytesFromMemory (memory : MemoryReader) (start : Nat) : PointBytes :=
  readFixed 64 memory start


-- @@ L52-54 verbatim
/-- Build the `p2` G1-point payload by reading 64 bytes from memory. -/
def p2BytesFromMemory (memory : MemoryReader) (start : Nat) : PointBytes :=
  readFixed 64 memory start


-- @@ L56-65 verbatim
/--
Accelerator-call input assembled from two byte-addressed memory slices, one
per G1 point.

Distinctive token: Bn254G1AddInputBridge.bn254G1AddInputFromMemory.
-/
def bn254G1AddInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  { p1 := p1BytesFromMemory memory p1Start
    p2 := p2BytesFromMemory memory p2Start }


-- @@ L67-70 verbatim
/-- Compatibility alias matching the SHA256/Secp256k1 bridge naming. -/
def acceleratorInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  bn254G1AddInputFromMemory memory p1Start p2Start


-- @@ L72-73 verbatim
theorem readFixed_apply (n : Nat) (memory : MemoryReader) (start : Nat) (i : Fin n) :
    readFixed n memory start i = memory (start + i.val) := rfl


-- @@ L75-76 verbatim
theorem p1BytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    p1BytesFromMemory memory start i = memory (start + i.val) := rfl


-- @@ L78-79 verbatim
theorem p2BytesFromMemory_apply (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    p2BytesFromMemory memory start i = memory (start + i.val) := rfl


-- @@ L81-84 verbatim
theorem bn254G1AddInputFromMemory_p1
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bn254G1AddInputFromMemory memory p1Start p2Start).p1 =
      p1BytesFromMemory memory p1Start := rfl


-- @@ L86-89 verbatim
theorem bn254G1AddInputFromMemory_p2
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bn254G1AddInputFromMemory memory p1Start p2Start).p2 =
      p2BytesFromMemory memory p2Start := rfl


-- @@ L91-94 verbatim
theorem acceleratorInputFromMemory_eq
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    acceleratorInputFromMemory memory p1Start p2Start =
      bn254G1AddInputFromMemory memory p1Start p2Start := rfl


-- @@ L96-96 verbatim
end Bn254G1AddInputBridge


-- @@ L98-98 verbatim
end EvmAsm.EL
