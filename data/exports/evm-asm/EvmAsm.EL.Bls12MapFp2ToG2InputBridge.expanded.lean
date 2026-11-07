/-
  EvmAsm.EL.Bls12MapFp2ToG2InputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_map_fp2_to_g2` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bls12MapFp2ToG2InputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-23 verbatim
/-- A BLS12-381 quadratic-extension field element as represented by
`zkvm_bls12_381_fp2` (`zkvm_bytes_96`). -/
abbrev Fp2Bytes := Fin 96 → Byte


-- @@ L25-27 verbatim
/-- Input payload passed to `zkvm_bls12_map_fp2_to_g2(fp2, result)`. -/
structure AcceleratorInput where
  fp2 : Fp2Bytes


-- @@ L29-31 verbatim
/-- Read one fixed-width BLS12-381 Fp2 element from executable memory. -/
def fp2FromMemory (memory : MemoryReader) (start : Nat) : Fp2Bytes :=
  fun i => memory (start + i.toNat)


-- @@ L33-38 verbatim
/--
Distinctive token: Bls12MapFp2ToG2InputBridge.bls12MapFp2ToG2InputFromMemory.
-/
def bls12MapFp2ToG2InputFromMemory
    (memory : MemoryReader) (fp2Start : Nat) : AcceleratorInput :=
  { fp2 := fp2FromMemory memory fp2Start }


-- @@ L40-42 verbatim
theorem fp2FromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    fp2FromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L44-47 verbatim
theorem bls12MapFp2ToG2InputFromMemory_fp2
    (memory : MemoryReader) (fp2Start : Nat) :
    (bls12MapFp2ToG2InputFromMemory memory fp2Start).fp2 =
      fp2FromMemory memory fp2Start := rfl


-- @@ L49-49 verbatim
end Bls12MapFp2ToG2InputBridge


-- @@ L51-51 verbatim
end EvmAsm.EL
