/-
  EvmAsm.EL.Bls12MapFpToG1InputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_map_fp_to_g1` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bls12MapFpToG1InputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A BLS12-381 base-field element as represented by `zkvm_bls12_381_fp` (48 bytes). -/
abbrev FpBytes := Fin 48 → Byte


-- @@ L24-26 verbatim
/-- Input payload passed to `zkvm_bls12_map_fp_to_g1(field_element, result)`. -/
structure AcceleratorInput where
  fieldElement : FpBytes


-- @@ L28-30 verbatim
/-- Read one fixed-width BLS12-381 base-field element from executable memory. -/
def fpFromMemory (memory : MemoryReader) (start : Nat) : FpBytes :=
  fun i => memory (start + i.toNat)


-- @@ L32-37 verbatim
/--
Distinctive token: Bls12MapFpToG1InputBridge.bls12MapFpToG1InputFromMemory.
-/
def bls12MapFpToG1InputFromMemory
    (memory : MemoryReader) (fpStart : Nat) : AcceleratorInput :=
  { fieldElement := fpFromMemory memory fpStart }


-- @@ L39-41 verbatim
theorem fpFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 48) :
    fpFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L43-46 verbatim
theorem bls12MapFpToG1InputFromMemory_fieldElement
    (memory : MemoryReader) (fpStart : Nat) :
    (bls12MapFpToG1InputFromMemory memory fpStart).fieldElement =
      fpFromMemory memory fpStart := rfl


-- @@ L48-51 verbatim
theorem bls12MapFpToG1InputFromMemory_fieldElement_apply
    (memory : MemoryReader) (fpStart : Nat) (i : Fin 48) :
    (bls12MapFpToG1InputFromMemory memory fpStart).fieldElement i =
      memory (fpStart + i.toNat) := rfl


-- @@ L53-53 verbatim
end Bls12MapFpToG1InputBridge


-- @@ L55-55 verbatim
end EvmAsm.EL
