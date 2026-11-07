/-
  EvmAsm.EL.Bls12G1AddInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_g1_add` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bls12G1AddInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A BLS12-381 G1 point as represented by `zkvm_bls12_381_g1_point`. -/
abbrev G1PointBytes := Fin 96 → Byte


-- @@ L24-27 verbatim
/-- Input payload passed to `zkvm_bls12_g1_add(p1, p2, result)`. -/
structure AcceleratorInput where
  p1 : G1PointBytes
  p2 : G1PointBytes


-- @@ L29-31 verbatim
/-- Read one fixed-width BLS12-381 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L33-39 verbatim
/--
Distinctive token: Bls12G1AddInputBridge.bls12G1AddInputFromMemory.
-/
def bls12G1AddInputFromMemory
    (memory : MemoryReader) (p1Start p2Start : Nat) : AcceleratorInput :=
  { p1 := g1PointFromMemory memory p1Start
    p2 := g1PointFromMemory memory p2Start }


-- @@ L41-43 verbatim
theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L45-48 verbatim
theorem bls12G1AddInputFromMemory_p1
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p1 =
      g1PointFromMemory memory p1Start := rfl


-- @@ L50-53 verbatim
theorem bls12G1AddInputFromMemory_p2
    (memory : MemoryReader) (p1Start p2Start : Nat) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p2 =
      g1PointFromMemory memory p2Start := rfl


-- @@ L55-58 verbatim
theorem bls12G1AddInputFromMemory_p1_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 96) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p1 i =
      memory (p1Start + i.toNat) := rfl


-- @@ L60-63 verbatim
theorem bls12G1AddInputFromMemory_p2_apply
    (memory : MemoryReader) (p1Start p2Start : Nat) (i : Fin 96) :
    (bls12G1AddInputFromMemory memory p1Start p2Start).p2 i =
      memory (p2Start + i.toNat) := rfl


-- @@ L65-65 verbatim
end Bls12G1AddInputBridge


-- @@ L67-67 verbatim
end EvmAsm.EL
