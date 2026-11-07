/-
  EvmAsm.EL.Bn254G1MulInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bn254_g1_mul` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bn254G1MulInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A BN254 G1 point as represented by `zkvm_bn254_g1_point`. -/
abbrev G1PointBytes := Fin 64 → Byte


-- @@ L24-25 verbatim
/-- A BN254 scalar as represented by `zkvm_bn254_scalar`. -/
abbrev ScalarBytes := Fin 32 → Byte


-- @@ L27-30 verbatim
/-- Input payload passed to `zkvm_bn254_g1_mul(point, scalar, result)`. -/
structure AcceleratorInput where
  point : G1PointBytes
  scalar : ScalarBytes


-- @@ L32-34 verbatim
/-- Read one fixed-width BN254 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L36-38 verbatim
/-- Read one fixed-width BN254 scalar from executable memory. -/
def scalarFromMemory (memory : MemoryReader) (start : Nat) : ScalarBytes :=
  fun i => memory (start + i.toNat)


-- @@ L40-46 verbatim
/--
Distinctive token: Bn254G1MulInputBridge.bn254G1MulInputFromMemory.
-/
def bn254G1MulInputFromMemory
    (memory : MemoryReader) (pointStart scalarStart : Nat) : AcceleratorInput :=
  { point := g1PointFromMemory memory pointStart
    scalar := scalarFromMemory memory scalarStart }


-- @@ L48-50 verbatim
theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L52-54 verbatim
theorem scalarFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    scalarFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L56-59 verbatim
theorem bn254G1MulInputFromMemory_point
    (memory : MemoryReader) (pointStart scalarStart : Nat) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).point =
      g1PointFromMemory memory pointStart := rfl


-- @@ L61-64 verbatim
theorem bn254G1MulInputFromMemory_scalar
    (memory : MemoryReader) (pointStart scalarStart : Nat) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).scalar =
      scalarFromMemory memory scalarStart := rfl


-- @@ L66-69 verbatim
theorem bn254G1MulInputFromMemory_point_apply
    (memory : MemoryReader) (pointStart scalarStart : Nat) (i : Fin 64) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).point i =
      memory (pointStart + i.toNat) := rfl


-- @@ L71-74 verbatim
theorem bn254G1MulInputFromMemory_scalar_apply
    (memory : MemoryReader) (pointStart scalarStart : Nat) (i : Fin 32) :
    (bn254G1MulInputFromMemory memory pointStart scalarStart).scalar i =
      memory (scalarStart + i.toNat) := rfl


-- @@ L76-76 verbatim
end Bn254G1MulInputBridge


-- @@ L78-78 verbatim
end EvmAsm.EL
