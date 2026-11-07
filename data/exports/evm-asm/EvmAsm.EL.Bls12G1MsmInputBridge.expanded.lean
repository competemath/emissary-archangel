/-
  EvmAsm.EL.Bls12G1MsmInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_g1_msm` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bls12G1MsmInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A BLS12-381 G1 point as represented by `zkvm_bls12_381_g1_point`. -/
abbrev G1PointBytes := Fin 96 → Byte


-- @@ L24-25 verbatim
/-- A BLS12-381 scalar as represented by `zkvm_bls12_381_scalar`. -/
abbrev ScalarBytes := Fin 32 → Byte


-- @@ L27-30 verbatim
/-- One `zkvm_bls12_381_g1_msm_pair` payload. -/
structure MsmPair where
  point : G1PointBytes
  scalar : ScalarBytes


-- @@ L32-35 verbatim
/-- Input payload passed to `zkvm_bls12_g1_msm(pairs, num_pairs, result)`. -/
structure AcceleratorInput where
  pairs : List MsmPair
  numPairs : Nat


-- @@ L37-39 verbatim
/-- Read one fixed-width BLS12-381 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L41-43 verbatim
/-- Read one fixed-width BLS12-381 scalar from executable memory. -/
def scalarFromMemory (memory : MemoryReader) (start : Nat) : ScalarBytes :=
  fun i => memory (start + i.toNat)


-- @@ L45-48 verbatim
/-- Read one `zkvm_bls12_381_g1_msm_pair` from executable memory. -/
def msmPairFromMemory (memory : MemoryReader) (start : Nat) : MsmPair :=
  { point := g1PointFromMemory memory start
    scalar := scalarFromMemory memory (start + 96) }


-- @@ L50-54 verbatim
/-- Read `numPairs` consecutive 128-byte G1 MSM pairs from executable memory. -/
def msmPairsFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List MsmPair :=
  (List.range numPairs).map
    (fun i => msmPairFromMemory memory (pairsStart + 128 * i))


-- @@ L56-62 verbatim
/--
Distinctive token: Bls12G1MsmInputBridge.bls12G1MsmInputFromMemory.
-/
def bls12G1MsmInputFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : AcceleratorInput :=
  { pairs := msmPairsFromMemory memory pairsStart numPairs
    numPairs := numPairs }


-- @@ L64-66 verbatim
theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 96) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L68-70 verbatim
theorem scalarFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    scalarFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L72-75 verbatim
theorem msmPairFromMemory_point
    (memory : MemoryReader) (start : Nat) :
    (msmPairFromMemory memory start).point =
      g1PointFromMemory memory start := rfl


-- @@ L77-80 verbatim
theorem msmPairFromMemory_scalar
    (memory : MemoryReader) (start : Nat) :
    (msmPairFromMemory memory start).scalar =
      scalarFromMemory memory (start + 96) := rfl


-- @@ L82-85 verbatim
theorem msmPairsFromMemory_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (msmPairsFromMemory memory pairsStart numPairs).length = numPairs := by
  simp [msmPairsFromMemory]


-- @@ L87-90 verbatim
theorem bls12G1MsmInputFromMemory_pairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G1MsmInputFromMemory memory pairsStart numPairs).pairs =
      msmPairsFromMemory memory pairsStart numPairs := rfl


-- @@ L92-94 verbatim
theorem bls12G1MsmInputFromMemory_numPairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G1MsmInputFromMemory memory pairsStart numPairs).numPairs = numPairs := rfl


-- @@ L96-99 verbatim
theorem bls12G1MsmInputFromMemory_pairs_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G1MsmInputFromMemory memory pairsStart numPairs).pairs.length = numPairs := by
  simp [bls12G1MsmInputFromMemory, msmPairsFromMemory_length]


-- @@ L101-101 verbatim
end Bls12G1MsmInputBridge


-- @@ L103-103 verbatim
end EvmAsm.EL
