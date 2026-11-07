/-
  EvmAsm.EL.Bls12G2MsmInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bls12_g2_msm` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bls12G2MsmInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-23 verbatim
/-- A BLS12-381 G2 point as represented by `zkvm_bls12_381_g2_point`
(`zkvm_bytes_192`). -/
abbrev G2PointBytes := Fin 192 → Byte


-- @@ L25-26 verbatim
/-- A BLS12-381 scalar as represented by `zkvm_bls12_381_scalar`. -/
abbrev ScalarBytes := Fin 32 → Byte


-- @@ L28-31 verbatim
/-- One `zkvm_bls12_381_g2_msm_pair` payload. -/
structure MsmPair where
  point : G2PointBytes
  scalar : ScalarBytes


-- @@ L33-36 verbatim
/-- Input payload passed to `zkvm_bls12_g2_msm(pairs, num_pairs, result)`. -/
structure AcceleratorInput where
  pairs : List MsmPair
  numPairs : Nat


-- @@ L38-40 verbatim
/-- Read one fixed-width BLS12-381 G2 point from executable memory. -/
def g2PointFromMemory (memory : MemoryReader) (start : Nat) : G2PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L42-44 verbatim
/-- Read one fixed-width BLS12-381 scalar from executable memory. -/
def scalarFromMemory (memory : MemoryReader) (start : Nat) : ScalarBytes :=
  fun i => memory (start + i.toNat)


-- @@ L46-51 verbatim
/-- Read one `zkvm_bls12_381_g2_msm_pair` from executable memory.
The pair layout is the 192-byte G2 point followed by the 32-byte scalar
(224 bytes total per pair). -/
def msmPairFromMemory (memory : MemoryReader) (start : Nat) : MsmPair :=
  { point := g2PointFromMemory memory start
    scalar := scalarFromMemory memory (start + 192) }


-- @@ L53-57 verbatim
/-- Read `numPairs` consecutive 224-byte G2 MSM pairs from executable memory. -/
def msmPairsFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List MsmPair :=
  (List.range numPairs).map
    (fun i => msmPairFromMemory memory (pairsStart + 224 * i))


-- @@ L59-65 verbatim
/--
Distinctive token: Bls12G2MsmInputBridge.bls12G2MsmInputFromMemory.
-/
def bls12G2MsmInputFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : AcceleratorInput :=
  { pairs := msmPairsFromMemory memory pairsStart numPairs
    numPairs := numPairs }


-- @@ L67-69 verbatim
theorem g2PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 192) :
    g2PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L71-73 verbatim
theorem scalarFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 32) :
    scalarFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L75-78 verbatim
theorem msmPairFromMemory_point
    (memory : MemoryReader) (start : Nat) :
    (msmPairFromMemory memory start).point =
      g2PointFromMemory memory start := rfl


-- @@ L80-83 verbatim
theorem msmPairFromMemory_scalar
    (memory : MemoryReader) (start : Nat) :
    (msmPairFromMemory memory start).scalar =
      scalarFromMemory memory (start + 192) := rfl


-- @@ L85-88 verbatim
theorem msmPairsFromMemory_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (msmPairsFromMemory memory pairsStart numPairs).length = numPairs := by
  simp [msmPairsFromMemory]


-- @@ L90-93 verbatim
theorem bls12G2MsmInputFromMemory_pairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G2MsmInputFromMemory memory pairsStart numPairs).pairs =
      msmPairsFromMemory memory pairsStart numPairs := rfl


-- @@ L95-97 verbatim
theorem bls12G2MsmInputFromMemory_numPairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G2MsmInputFromMemory memory pairsStart numPairs).numPairs = numPairs := rfl


-- @@ L99-102 verbatim
theorem bls12G2MsmInputFromMemory_pairs_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bls12G2MsmInputFromMemory memory pairsStart numPairs).pairs.length = numPairs := by
  simp [bls12G2MsmInputFromMemory, msmPairsFromMemory_length]


-- @@ L104-104 verbatim
end Bls12G2MsmInputBridge


-- @@ L106-106 verbatim
end EvmAsm.EL
