/-
  EvmAsm.EL.Bn254PairingInputBridge

  Bridge from executable memory to the input payload consumed by the
  `zkvm_bn254_pairing` accelerator.
-/

module

public import EvmAsm.EL.KeccakInputBridge


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.EL


-- @@ L16-16 verbatim
namespace Bn254PairingInputBridge


-- @@ L18-19 verbatim
/-- A byte-addressed executable memory reader. -/
abbrev MemoryReader := KeccakInputBridge.MemoryReader


-- @@ L21-22 verbatim
/-- A BN254 G1 point as represented by `zkvm_bn254_g1_point`. -/
abbrev G1PointBytes := Fin 64 → Byte


-- @@ L24-25 verbatim
/-- A BN254 G2 point as represented by `zkvm_bn254_g2_point`. -/
abbrev G2PointBytes := Fin 128 → Byte


-- @@ L27-30 verbatim
/-- One `zkvm_bn254_pairing_pair` payload. -/
structure PairingPair where
  g1 : G1PointBytes
  g2 : G2PointBytes


-- @@ L32-35 verbatim
/-- Input payload passed to `zkvm_bn254_pairing(pairs, num_pairs, verified)`. -/
structure AcceleratorInput where
  pairs : List PairingPair
  numPairs : Nat


-- @@ L37-39 verbatim
/-- Read one fixed-width BN254 G1 point from executable memory. -/
def g1PointFromMemory (memory : MemoryReader) (start : Nat) : G1PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L41-43 verbatim
/-- Read one fixed-width BN254 G2 point from executable memory. -/
def g2PointFromMemory (memory : MemoryReader) (start : Nat) : G2PointBytes :=
  fun i => memory (start + i.toNat)


-- @@ L45-48 verbatim
/-- Read one `zkvm_bn254_pairing_pair` from executable memory. -/
def pairingPairFromMemory (memory : MemoryReader) (start : Nat) : PairingPair :=
  { g1 := g1PointFromMemory memory start
    g2 := g2PointFromMemory memory (start + 64) }


-- @@ L50-54 verbatim
/-- Read `numPairs` consecutive 192-byte pairing pairs from executable memory. -/
def pairingPairsFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : List PairingPair :=
  (List.range numPairs).map
    (fun i => pairingPairFromMemory memory (pairsStart + 192 * i))


-- @@ L56-62 verbatim
/--
Distinctive token: Bn254PairingInputBridge.bn254PairingInputFromMemory.
-/
def bn254PairingInputFromMemory
    (memory : MemoryReader) (pairsStart numPairs : Nat) : AcceleratorInput :=
  { pairs := pairingPairsFromMemory memory pairsStart numPairs
    numPairs := numPairs }


-- @@ L64-66 verbatim
theorem g1PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 64) :
    g1PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L68-70 verbatim
theorem g2PointFromMemory_apply
    (memory : MemoryReader) (start : Nat) (i : Fin 128) :
    g2PointFromMemory memory start i = memory (start + i.toNat) := rfl


-- @@ L72-75 verbatim
theorem pairingPairFromMemory_g1
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g1 =
      g1PointFromMemory memory start := rfl


-- @@ L77-80 verbatim
theorem pairingPairFromMemory_g2
    (memory : MemoryReader) (start : Nat) :
    (pairingPairFromMemory memory start).g2 =
      g2PointFromMemory memory (start + 64) := rfl


-- @@ L82-85 verbatim
theorem pairingPairsFromMemory_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (pairingPairsFromMemory memory pairsStart numPairs).length = numPairs := by
  simp [pairingPairsFromMemory]


-- @@ L87-90 verbatim
theorem bn254PairingInputFromMemory_pairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).pairs =
      pairingPairsFromMemory memory pairsStart numPairs := rfl


-- @@ L92-94 verbatim
theorem bn254PairingInputFromMemory_numPairs
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).numPairs = numPairs := rfl


-- @@ L96-99 verbatim
theorem bn254PairingInputFromMemory_pairs_length
    (memory : MemoryReader) (pairsStart numPairs : Nat) :
    (bn254PairingInputFromMemory memory pairsStart numPairs).pairs.length = numPairs := by
  simp [bn254PairingInputFromMemory, pairingPairsFromMemory_length]


-- @@ L101-101 verbatim
end Bn254PairingInputBridge


-- @@ L103-103 verbatim
end EvmAsm.EL
