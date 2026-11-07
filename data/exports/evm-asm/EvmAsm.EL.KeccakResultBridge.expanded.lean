/-
  EvmAsm.EL.KeccakResultBridge

  Bridge from the zkVM KECCAK256 accelerator output to the EVM stack word
  pushed by the executable spec (GH #111).
-/

module

public import EvmAsm.EL.RLP.Basic
public import EvmAsm.EL.WorldState
public import EvmAsm.Evm64.EvmWord


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace EvmAsm.EL


-- @@ L18-18 verbatim
namespace KeccakResultBridge


-- @@ L20-20 verbatim
abbrev EvmWord := EvmAsm.Evm64.EvmWord


-- @@ L22-23 verbatim
/-- The KECCAK accelerator returns exactly 32 hash bytes. -/
abbrev HashBytes := Fin 32 → Byte


-- @@ L25-27 verbatim
/-- Accelerator output payload for `zkvm_keccak256`. -/
structure AcceleratorOutput where
  hash : HashBytes


-- @@ L29-30 verbatim
def hashBytesList (hash : HashBytes) : List Byte :=
  List.ofFn hash


-- @@ L32-34 verbatim
/-- Big-endian byte conversion matching executable-spec `U256.from_be_bytes`. -/
def wordFromBigEndianBytes (bytes : List Byte) : EvmWord :=
  BitVec.ofNat 256 (EvmAsm.EL.RLP.Nat.fromBytesBE bytes)


-- @@ L36-38 verbatim
/-- Distinctive token: KeccakResultBridge.stackWordFromAcceleratorHash #111. -/
def stackWordFromAcceleratorHash (hash : HashBytes) : EvmWord :=
  wordFromBigEndianBytes (hashBytesList hash)


-- @@ L40-42 verbatim
/-- Stack word pushed by KECCAK256 from the accelerator output buffer. -/
def stackWordFromAcceleratorOutput (output : AcceleratorOutput) : EvmWord :=
  stackWordFromAcceleratorHash output.hash


-- @@ L44-46 verbatim
theorem hashBytesList_length (hash : HashBytes) :
    (hashBytesList hash).length = 32 := by
  simp [hashBytesList]


-- @@ L48-49 verbatim
@[simp] theorem wordFromBigEndianBytes_nil :
    wordFromBigEndianBytes [] = 0 := rfl


-- @@ L51-55 verbatim
theorem wordFromBigEndianBytes_cons (byte : Byte) (tail : List Byte) :
    wordFromBigEndianBytes (byte :: tail) =
      BitVec.ofNat 256
        (byte.toNat * 256 ^ tail.length + EvmAsm.EL.RLP.Nat.fromBytesBE tail) := by
  rfl


-- @@ L57-59 verbatim
theorem stackWordFromAcceleratorHash_eq (hash : HashBytes) :
    stackWordFromAcceleratorHash hash =
      BitVec.ofNat 256 (EvmAsm.EL.RLP.Nat.fromBytesBE (hashBytesList hash)) := rfl


-- @@ L61-63 verbatim
theorem stackWordFromAcceleratorOutput_eq (output : AcceleratorOutput) :
    stackWordFromAcceleratorOutput output =
      stackWordFromAcceleratorHash output.hash := rfl


-- @@ L65-67 verbatim
theorem stackWordFromAcceleratorOutput_hash_length (output : AcceleratorOutput) :
    (hashBytesList output.hash).length = 32 :=
  hashBytesList_length output.hash


-- @@ L69-69 verbatim
end KeccakResultBridge


-- @@ L71-71 verbatim
end EvmAsm.EL
