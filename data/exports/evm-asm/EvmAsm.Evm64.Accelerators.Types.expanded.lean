/-
  EvmAsm.Evm64.Accelerators.Types

  Lean-side payload type aliases for the fixed-size byte structs declared in
  `zkvm_accelerators.h`.
-/

module


-- @@ L10-10 verbatim
public section

-- @@ L11-11 verbatim
namespace EvmAsm

-- @@ L12-12 verbatim
namespace Accelerators


-- @@ L14-15 verbatim
/-- C `uint8_t`, used by the accelerator ABI payload structs. -/
abbrev Byte := BitVec 8


-- @@ L17-19 verbatim
/-- Fixed-size C byte array payload, matching `struct { uint8_t data[n]; }`. -/
structure ByteArray (n : Nat) where
  data : Fin n → Byte


-- @@ L21-21 verbatim
namespace ByteArray


-- @@ L23-25 verbatim
/-- Convert a fixed-size byte payload to a Lean list in index order. -/
def toList {n : Nat} (bytes : ByteArray n) : List Byte :=
  List.ofFn bytes.data


-- @@ L27-29 verbatim
theorem toList_length {n : Nat} (bytes : ByteArray n) :
    bytes.toList.length = n := by
  simp [toList]


-- @@ L31-33 verbatim
theorem toList_get? {n : Nat} (bytes : ByteArray n) (i : Nat) (h_i : i < n) :
    bytes.toList[i]? = some (bytes.data ⟨i, h_i⟩) := by
  simp [toList, h_i]


-- @@ L35-37 verbatim
@[simp] theorem toList_zero (bytes : ByteArray 0) :
    bytes.toList = [] := by
  simp [toList]


-- @@ L39-50 verbatim
theorem toList_injective {n : Nat} :
    Function.Injective (@toList n) := by
  intro a b h_list
  cases a with
  | mk aData =>
    cases b with
    | mk bData =>
      congr
      funext i
      have h_get := congrArg (fun xs : List Byte => xs[i.val]?) h_list
      simpa [toList_get? { data := aData } i.val i.isLt,
        toList_get? { data := bData } i.val i.isLt] using h_get


-- @@ L52-54 verbatim
theorem toList_eq_iff {n : Nat} (a b : ByteArray n) :
    a.toList = b.toList ↔ a = b :=
  ⟨fun h_list => toList_injective h_list, fun h_eq => by rw [h_eq]⟩


-- @@ L56-56 verbatim
end ByteArray


-- @@ L58-58 verbatim
/-! ## Common byte array structs -/


-- @@ L60-61 verbatim
/-- C `zkvm_bytes_16`. -/
abbrev ZkvmBytes16 := ByteArray 16


-- @@ L63-64 verbatim
/-- C `zkvm_bytes_32`. -/
abbrev ZkvmBytes32 := ByteArray 32


-- @@ L66-67 verbatim
/-- C `zkvm_bytes_48`. -/
abbrev ZkvmBytes48 := ByteArray 48


-- @@ L69-70 verbatim
/-- C `zkvm_bytes_64`. -/
abbrev ZkvmBytes64 := ByteArray 64


-- @@ L72-73 verbatim
/-- C `zkvm_bytes_96`. -/
abbrev ZkvmBytes96 := ByteArray 96


-- @@ L75-76 verbatim
/-- C `zkvm_bytes_128`. -/
abbrev ZkvmBytes128 := ByteArray 128


-- @@ L78-79 verbatim
/-- C `zkvm_bytes_192`. -/
abbrev ZkvmBytes192 := ByteArray 192


-- @@ L81-81 verbatim
/-! ## Hash and signature aliases -/


-- @@ L83-84 verbatim
/-- C `zkvm_keccak256_hash`. -/
abbrev ZkvmKeccak256Hash := ZkvmBytes32


-- @@ L86-87 verbatim
/-- C `zkvm_sha256_hash`. -/
abbrev ZkvmSha256Hash := ZkvmBytes32


-- @@ L89-90 verbatim
/-- C `zkvm_ripemd160_hash`: 20-byte hash padded to 32 bytes. -/
abbrev ZkvmRipemd160Hash := ZkvmBytes32


-- @@ L92-93 verbatim
/-- C `zkvm_secp256k1_hash`. -/
abbrev ZkvmSecp256k1Hash := ZkvmBytes32


-- @@ L95-96 verbatim
/-- C `zkvm_secp256k1_signature`. -/
abbrev ZkvmSecp256k1Signature := ZkvmBytes64


-- @@ L98-99 verbatim
/-- C `zkvm_secp256k1_pubkey`. -/
abbrev ZkvmSecp256k1Pubkey := ZkvmBytes64


-- @@ L101-102 verbatim
/-- C `zkvm_secp256r1_hash`. -/
abbrev ZkvmSecp256r1Hash := ZkvmBytes32


-- @@ L104-105 verbatim
/-- C `zkvm_secp256r1_signature`. -/
abbrev ZkvmSecp256r1Signature := ZkvmBytes64


-- @@ L107-108 verbatim
/-- C `zkvm_secp256r1_pubkey`. -/
abbrev ZkvmSecp256r1Pubkey := ZkvmBytes64


-- @@ L110-110 verbatim
/-! ## BN254 aliases -/


-- @@ L112-113 verbatim
/-- C `zkvm_bn254_g1_point`. -/
abbrev ZkvmBn254G1Point := ZkvmBytes64


-- @@ L115-116 verbatim
/-- C `zkvm_bn254_g2_point`. -/
abbrev ZkvmBn254G2Point := ZkvmBytes128


-- @@ L118-119 verbatim
/-- C `zkvm_bn254_scalar`. -/
abbrev ZkvmBn254Scalar := ZkvmBytes32


-- @@ L121-124 verbatim
/-- C `zkvm_bn254_pairing_pair`. -/
structure ZkvmBn254PairingPair where
  g1 : ZkvmBn254G1Point
  g2 : ZkvmBn254G2Point


-- @@ L126-126 verbatim
/-! ## BLS12-381 aliases -/


-- @@ L128-129 verbatim
/-- C `zkvm_bls12_381_g1_point`. -/
abbrev ZkvmBls12_381G1Point := ZkvmBytes96


-- @@ L131-132 verbatim
/-- C `zkvm_bls12_381_g2_point`. -/
abbrev ZkvmBls12_381G2Point := ZkvmBytes192


-- @@ L134-135 verbatim
/-- C `zkvm_bls12_381_scalar`. -/
abbrev ZkvmBls12_381Scalar := ZkvmBytes32


-- @@ L137-138 verbatim
/-- C `zkvm_bls12_381_fp`. -/
abbrev ZkvmBls12_381Fp := ZkvmBytes48


-- @@ L140-141 verbatim
/-- C `zkvm_bls12_381_fp2`. -/
abbrev ZkvmBls12_381Fp2 := ZkvmBytes96


-- @@ L143-146 verbatim
/-- C `zkvm_bls12_381_g1_msm_pair`. -/
structure ZkvmBls12_381G1MsmPair where
  point : ZkvmBls12_381G1Point
  scalar : ZkvmBls12_381Scalar


-- @@ L148-151 verbatim
/-- C `zkvm_bls12_381_g2_msm_pair`. -/
structure ZkvmBls12_381G2MsmPair where
  point : ZkvmBls12_381G2Point
  scalar : ZkvmBls12_381Scalar


-- @@ L153-156 verbatim
/-- C `zkvm_bls12_381_pairing_pair`. -/
structure ZkvmBls12_381PairingPair where
  g1 : ZkvmBls12_381G1Point
  g2 : ZkvmBls12_381G2Point


-- @@ L158-158 verbatim
/-! ## BLAKE2F and KZG aliases -/


-- @@ L160-161 verbatim
/-- C `zkvm_blake2f_state`. -/
abbrev ZkvmBlake2fState := ZkvmBytes64


-- @@ L163-164 verbatim
/-- C `zkvm_blake2f_message`. -/
abbrev ZkvmBlake2fMessage := ZkvmBytes128


-- @@ L166-167 verbatim
/-- C `zkvm_blake2f_offset`. -/
abbrev ZkvmBlake2fOffset := ZkvmBytes16


-- @@ L169-170 verbatim
/-- C `zkvm_kzg_commitment`. -/
abbrev ZkvmKzgCommitment := ZkvmBytes48


-- @@ L172-173 verbatim
/-- C `zkvm_kzg_proof`. -/
abbrev ZkvmKzgProof := ZkvmBytes48


-- @@ L175-176 verbatim
/-- C `zkvm_kzg_field_element`. -/
abbrev ZkvmKzgFieldElement := ZkvmBytes32


-- @@ L178-178 verbatim
/-! ## Length sanity checks for common output payloads -/


-- @@ L180-182 verbatim
theorem zkvmSha256Hash_length (hash : ZkvmSha256Hash) :
    hash.toList.length = 32 :=
  ByteArray.toList_length hash


-- @@ L184-186 verbatim
theorem zkvmRipemd160Hash_length (hash : ZkvmRipemd160Hash) :
    hash.toList.length = 32 :=
  ByteArray.toList_length hash


-- @@ L188-190 verbatim
theorem zkvmBlake2fState_length (state : ZkvmBlake2fState) :
    state.toList.length = 64 :=
  ByteArray.toList_length state


-- @@ L192-192 verbatim
end Accelerators

-- @@ L193-193 verbatim
end EvmAsm
