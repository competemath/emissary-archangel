/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptySpec

  Whole-program caller contract for `accountIsEip161Empty_prog` (K137,
  `AccountFields.lean`, 108 instructions, entry
  `GuestAddrs.account_is_eip161_empty`).

  The routine decodes an Ethereum account RLP
  `[nonce, balance, storage_root, code_hash]` via three calls to
  `rlp_list_nth_item` (K20, fields 0/1/3) and writes to a u64 output cell
  whether the account is EIP-161 empty:

      is_empty  ⟺  nonce == 0  ∧  balance == 0  ∧  code_hash == EMPTY_CODE_HASH

  Each field is inspected with a byte-wise LBU loop (the #10340 byte-safe
  code-hash compare, replacing the earlier misaligned 32-byte dword LDs):
    * nonce   (field 0): length ≤ 8, big-endian accumulate + test == 0;
    * balance (field 1): length ≤ 32, all content bytes == 0;
    * code_hash (field 3): length == 32, bytes == EMPTY_CODE_HASH.

  This module consumes the shared semantic model (`beAccum`,
  `aieEmptyCodeHashBytes`, `accountEip161Empty`), the byte-scan bridge
  lemmas, and the code-layout infrastructure.  Composition of the whole
  108-instruction triple (`account_is_eip161_empty_spec_within`) builds on
  the three byte-scan loop lemmas here.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountFields
import EvmAsm.Codegen.Programs.RlpListNthItemSAsmBase
import EvmAsm.Codegen.Programs.AccountDecodeSpec


-- @@ L34-34 verbatim
namespace EvmAsm.Codegen.AccountIsEip161EmptySpec


-- @@ L36-36 verbatim
open EvmAsm.Rv64

-- @@ L37-37 verbatim
open EvmAsm.Rv64.SAsm

-- @@ L38-38 verbatim
open EvmAsm.EL.RLP

-- @@ L39-39 verbatim
open EvmAsm.Codegen.RlpListNthItemSAsm

-- @@ L40-42 verbatim
open EvmAsm.Codegen.AccountDecodeSpec (beAccum beAccum_zero beAccum_succ
  beAccum_eq_zero_of_allZero beAccum_toNat_lt beAccum_allZero_of_eq_zero
  beAccum_eq_zero_iff)


-- @@ L44-44 verbatim
/-! ## Code layout -/


-- @@ L46-47 verbatim
/-- The accessor body's fixed guest base address. -/
abbrev AB : Word := (GuestAddrs.account_is_eip161_empty : Word)


-- @@ L49-50 verbatim
/-- Code requirement for the 108-instruction accessor body. -/
def aieCode : CodeReq := CodeReq.ofProg AB accountIsEip161Empty_prog


-- @@ L52-54 verbatim
/-- The full code region: the accessor body ∪ the `rlp_list_nth_item`
    subroutine it calls three times. -/
def fullCode : CodeReq := aieCode.union RlpListNthItemSAsm.code


-- @@ L56-56 verbatim
theorem aie_prog_length : accountIsEip161Empty_prog.length = 108 := by decide


-- @@ L58-58 verbatim
/-! ## The empty-code-hash constant (`aie_empty_code_hash` `.data` bytes) -/


-- @@ L60-66 verbatim
/-- The 32 bytes of `EMPTY_CODE_HASH = keccak256(b'')`, exactly as baked
    into the `aie_empty_code_hash` `.data` constant. -/
def aieEmptyCodeHashBytes : List (BitVec 8) :=
  [ 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
    0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
    0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
    0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70 ]


-- @@ L68-68 verbatim
theorem aieEmptyCodeHashBytes_length : aieEmptyCodeHashBytes.length = 32 := by decide


-- @@ L70-74 verbatim
/-! ## The genuine EIP-161-empty verdict

    Tied to the three `rlp_list_nth_item` successes and the actual content
    bytes: the nonce decodes big-endian to `0`, every balance content byte
    is `0`, and the code-hash content equals `EMPTY_CODE_HASH`. -/


-- @@ L76-86 verbatim
def accountEip161Empty (bytes : List (BitVec 8)) (base : Word) (listLen : Nat) : Prop :=
  ∃ o0 l0 o1 l1 o3 l3 : Word,
    -- field 0 (nonce): lenient — every content byte is zero
    Success bytes base listLen 0 o0 l0 ∧ l0.toNat ≤ 8 ∧
      (∀ k, k < l0.toNat → bytes.getD (o0.toNat + k) 0 = 0) ∧
    -- field 1 (balance): lenient — every content byte is zero
    Success bytes base listLen 1 o1 l1 ∧ l1.toNat ≤ 32 ∧
      (∀ k, k < l1.toNat → bytes.getD (o1.toNat + k) 0 = 0) ∧
    -- field 3 (code_hash): exact — content equals EMPTY_CODE_HASH
    Success bytes base listLen 3 o3 l3 ∧ l3.toNat = 32 ∧
      (∀ k, k < 32 → bytes.getD (o3.toNat + k) 0 = aieEmptyCodeHashBytes.getD k 0)


-- @@ L88-88 verbatim
end EvmAsm.Codegen.AccountIsEip161EmptySpec
