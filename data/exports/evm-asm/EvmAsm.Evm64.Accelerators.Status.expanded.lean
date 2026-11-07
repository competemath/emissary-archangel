/-
  EvmAsm.Evm64.Accelerators.Status

  Lean bridge for the `zkvm_status` enum from
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.

  The C header (current upstream version) defines exactly two return codes:

      typedef enum {
          ZKVM_EOK   =  0,   /* Success */
          ZKVM_EFAIL = -1    /* Failure */
      } zkvm_status;

  This module mirrors that enum, provides the matching `Int32` numeric encoding,
  and exposes the `a0` return-register `Word` constants used to bridge accelerator
  ECALL postconditions to RISC-V state.

  Refs: parent beads task `evm-asm-nr2sk`, slice `evm-asm-hzmi6`.
-/

module

public import EvmAsm.Rv64.Word


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace EvmAsm

-- @@ L28-28 verbatim
namespace Accelerators


-- @@ L30-36 verbatim
/-- Status codes returned by zkVM accelerator functions, mirroring the
`zkvm_status` C enum. The C enum is signed (`ZKVM_EFAIL = -1`); we model it
as a Lean inductive and provide a 32-bit signed encoding. -/
inductive ZkvmStatus where
  | eok    -- ZKVM_EOK   =  0  (Success)
  | efail  -- ZKVM_EFAIL = -1  (Failure)
  deriving DecidableEq, Repr, Inhabited


-- @@ L38-38 verbatim
namespace ZkvmStatus


-- @@ L40-45 verbatim
/-- 32-bit signed encoding matching the C enum's numeric values exactly.
`ZKVM_EOK` is `0`; `ZKVM_EFAIL` is `-1`, encoded as the all-ones `Int32`
bit-pattern `0xFFFFFFFF`. -/
def toInt32 : ZkvmStatus → Int32
  | .eok   => 0
  | .efail => -1


-- @@ L47-50 verbatim
/-- Predicate identifying the success status. -/
def isOk : ZkvmStatus → Bool
  | .eok   => true
  | .efail => false


-- @@ L52-52 verbatim
@[simp] theorem isOk_eok   : isOk .eok   = true  := rfl

-- @@ L53-53 verbatim
@[simp] theorem isOk_efail : isOk .efail = false := rfl


-- @@ L55-57 verbatim
/-- `isOk` agrees with structural equality against `eok`. -/
theorem isOk_iff_eq_eok (s : ZkvmStatus) : s.isOk = true ↔ s = .eok := by
  cases s <;> simp [isOk]


-- @@ L59-61 verbatim
/-- The two encodings are distinct. -/
theorem toInt32_eok_ne_efail : (ZkvmStatus.eok).toInt32 ≠ (ZkvmStatus.efail).toInt32 := by
  decide


-- @@ L63-67 verbatim
/-- The encoding is injective. -/
theorem toInt32_injective : Function.Injective ZkvmStatus.toInt32 := by
  intro a b h
  cases a <;> cases b <;> simp [toInt32] at h ⊢
  all_goals (first | rfl | exact (h rfl).elim | exact absurd h (by decide))


-- @@ L69-69 verbatim
end ZkvmStatus


-- @@ L71-71 verbatim
end Accelerators

-- @@ L72-72 verbatim
end EvmAsm


-- @@ L74-74 verbatim
namespace EvmAsm

-- @@ L75-75 verbatim
namespace Rv64


-- @@ L77-80 verbatim
/-- RISC-V `a0` return-register `Word` value corresponding to `ZKVM_EOK`.
Accelerator ECALL handlers that succeed leave `0` in `a0`; this constant
names that value for postcondition reasoning. -/
def zkvmStatusEokWord : Word := 0


-- @@ L82-86 verbatim
/-- RISC-V `a0` return-register `Word` value corresponding to `ZKVM_EFAIL`.
The C enum value is `-1` (signed `Int32`). On the RV64 ABI, accelerator
return codes occupy `a0` (a 64-bit register) sign-extended from `Int32`,
so `ZKVM_EFAIL` is the all-ones 64-bit word `0xFFFFFFFFFFFFFFFF`. -/
def zkvmStatusEfailWord : Word := BitVec.allOnes 64


-- @@ L88-91 verbatim
/-- The two status words are distinct. -/
theorem zkvmStatusEokWord_ne_efailWord :
    zkvmStatusEokWord ≠ zkvmStatusEfailWord := by
  decide


-- @@ L93-96 verbatim
/-- RV64 `a0` return-register encoding for a zkVM accelerator status. -/
def zkvmStatusToWord : Accelerators.ZkvmStatus → Word
  | .eok => zkvmStatusEokWord
  | .efail => zkvmStatusEfailWord


-- @@ L98-99 verbatim
@[simp] theorem zkvmStatusToWord_eok :
    zkvmStatusToWord .eok = zkvmStatusEokWord := rfl


-- @@ L101-102 verbatim
@[simp] theorem zkvmStatusToWord_efail :
    zkvmStatusToWord .efail = zkvmStatusEfailWord := rfl


-- @@ L104-110 verbatim
/-- The RV64 return-register encoding is injective over accelerator statuses. -/
theorem zkvmStatusToWord_injective :
    Function.Injective zkvmStatusToWord := by
  intro a b h
  cases a <;> cases b <;> simp [zkvmStatusToWord] at h ⊢
  · exact absurd h zkvmStatusEokWord_ne_efailWord
  · exact absurd h zkvmStatusEokWord_ne_efailWord.symm


-- @@ L112-120 verbatim
/-- Decode an RV64 `a0` return-register word back to a zkVM accelerator status,
when the word is one of the two ABI status encodings. -/
def zkvmStatusFromWord? (word : Word) : Option Accelerators.ZkvmStatus :=
  if word = zkvmStatusEokWord then
    some .eok
  else if word = zkvmStatusEfailWord then
    some .efail
  else
    none


-- @@ L122-124 verbatim
@[simp] theorem zkvmStatusFromWord?_eok :
    zkvmStatusFromWord? zkvmStatusEokWord = some .eok := by
  simp [zkvmStatusFromWord?]


-- @@ L126-128 verbatim
@[simp] theorem zkvmStatusFromWord?_efail :
    zkvmStatusFromWord? zkvmStatusEfailWord = some .efail := by
  simp [zkvmStatusFromWord?, zkvmStatusEokWord_ne_efailWord.symm]


-- @@ L130-132 verbatim
theorem zkvmStatusFromWord?_toWord (status : Accelerators.ZkvmStatus) :
    zkvmStatusFromWord? (zkvmStatusToWord status) = some status := by
  cases status <;> simp [zkvmStatusToWord]


-- @@ L134-149 verbatim
theorem zkvmStatusFromWord?_some_eq_toWord
    {word : Word} {status : Accelerators.ZkvmStatus}
    (h_status : zkvmStatusFromWord? word = some status) :
    word = zkvmStatusToWord status := by
  cases status
  · by_cases h_eok : word = zkvmStatusEokWord
    · simpa [zkvmStatusToWord] using h_eok
    · by_cases h_efail : word = zkvmStatusEfailWord
      · simp [zkvmStatusFromWord?, h_efail] at h_status
        exact False.elim (zkvmStatusEokWord_ne_efailWord h_status.symm)
      · simp [zkvmStatusFromWord?, h_eok, h_efail] at h_status
  · by_cases h_eok : word = zkvmStatusEokWord
    · simp [zkvmStatusFromWord?, h_eok] at h_status
    · by_cases h_efail : word = zkvmStatusEfailWord
      · simpa [zkvmStatusToWord] using h_efail
      · simp [zkvmStatusFromWord?, h_eok, h_efail] at h_status


-- @@ L151-158 verbatim
theorem zkvmStatusFromWord?_eq_none_iff (word : Word) :
    zkvmStatusFromWord? word = none ↔
      word ≠ zkvmStatusEokWord ∧ word ≠ zkvmStatusEfailWord := by
  by_cases h_eok : word = zkvmStatusEokWord
  · simp [zkvmStatusFromWord?, h_eok]
  · by_cases h_efail : word = zkvmStatusEfailWord
    · simp [zkvmStatusFromWord?, h_efail, zkvmStatusEokWord_ne_efailWord.symm]
    · simp [zkvmStatusFromWord?, h_eok, h_efail]


-- @@ L160-165 verbatim
theorem zkvmStatusFromWord?_eq_none_of_ne_status_words
    {word : Word}
    (h_eok : word ≠ zkvmStatusEokWord)
    (h_efail : word ≠ zkvmStatusEfailWord) :
    zkvmStatusFromWord? word = none :=
  (zkvmStatusFromWord?_eq_none_iff word).2 ⟨h_eok, h_efail⟩


-- @@ L167-167 verbatim
end Rv64

-- @@ L168-168 verbatim
end EvmAsm
