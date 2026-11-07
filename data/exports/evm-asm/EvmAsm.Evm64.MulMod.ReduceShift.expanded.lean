/-
  EvmAsm.Evm64.MulMod.ReduceShift

  Pure limb bridges for the shift-and-insert half of the bit-serial MULMOD
  reducer inner step.
-/

module

public import EvmAsm.Evm64.MulMod.ReduceSemantics


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64


-- @@ L16-16 verbatim
open EvmAsm.Rv64


-- @@ L18-33 verbatim
/-- The consumed high bit of `x17` as the one-bit word produced by `SRLI x17, 63`. -/
theorem mulModReduceInputBit_word (x17 : Word) :
    (if mulModReduceInputBit x17 then (1 : Word) else 0) = (x17 >>> 63) := by
  unfold mulModReduceInputBit
  apply BitVec.eq_of_getElem_eq
  intro j _hj
  by_cases hj : (j : Nat) = 0
  · subst hj
    by_cases hbit : x17.toNat.testBit 63 = true <;>
      simp [BitVec.getElem_ushiftRight, BitVec.getLsbD, hbit]
  · have htest : x17.toNat.testBit (63 + j) = false := by
      apply Nat.testBit_lt_two_pow
      calc x17.toNat < 2 ^ 64 := x17.isLt
        _ ≤ 2 ^ (63 + j) := Nat.pow_le_pow_right (by omega) (by omega)
    by_cases hbit : x17.toNat.testBit 63 = true <;>
      simp [BitVec.getElem_ushiftRight, BitVec.getLsbD, hbit, hj, htest]


-- @@ L35-42 verbatim
theorem mulModReduceRemWord_shiftLeft_one_getLimbN_zero (r0 r1 r2 r3 : Word) :
    EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 0 = r0 <<< 1 := by
  rw [show EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 0 =
      EvmWord.getLimb (mulModReduceRemWord r0 r1 r2 r3 <<< 1) ⟨0, by decide⟩ by
    simp [EvmWord.getLimbN]]
  rw [EvmWord.getLimb_shiftLeft_eq_div
    (v := mulModReduceRemWord r0 r1 r2 r3) (n := 1) (i := ⟨0, by decide⟩) (by decide)]
  simp


-- @@ L44-54 verbatim
theorem mulModReduceRemWord_shiftLeft_one_getLimbN_one (r0 r1 r2 r3 : Word) :
    EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 1 =
      (r1 <<< 1) ||| (r0 >>> 63) := by
  rw [show EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 1 =
      EvmWord.getLimb (mulModReduceRemWord r0 r1 r2 r3 <<< 1) ⟨1, by decide⟩ by
    simp [EvmWord.getLimbN]]
  rw [EvmWord.getLimb_shiftLeft
    (v := mulModReduceRemWord r0 r1 r2 r3) (n := 1) (i := ⟨1, by decide⟩) (by decide)]
  simp
  rw [show 18446744073709551615#64 = BitVec.allOnes 64 by decide]
  rw [BitVec.and_allOnes]


-- @@ L56-66 verbatim
theorem mulModReduceRemWord_shiftLeft_one_getLimbN_two (r0 r1 r2 r3 : Word) :
    EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 2 =
      (r2 <<< 1) ||| (r1 >>> 63) := by
  rw [show EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 2 =
      EvmWord.getLimb (mulModReduceRemWord r0 r1 r2 r3 <<< 1) ⟨2, by decide⟩ by
    simp [EvmWord.getLimbN]]
  rw [EvmWord.getLimb_shiftLeft
    (v := mulModReduceRemWord r0 r1 r2 r3) (n := 1) (i := ⟨2, by decide⟩) (by decide)]
  simp
  rw [show 18446744073709551615#64 = BitVec.allOnes 64 by decide]
  rw [BitVec.and_allOnes]


-- @@ L68-78 verbatim
theorem mulModReduceRemWord_shiftLeft_one_getLimbN_three (r0 r1 r2 r3 : Word) :
    EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 3 =
      (r3 <<< 1) ||| (r2 >>> 63) := by
  rw [show EvmWord.getLimbN (mulModReduceRemWord r0 r1 r2 r3 <<< 1) 3 =
      EvmWord.getLimb (mulModReduceRemWord r0 r1 r2 r3 <<< 1) ⟨3, by decide⟩ by
    simp [EvmWord.getLimbN]]
  rw [EvmWord.getLimb_shiftLeft
    (v := mulModReduceRemWord r0 r1 r2 r3) (n := 1) (i := ⟨3, by decide⟩) (by decide)]
  simp
  rw [show 18446744073709551615#64 = BitVec.allOnes 64 by decide]
  rw [BitVec.and_allOnes]


-- @@ L80-89 verbatim
theorem mulModReduceShiftInBit_getLimbN_zero (r0 r1 r2 r3 : Word) (bit : Bool) :
    EvmWord.getLimbN (mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) bit) 0 =
      (r0 <<< 1) ||| (if bit then 1 else 0) := by
  unfold mulModReduceShiftInBit
  rw [EvmWord.getLimbN_or, mulModReduceRemWord_shiftLeft_one_getLimbN_zero]
  cases bit
  · rw [mulModReduceBitWord_false, EvmWord.getLimbN_zero]
    simp
  · rw [mulModReduceBitWord_true, EvmWord.getLimbN_one_zero]
    simp


-- @@ L91-96 verbatim
theorem mulModReduceShiftInBit_getLimbN_zero_input (r0 r1 r2 r3 x17 : Word) :
    EvmWord.getLimbN
        (mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) (mulModReduceInputBit x17)) 0 =
      (r0 <<< 1) ||| (x17 >>> 63) := by
  rw [mulModReduceShiftInBit_getLimbN_zero]
  rw [← mulModReduceInputBit_word x17]


-- @@ L98-107 verbatim
theorem mulModReduceShiftInBit_getLimbN_one (r0 r1 r2 r3 : Word) (bit : Bool) :
    EvmWord.getLimbN (mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) bit) 1 =
      (r1 <<< 1) ||| (r0 >>> 63) := by
  unfold mulModReduceShiftInBit
  rw [EvmWord.getLimbN_or, mulModReduceRemWord_shiftLeft_one_getLimbN_one]
  cases bit
  · rw [mulModReduceBitWord_false, EvmWord.getLimbN_zero]
    simp
  · rw [mulModReduceBitWord_true, EvmWord.getLimbN_one_one]
    simp


-- @@ L109-118 verbatim
theorem mulModReduceShiftInBit_getLimbN_two (r0 r1 r2 r3 : Word) (bit : Bool) :
    EvmWord.getLimbN (mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) bit) 2 =
      (r2 <<< 1) ||| (r1 >>> 63) := by
  unfold mulModReduceShiftInBit
  rw [EvmWord.getLimbN_or, mulModReduceRemWord_shiftLeft_one_getLimbN_two]
  cases bit
  · rw [mulModReduceBitWord_false, EvmWord.getLimbN_zero]
    simp
  · rw [mulModReduceBitWord_true, EvmWord.getLimbN_one_two]
    simp


-- @@ L120-129 verbatim
theorem mulModReduceShiftInBit_getLimbN_three (r0 r1 r2 r3 : Word) (bit : Bool) :
    EvmWord.getLimbN (mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) bit) 3 =
      (r3 <<< 1) ||| (r2 >>> 63) := by
  unfold mulModReduceShiftInBit
  rw [EvmWord.getLimbN_or, mulModReduceRemWord_shiftLeft_one_getLimbN_three]
  cases bit
  · rw [mulModReduceBitWord_false, EvmWord.getLimbN_zero]
    simp
  · rw [mulModReduceBitWord_true, EvmWord.getLimbN_one_three]
    simp


-- @@ L131-131 verbatim
end EvmAsm.Evm64
