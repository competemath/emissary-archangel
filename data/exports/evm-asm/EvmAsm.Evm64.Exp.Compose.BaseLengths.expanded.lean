/-
  EvmAsm.Evm64.Exp.Compose.BaseLengths

  Shared EXP composition length and byte-offset lemmas.
-/

module

public import EvmAsm.Evm64.Exp.CondMulCall


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-18 verbatim
abbrev expIterCountNew (iterCount : Word) : Word :=
  iterCount + signExtend12 ((-1 : BitVec 12))


-- @@ L20-23 verbatim
/-- Length of the EXP prologue block, restated in the composition namespace so
    future `skipBlock`-style subsumption proofs can use a compact simp set. -/
theorem exp_prologue_len : (EvmAsm.Evm64.exp_prologue).length = 6 := by
  exact EvmAsm.Evm64.exp_prologue_length


-- @@ L25-27 verbatim
/-- Length of the EXP epilogue block, restated in the composition namespace. -/
theorem exp_epilogue_len : (EvmAsm.Evm64.exp_epilogue).length = 9 := by
  exact EvmAsm.Evm64.exp_epilogue_length


-- @@ L29-30 verbatim
theorem exp_bit_test_block_len : (EvmAsm.Evm64.exp_bit_test_block).length = 3 := by
  exact EvmAsm.Evm64.exp_bit_test_block_length


-- @@ L32-34 verbatim
theorem exp_square_block_len (mulOff : BitVec 21) :
    (EvmAsm.Evm64.exp_square_block mulOff).length = 1 := by
  exact EvmAsm.Evm64.exp_square_block_length mulOff


-- @@ L36-38 verbatim
theorem exp_cond_mul_block_len (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_block mulOff skipOff).length = 2 := by
  exact EvmAsm.Evm64.exp_cond_mul_block_length mulOff skipOff


-- @@ L40-42 verbatim
theorem exp_loop_back_len (backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_loop_back backOff).length = 2 := by
  exact EvmAsm.Evm64.exp_loop_back_length backOff


-- @@ L44-46 verbatim
theorem exp_loop_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 8 := by
  exact EvmAsm.Evm64.exp_loop_length mulOff skipOff backOff


-- @@ L48-50 verbatim
theorem exp_iter_body_byte_len (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 := by
  exact EvmAsm.Evm64.exp_iter_body_byte_length mulOff skipOff


-- @@ L52-54 verbatim
theorem exp_loop_back_byte_len (backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop_back backOff).length = 8 := by
  exact EvmAsm.Evm64.exp_loop_back_byte_length backOff


-- @@ L56-58 verbatim
theorem exp_loop_byte_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact EvmAsm.Evm64.exp_loop_byte_length mulOff skipOff backOff


-- @@ L60-63 verbatim
/-- Byte offset of the square-call block within one EXP loop iteration. -/
theorem exp_loop_square_byte_off :
    4 * (EvmAsm.Evm64.exp_bit_test_block).length = 12 := by
  rw [exp_bit_test_block_len]


-- @@ L65-69 verbatim
/-- Byte offset of the conditional multiply block within one EXP loop iteration. -/
theorem exp_loop_cond_mul_byte_off (mulOff : BitVec 21) :
    4 * ((EvmAsm.Evm64.exp_bit_test_block).length +
      (EvmAsm.Evm64.exp_square_block mulOff).length) = 16 := by
  simp only [exp_bit_test_block_len, exp_square_block_len]


-- @@ L71-74 verbatim
/-- Byte offset of the loop-back block within one EXP loop iteration. -/
theorem exp_loop_back_byte_off (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 := by
  exact exp_iter_body_byte_len mulOff skipOff


-- @@ L76-79 verbatim
/-- Byte offset of the next EXP loop iteration. -/
theorem exp_loop_next_iter_byte_off (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact exp_loop_byte_len mulOff skipOff backOff


-- @@ L81-83 verbatim
theorem exp_squaring_call_block_len (mulOff : BitVec 21) :
    (EvmAsm.Evm64.exp_squaring_call_block mulOff).length = 26 := by
  exact EvmAsm.Evm64.exp_squaring_call_block_length mulOff


-- @@ L85-87 verbatim
theorem exp_squaring_call_block_byte_len (mulOff : BitVec 21) :
    4 * (EvmAsm.Evm64.exp_squaring_call_block mulOff).length = 104 := by
  exact EvmAsm.Evm64.exp_squaring_call_block_byte_length mulOff


-- @@ L89-92 verbatim
theorem exp_cond_mul_call_with_skip_block_len
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block mulOff skipOff).length = 27 := by
  exact EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_length mulOff skipOff


-- @@ L94-97 verbatim
theorem exp_iter_body_full_len
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.exp_iter_body_full mulOff skipOff backOff).length = 58 := by
  exact EvmAsm.Evm64.exp_iter_body_full_length mulOff skipOff backOff


-- @@ L99-101 verbatim
theorem exp_loop_pointer_advance_len :
    (EvmAsm.Evm64.exp_loop_pointer_advance).length = 1 := by
  exact EvmAsm.Evm64.exp_loop_pointer_advance_length


-- @@ L103-105 verbatim
theorem exp_loop_pointer_restore_len :
    (EvmAsm.Evm64.exp_loop_pointer_restore).length = 1 := by
  exact EvmAsm.Evm64.exp_loop_pointer_restore_length


-- @@ L107-109 verbatim
theorem evm_exp_len (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (EvmAsm.Evm64.evm_exp mulOff skipOff backOff).length = 75 := by
  exact EvmAsm.Evm64.evm_exp_length mulOff skipOff backOff


-- @@ L111-121 verbatim
/-- Bundled byte offsets for the blocks within one EXP loop iteration. -/
theorem exp_loop_block_byte_offsets (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (EvmAsm.Evm64.exp_bit_test_block).length = 12 ∧
    4 * ((EvmAsm.Evm64.exp_bit_test_block).length +
      (EvmAsm.Evm64.exp_square_block mulOff).length) = 16 ∧
    4 * (EvmAsm.Evm64.exp_iter_body mulOff skipOff).length = 24 ∧
    4 * (EvmAsm.Evm64.exp_loop mulOff skipOff backOff).length = 32 := by
  exact ⟨exp_loop_square_byte_off,
    exp_loop_cond_mul_byte_off mulOff,
    exp_loop_back_byte_off mulOff skipOff,
    exp_loop_next_iter_byte_off mulOff skipOff backOff⟩


-- @@ L123-125 verbatim
theorem exp_prologue_byte_len :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 := by
  exact EvmAsm.Evm64.exp_prologue_byte_length


-- @@ L127-129 verbatim
theorem exp_epilogue_byte_len :
    4 * (EvmAsm.Evm64.exp_epilogue).length = 36 := by
  exact EvmAsm.Evm64.exp_epilogue_byte_length


-- @@ L131-134 verbatim
/-- Byte offset of the EXP epilogue within the boundary-code layout. -/
theorem exp_boundary_epilogue_byte_off :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 := by
  exact exp_prologue_byte_len


-- @@ L136-140 verbatim
/-- Byte offset immediately after the EXP prologue/epilogue boundary blocks. -/
theorem exp_boundary_end_byte_off :
    4 * ((EvmAsm.Evm64.exp_prologue).length +
      (EvmAsm.Evm64.exp_epilogue).length) = 60 := by
  simp only [exp_prologue_len, exp_epilogue_len]


-- @@ L142-147 verbatim
/-- Bundled byte offsets for the EXP boundary-code layout. -/
theorem exp_boundary_block_byte_offsets :
    4 * (EvmAsm.Evm64.exp_prologue).length = 24 ∧
    4 * ((EvmAsm.Evm64.exp_prologue).length +
      (EvmAsm.Evm64.exp_epilogue).length) = 60 := by
  exact ⟨exp_boundary_epilogue_byte_off, exp_boundary_end_byte_off⟩


-- @@ L149-149 verbatim
end EvmAsm.Evm64.Exp.Compose
