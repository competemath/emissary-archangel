/-
  EvmAsm.Evm64.EvmWordArith.IsZero

  ISZERO correctness: OR-reduction of limbs detects zero.
-/

module

public import EvmAsm.Evm64.EvmWordArith.Common


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-21 verbatim
namespace EvmWord

-- ============================================================================
-- ISZERO correctness
-- ============================================================================


-- @@ L23-37 verbatim
theorem iszero_or_reduce_correct {a : EvmWord} :
    (if BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1
     then (1 : Word) else 0) =
    (if a = 0 then (1 : Word) else 0) := by
  suffices h : BitVec.ult (a.getLimb 0 ||| a.getLimb 1 ||| a.getLimb 2 ||| a.getLimb 3) 1 ↔ a = 0 by
    by_cases ha : a = 0 <;> simp_all
  constructor
  · intro h
    have hor := ult_one_eq_zero.mp h
    have h12 := bv_or_eq_zero (show (a.getLimb 0 ||| a.getLimb 1) ||| (a.getLimb 2 ||| a.getLimb 3) = 0 by
      rw [BitVec.or_assoc] at hor; exact hor)
    exact eq_zero_iff_limbs.mpr
      ⟨(bv_or_eq_zero h12.1).1, (bv_or_eq_zero h12.1).2,
       (bv_or_eq_zero h12.2).1, (bv_or_eq_zero h12.2).2⟩
  · intro h; subst h; exact ult_one_eq_zero.mpr rfl


-- @@ L39-39 verbatim
end EvmWord


-- @@ L41-41 verbatim
end EvmAsm.Evm64
