/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedAccumulatorRun

  Small algebraic helpers for composing the pure fixed-loop accumulator run.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-29 verbatim
/-- Split a pure fixed-loop accumulator run into a prefix and suffix. -/
theorem expTwoMulFixedAccumulatorRun_add
    (baseWord exponentWord accWord : EvmWord) (k m n : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k (m + n) =
      expTwoMulFixedAccumulatorRun baseWord exponentWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k m)
        (k + m) n := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorRun]
  | succ n ih =>
      rw [Nat.add_succ, expTwoMulFixedAccumulatorRun_succ,
        expTwoMulFixedAccumulatorRun_succ, ih]
      congr 1
      rw [Nat.add_assoc]


-- @@ L31-43 verbatim
/-- Running the remaining fixed-loop suffix from a semantically correct prefix
    reaches the full EXP result. -/
theorem expTwoMulFixedAccumulatorRun_suffix_eq_exp_of_start
    {baseWord exponentWord accWord : EvmWord} {k : Nat}
    (hk : k ≤ 256)
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord k) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k (256 - k) =
      EvmWord.exp baseWord exponentWord := by
  have hBound : k + (256 - k) ≤ 256 := by omega
  rw [expTwoMulFixedAccumulatorRun_eq_target_add hBound hStart]
  have hAdd : k + (256 - k) = 256 := by omega
  rw [hAdd, expTwoMulFixedAccumulatorTarget_full]


-- @@ L45-57 verbatim
/-- Direct suffix form from the four-limb accumulator invariant. -/
theorem expTwoMulFixedAccumulatorRun_suffix_eq_exp_of_invariant
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word}
    (hk : k ≤ 256)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord
        (expResultWord r0 r1 r2 r3) k (256 - k) =
      EvmWord.exp baseWord exponentWord := by
  unfold expTwoMulFixedAccumulatorInvariant at hInv
  exact expTwoMulFixedAccumulatorRun_suffix_eq_exp_of_start hk hInv


-- @@ L59-75 verbatim
/-- The remaining fixed-loop suffix preserves the full semantic invariant. -/
theorem expTwoMulFixedAccumulatorInvariant_full_of_suffix_run
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hk : k ≤ 256)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorRun baseWord exponentWord
          (expResultWord r0 r1 r2 r3) k (256 - k)) :
    expResultWord r0' r1' r2' r3' =
      EvmWord.exp baseWord exponentWord := by
  unfold expTwoMulFixedAccumulatorInvariant at hInv
  rw [hRun]
  exact expTwoMulFixedAccumulatorRun_suffix_eq_exp_of_start hk hInv


-- @@ L77-77 verbatim
end EvmAsm.Evm64.Exp.Compose
