/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

  Symbolic loop invariant anchor for the fixed x19 two-MUL saved-bit EXP loop.
-/

module

public import EvmAsm.Evm64.EvmWordArith.Exp
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L16-16 verbatim
open EvmAsm.Rv64


-- @@ L18-23 verbatim
/-- The exponent prefix that has been consumed after `k` fixed-loop iterations.
    The fixed loop scans most-significant bit first, so this is the high prefix
    shifted down into the low end of the EVM word. -/
def expTwoMulFixedProcessedExponent (exponentWord : EvmWord) (k : Nat) :
    EvmWord :=
  exponentWord >>> (256 - k)


-- @@ L25-28 verbatim
/-- Semantic accumulator target after `k` fixed-loop iterations. -/
def expTwoMulFixedAccumulatorTarget
    (baseWord exponentWord : EvmWord) (k : Nat) : EvmWord :=
  EvmWord.exp baseWord (expTwoMulFixedProcessedExponent exponentWord k)


-- @@ L30-32 verbatim
theorem expTwoMulFixedProcessedExponent_full (exponentWord : EvmWord) :
    expTwoMulFixedProcessedExponent exponentWord 256 = exponentWord := by
  simp [expTwoMulFixedProcessedExponent]


-- @@ L34-38 verbatim
theorem expTwoMulFixedAccumulatorTarget_full
    (baseWord exponentWord : EvmWord) :
    expTwoMulFixedAccumulatorTarget baseWord exponentWord 256 =
      EvmWord.exp baseWord exponentWord := by
  simp [expTwoMulFixedAccumulatorTarget, expTwoMulFixedProcessedExponent_full]


-- @@ L40-45 verbatim
theorem expTwoMulFixedProcessedExponent_zero (exponentWord : EvmWord) :
    expTwoMulFixedProcessedExponent exponentWord 0 = 0 := by
  unfold expTwoMulFixedProcessedExponent
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt exponentWord.isLt


-- @@ L47-51 verbatim
theorem expTwoMulFixedAccumulatorTarget_zero
    (baseWord exponentWord : EvmWord) :
    expTwoMulFixedAccumulatorTarget baseWord exponentWord 0 = 1 := by
  rw [expTwoMulFixedAccumulatorTarget, expTwoMulFixedProcessedExponent_zero]
  exact EvmWord.exp_zero_right baseWord


-- @@ L53-56 verbatim
theorem expResultWord_one_zero_zero_zero :
    expResultWord 1 0 0 0 = (1 : EvmWord) := by
  apply BitVec.eq_of_toNat_eq
  decide


-- @@ L58-63 verbatim
/-- The next exponent bit consumed by iteration `k`, as a Bool.

    The fixed loop scans most-significant bit first, so iteration `k` consumes
    source bit `255 - k`. -/
def expTwoMulFixedProcessedBit (exponentWord : EvmWord) (k : Nat) : Bool :=
  decide (((exponentWord >>> (255 - k)).toNat % 2) = 1)


-- @@ L65-66 verbatim
def expTwoMulFixedProcessedBitWord (exponentWord : EvmWord) (k : Nat) : Word :=
  if expTwoMulFixedProcessedBit exponentWord k then 1 else 0


-- @@ L68-73 verbatim
theorem expTwoMulFixedProcessedBitWord_eq_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k = 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = false := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide


-- @@ L75-80 verbatim
theorem expTwoMulFixedProcessedBitWord_ne_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k ≠ 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = true := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide


-- @@ L82-88 verbatim
theorem expTwoMulFixedProcessedBitWord_add_zero_eq_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k +
        signExtend12 (0 : BitVec 12) = 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = false := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide


-- @@ L90-96 verbatim
theorem expTwoMulFixedProcessedBitWord_add_zero_ne_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k +
        signExtend12 (0 : BitVec 12) ≠ 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = true := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide


-- @@ L98-117 verbatim
theorem expTwoMulFixedProcessedExponent_succ_toNat
    (exponentWord : EvmWord) {k : Nat} (hk : k < 256) :
    (expTwoMulFixedProcessedExponent exponentWord (k + 1)).toNat =
      2 * (expTwoMulFixedProcessedExponent exponentWord k).toNat +
        if expTwoMulFixedProcessedBit exponentWord k then 1 else 0 := by
  unfold expTwoMulFixedProcessedExponent expTwoMulFixedProcessedBit
  simp [Nat.shiftRight_eq_div_pow]
  set shift := 255 - k
  have hShift : 256 - k = shift + 1 := by omega
  rw [hShift]
  rw [show 2 ^ (shift + 1) = 2 ^ shift * 2 by rw [Nat.pow_succ]]
  rw [← Nat.div_div_eq_div_mul]
  let shifted := exponentWord.toNat / 2 ^ shift
  have hmod : shifted % 2 < 2 := Nat.mod_lt shifted (by decide)
  have hmod_cases : shifted % 2 = 0 ∨ shifted % 2 = 1 := by omega
  rcases hmod_cases with h_zero | h_one
  · simp [shifted, h_zero]
    omega
  · simp [shifted, h_one]
    omega


-- @@ L119-127 verbatim
/-- One Bool-unified semantic accumulator update for the fixed loop.

    Every iteration squares the current accumulator. The conditional multiply
    path additionally multiplies by the original base when the consumed bit is
    one. -/
def expTwoMulFixedAccumulatorStep
    (baseWord accWord : EvmWord) (bit : Bool) : EvmWord :=
  let squared := accWord * accWord
  if bit then baseWord * squared else squared


-- @@ L129-134 verbatim
/-- Pure semantic invariant carried by the fixed-loop induction path. -/
def expTwoMulFixedAccumulatorInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) : Prop :=
  expResultWord r0 r1 r2 r3 =
    expTwoMulFixedAccumulatorTarget baseWord exponentWord k


-- @@ L136-141 verbatim
theorem expTwoMulFixedAccumulatorInvariant_zero_one
    (baseWord exponentWord : EvmWord) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord 0 1 0 0 0 := by
  unfold expTwoMulFixedAccumulatorInvariant
  rw [expResultWord_one_zero_zero_zero,
    expTwoMulFixedAccumulatorTarget_zero]


-- @@ L143-150 verbatim
theorem expTwoMulFixedAccumulatorInvariant_full
    {baseWord exponentWord : EvmWord} {r0 r1 r2 r3 : Word}
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord 256
        r0 r1 r2 r3) :
    expResultWord r0 r1 r2 r3 = EvmWord.exp baseWord exponentWord := by
  unfold expTwoMulFixedAccumulatorInvariant at hInv
  rw [hInv, expTwoMulFixedAccumulatorTarget_full]


-- @@ L152-156 verbatim
@[irreducible]
def expTwoMulFixedSemanticInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) : Assertion :=
  ⌜expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3⌝


-- @@ L158-164 verbatim
theorem expTwoMulFixedSemanticInvariant_unfold
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word} :
    expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3 =
      ⌜expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3⌝ := by
  delta expTwoMulFixedSemanticInvariant
  rfl


-- @@ L166-171 verbatim
theorem expTwoMulFixedSemanticInvariant_pcFree
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word} :
    (expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3).pcFree := by
  rw [expTwoMulFixedSemanticInvariant_unfold]
  pcFree


-- @@ L173-178 verbatim
instance pcFreeInst_expTwoMulFixedSemanticInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) :
    Assertion.PCFree
      (expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3) :=
  ⟨expTwoMulFixedSemanticInvariant_pcFree⟩


-- @@ L180-202 verbatim
/-- Generic Bool-unified successor rule for the semantic accumulator invariant.

    The CPS one-step proof should discharge `hStep` from the concrete
    squaring/conditional-multiply case and `hSemanticStep` from the exponent
    bit algebra, then use this lemma for both branch outcomes. -/
theorem expTwoMulFixedAccumulatorInvariant_succ_of_step
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hStep :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorStep baseWord
          (expResultWord r0 r1 r2 r3) bit)
    (hSemanticStep :
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) bit =
          expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1)) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hStep, hInv, hSemanticStep]


-- @@ L204-226 verbatim
theorem expTwoMulFixedAccumulatorStep_eq_target_of_processedExponent_succ
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    (hNext :
      (expTwoMulFixedProcessedExponent exponentWord (k + 1)).toNat =
        2 * (expTwoMulFixedProcessedExponent exponentWord k).toNat +
          if bit then 1 else 0) :
    expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) bit =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1) := by
  unfold expTwoMulFixedAccumulatorStep expTwoMulFixedAccumulatorTarget
  by_cases hbit : bit
  · simp [hbit] at hNext ⊢
    exact (EvmWord.exp_double_add_one_right_of_toNat_eq
      baseWord
      (expTwoMulFixedProcessedExponent exponentWord k)
      (expTwoMulFixedProcessedExponent exponentWord (k + 1))
      hNext).symm
  · simp [hbit] at hNext ⊢
    exact (EvmWord.exp_double_right_of_toNat_eq
      baseWord
      (expTwoMulFixedProcessedExponent exponentWord k)
      (expTwoMulFixedProcessedExponent exponentWord (k + 1))
      hNext).symm


-- @@ L228-235 verbatim
theorem expTwoMulFixedAccumulatorStep_eq_target_succ
    (baseWord exponentWord : EvmWord) {k : Nat} (hk : k < 256) :
    expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k)
        (expTwoMulFixedProcessedBit exponentWord k) =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1) :=
  expTwoMulFixedAccumulatorStep_eq_target_of_processedExponent_succ
    (expTwoMulFixedProcessedExponent_succ_toNat exponentWord hk)


-- @@ L237-242 verbatim
theorem expTwoMulFixedAccumulatorStep_false_eq_squareW
    (baseWord : EvmWord) (r0 r1 r2 r3 : Word) :
    expTwoMulFixedAccumulatorStep baseWord
        (expResultWord r0 r1 r2 r3) false =
      expSquaringCallSquareW r0 r1 r2 r3 := by
  rfl


-- @@ L244-253 verbatim
theorem expTwoMulFixedAccumulatorStep_true_eq_condRw
    {baseWord : EvmWord} {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBase : baseWord = expResultWord a0 a1 a2 a3) :
    expTwoMulFixedAccumulatorStep baseWord
        (expResultWord r0 r1 r2 r3) true =
      expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3 := by
  subst hBase
  simp [expTwoMulFixedAccumulatorStep, expTwoMulCondRw,
    expSquaringCallSquareW, expTwoMulIterAw]
  ac_rfl


-- @@ L255-276 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_squareW_false
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word}
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hSemanticStep :
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) false =
        expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1)) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
  exact
    expTwoMulFixedAccumulatorInvariant_succ_of_step
      hInv
      (by
        rw [expResultWord_getLimbN_self,
          expTwoMulFixedAccumulatorStep_false_eq_squareW])
      hSemanticStep


-- @@ L278-304 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_condRw_true
    {baseWord exponentWord : EvmWord} {k : Nat}
    {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hSemanticStep :
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) true =
        expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1)) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) := by
  exact
    expTwoMulFixedAccumulatorInvariant_succ_of_step
      hInv
      (by
        rw [expResultWord_getLimbN_self,
          expTwoMulFixedAccumulatorStep_true_eq_condRw hBase])
      hSemanticStep


-- @@ L306-333 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_squareW_branch
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBitWord :
      e >>> (63 : BitVec 6).toNat =
        expTwoMulFixedProcessedBitWord exponentWord k)
    (hBitZero : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) = 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
  have hProcessedFalse :
      expTwoMulFixedProcessedBit exponentWord k = false := by
    rw [hBitWord] at hBitZero
    exact
      (expTwoMulFixedProcessedBitWord_add_zero_eq_zero_iff
        exponentWord k).1 hBitZero
  refine
    expTwoMulFixedAccumulatorInvariant_succ_of_squareW_false
      hInv ?_
  rw [← hProcessedFalse]
  exact expTwoMulFixedAccumulatorStep_eq_target_succ baseWord exponentWord hk


-- @@ L335-367 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_condRw_branch
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBitWord :
      e >>> (63 : BitVec 6).toNat =
        expTwoMulFixedProcessedBitWord exponentWord k)
    (hBitNe : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) := by
  have hProcessedTrue :
      expTwoMulFixedProcessedBit exponentWord k = true := by
    rw [hBitWord] at hBitNe
    exact
      (expTwoMulFixedProcessedBitWord_add_zero_ne_zero_iff
        exponentWord k).1 hBitNe
  refine
    expTwoMulFixedAccumulatorInvariant_succ_of_condRw_true
      hBase hInv ?_
  rw [← hProcessedTrue]
  exact expTwoMulFixedAccumulatorStep_eq_target_succ baseWord exponentWord hk


-- @@ L369-381 verbatim
/-- Semantic accumulator obtained by running `n` generic fixed-loop updates
    starting from the target at iteration `k`.

    This is intentionally indexed by `n`, not by concrete iteration names, so
    the loop proof can recurse over this family instead of peeling 256 named
    pre/post pairs. -/
def expTwoMulFixedAccumulatorAfter
    (baseWord exponentWord : EvmWord) (k : Nat) : Nat → EvmWord
  | 0 => expTwoMulFixedAccumulatorTarget baseWord exponentWord k
  | n + 1 =>
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorAfter baseWord exponentWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n))


-- @@ L383-387 verbatim
theorem expTwoMulFixedAccumulatorAfter_zero
    (baseWord exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k 0 =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord k := by
  rfl


-- @@ L389-395 verbatim
theorem expTwoMulFixedAccumulatorAfter_succ
    (baseWord exponentWord : EvmWord) (k n : Nat) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k (n + 1) =
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorAfter baseWord exponentWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n)) := by
  rfl


-- @@ L397-411 verbatim
theorem expTwoMulFixedAccumulatorAfter_eq_target_add
    (baseWord exponentWord : EvmWord) (k n : Nat) (hBound : k + n ≤ 256) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k n =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + n) := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorAfter]
  | succ n ih =>
      rw [expTwoMulFixedAccumulatorAfter_succ]
      have hPrev : k + n ≤ 256 := by omega
      have hStep : k + n < 256 := by omega
      rw [ih hPrev]
      simpa [Nat.add_assoc] using
        expTwoMulFixedAccumulatorStep_eq_target_succ
          baseWord exponentWord (k := k + n) hStep


-- @@ L413-424 verbatim
theorem expTwoMulFixedAccumulatorInvariant_of_after
    {baseWord exponentWord : EvmWord} {k n : Nat}
    {r0' r1' r2' r3' : Word}
    (hBound : k + n ≤ 256)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorAfter baseWord exponentWord k n) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + n)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hRun, expTwoMulFixedAccumulatorAfter_eq_target_add
    baseWord exponentWord k n hBound]


-- @@ L426-438 verbatim
/-- Semantic accumulator obtained by running `n` generic fixed-loop updates
    from an arbitrary current accumulator word.

    This is the form the CPS loop composition should expose: the machine proof
    establishes the concrete post-iteration result is this run, while the
    invariant theorem below connects that run back to the mathematical target. -/
def expTwoMulFixedAccumulatorRun
    (baseWord exponentWord accWord : EvmWord) (k : Nat) : Nat → EvmWord
  | 0 => accWord
  | n + 1 =>
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n))


-- @@ L440-444 verbatim
theorem expTwoMulFixedAccumulatorRun_zero
    (baseWord exponentWord accWord : EvmWord) (k : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k 0 =
      accWord := by
  rfl


-- @@ L446-452 verbatim
theorem expTwoMulFixedAccumulatorRun_succ
    (baseWord exponentWord accWord : EvmWord) (k n : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k (n + 1) =
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n)) := by
  rfl


-- @@ L454-466 verbatim
theorem expTwoMulFixedAccumulatorRun_eq_after_of_start
    {baseWord exponentWord accWord : EvmWord} {k n : Nat}
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord k) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n =
      expTwoMulFixedAccumulatorAfter baseWord exponentWord k n := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorRun, expTwoMulFixedAccumulatorAfter,
        hStart]
  | succ n ih =>
      rw [expTwoMulFixedAccumulatorRun_succ,
        expTwoMulFixedAccumulatorAfter_succ, ih]


-- @@ L468-477 verbatim
theorem expTwoMulFixedAccumulatorRun_eq_target_add
    {baseWord exponentWord accWord : EvmWord} {k n : Nat}
    (hBound : k + n ≤ 256)
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord k) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + n) := by
  rw [expTwoMulFixedAccumulatorRun_eq_after_of_start hStart]
  exact expTwoMulFixedAccumulatorAfter_eq_target_add
    baseWord exponentWord k n hBound


-- @@ L479-494 verbatim
theorem expTwoMulFixedAccumulatorInvariant_of_run
    {baseWord exponentWord : EvmWord} {k n : Nat}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hBound : k + n ≤ 256)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorRun baseWord exponentWord
          (expResultWord r0 r1 r2 r3) k n) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + n)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hRun, expTwoMulFixedAccumulatorRun_eq_target_add
    hBound hInv]


-- @@ L496-503 verbatim
theorem expTwoMulFixedAccumulatorRun_eq_exp_of_start_zero
    {baseWord exponentWord accWord : EvmWord}
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord 0) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord 0 256 =
      EvmWord.exp baseWord exponentWord := by
  rw [expTwoMulFixedAccumulatorRun_eq_target_add (hBound := by decide) hStart]
  exact expTwoMulFixedAccumulatorTarget_full baseWord exponentWord


-- @@ L505-518 verbatim
theorem expTwoMulFixedAccumulatorInvariant_full_of_run
    {baseWord exponentWord : EvmWord}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord 0
        r0 r1 r2 r3)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorRun baseWord exponentWord
          (expResultWord r0 r1 r2 r3) 0 256) :
    expResultWord r0' r1' r2' r3' =
      EvmWord.exp baseWord exponentWord := by
  unfold expTwoMulFixedAccumulatorInvariant at hInv
  rw [hRun, expTwoMulFixedAccumulatorRun_eq_exp_of_start_zero hInv]


-- @@ L520-530 verbatim
theorem expTwoMulFixedAccumulatorRun_full_of_initial_one
    {baseWord exponentWord : EvmWord}
    {r0' r1' r2' r3' : Word}
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorRun baseWord exponentWord
          (expResultWord 1 0 0 0) 0 256) :
    expResultWord r0' r1' r2' r3' =
      EvmWord.exp baseWord exponentWord :=
  expTwoMulFixedAccumulatorInvariant_full_of_run
    (expTwoMulFixedAccumulatorInvariant_zero_one baseWord exponentWord) hRun


-- @@ L532-537 verbatim
/-- Expected fixed-loop `x19` exponent cursor at the start of iteration `k`.

    The loop starts from limb 3, shifts the current limb left once per bit, and
    reloads the next lower limb every 64 iterations. -/
def expTwoMulFixedCursorWord (exponentWord : EvmWord) (k : Nat) : Word :=
  exponentWord.getLimbN (3 - k / 64) <<< (k % 64)


-- @@ L539-541 verbatim
def expTwoMulFixedCursorInvariant
    (exponentWord : EvmWord) (k : Nat) (e : Word) : Prop :=
  e = expTwoMulFixedCursorWord exponentWord k


-- @@ L543-547 verbatim
theorem expTwoMulFixedCursorInvariant_zero (exponentWord : EvmWord) :
    expTwoMulFixedCursorInvariant exponentWord 0
      (exponentWord.getLimbN 3) := by
  unfold expTwoMulFixedCursorInvariant expTwoMulFixedCursorWord
  simp


-- @@ L549-553 verbatim
def expTwoMulFixedControlInvariant
    (exponentWord : EvmWord) (k : Nat)
    (c6 _ptr nextLimb _evmSp : Word) : Prop :=
  c6.toNat = 64 - k % 64 ∧
  nextLimb = exponentWord.getLimbN (2 - k / 64)


-- @@ L555-560 verbatim
theorem expTwoMulFixedControlInvariant_zero
    (exponentWord : EvmWord) (ptr evmSp : Word) :
    expTwoMulFixedControlInvariant exponentWord 0
      64 ptr (exponentWord.getLimbN 2) evmSp := by
  unfold expTwoMulFixedControlInvariant
  simp


-- @@ L562-571 verbatim
theorem expTwoMulFixedInitialInvariants
    (baseWord exponentWord : EvmWord) (ptr evmSp : Word) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord 0 1 0 0 0 ∧
    expTwoMulFixedCursorInvariant exponentWord 0
      (exponentWord.getLimbN 3) ∧
    expTwoMulFixedControlInvariant exponentWord 0
      64 ptr (exponentWord.getLimbN 2) evmSp :=
  ⟨expTwoMulFixedAccumulatorInvariant_zero_one baseWord exponentWord,
    expTwoMulFixedCursorInvariant_zero exponentWord,
    expTwoMulFixedControlInvariant_zero exponentWord ptr evmSp⟩


-- @@ L573-575 verbatim
private theorem signExtend12_neg1_toNat :
    (signExtend12 (-1 : BitVec 12)).toNat = 2^64 - 1 := by
  decide


-- @@ L577-584 verbatim
private theorem word_add_neg1_toNat {w : Word} (hPos : 1 ≤ w.toNat) :
    (w + signExtend12 (-1 : BitVec 12)).toNat = w.toNat - 1 := by
  rw [BitVec.toNat_add, signExtend12_neg1_toNat]
  rw [show w.toNat + (2^64 - 1) = (w.toNat - 1) + 2^64 from by
    have := w.isLt
    omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by have := w.isLt; omega)


-- @@ L586-604 verbatim
theorem expTwoMulFixedControlInvariant_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    k % 64 = 63 := by
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
    omega
  have hDec := word_add_neg1_toNat (w := c6) hPos
  have hZero : (c6 + signExtend12 (-1 : BitVec 12)).toNat = 0 := by
    rw [hC6]
    rfl
  rw [hDec, hNat] at hZero
  have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
  omega


-- @@ L606-626 verbatim
theorem expTwoMulFixedControlInvariant_no_reload_mod
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    k % 64 < 63 := by
  by_contra hNot
  have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
  have hMod : k % 64 = 63 := by omega
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨hNat, _⟩
  have hPos : 1 ≤ c6.toNat := by
    rw [hNat]
    omega
  have hDec := word_add_neg1_toNat (w := c6) hPos
  have hZero : c6 + signExtend12 (-1 : BitVec 12) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hDec, hNat, hMod]
    rfl
  exact hC6 hZero


-- @@ L628-652 verbatim
theorem expTwoMulFixedControlInvariant_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  unfold expTwoMulFixedControlInvariant at *
  rcases hControl with ⟨hNat, hNext⟩
  constructor
  · have hPos : 1 ≤ c6.toNat := by
      have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
      omega
    rw [word_add_neg1_toNat (w := c6) hPos, hNat]
    have hmod : (k + 1) % 64 = k % 64 + 1 := by
      omega
    rw [hmod]
    omega
  · rw [hNext]
    have hdiv : (k + 1) / 64 = k / 64 := by
      omega
    rw [hdiv]


-- @@ L654-671 verbatim
theorem expTwoMulFixedControlInvariant_succ_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr loadedLimb nextNextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr loadedLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp := by
  have hMod :=
    expTwoMulFixedControlInvariant_reload_mod hControl hC6
  unfold expTwoMulFixedControlInvariant
  constructor
  · have hmod : (k + 1) % 64 = 0 := by
      omega
    simp [hmod]
  · exact hNext


-- @@ L673-687 verbatim
theorem expTwoMulFixedControlInvariant_nextLimb_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hMod : k % 64 = 63) :
    nextLimb = exponentWord.getLimbN (3 - (k + 1) / 64) := by
  unfold expTwoMulFixedControlInvariant at hControl
  rcases hControl with ⟨_, hNext⟩
  rw [hNext]
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  congr 1
  omega


-- @@ L689-710 verbatim
private theorem word_shiftLeft_succ (x : Word) (n : Nat) :
    (x <<< n) <<< 1 = x <<< (n + 1) := by
  ext i hi
  simp [BitVec.getElem_shiftLeft]
  by_cases hin : i < n + 1
  · by_cases hi1 : i = n
    · subst i
      by_cases hn0 : n = 0
      · subst n
        simp
      · simp [hn0]
    · have hlt : i < n := by omega
      simp [hin]
      have hltPred : i - 1 < n := by omega
      have hsub : i - 1 - n = i - (n + 1) := by omega
      simp [hltPred, hsub]
  · have hnot : ¬i < n := by omega
    simp [hin]
    have hi0 : ¬i = 0 := by omega
    have hnotPred : ¬i - 1 < n := by omega
    have hsub : i - 1 - n = i - (n + 1) := by omega
    simp [hi0, hnotPred, hsub]


-- @@ L712-727 verbatim
theorem expTwoMulFixedCursorInvariant_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {e : Word}
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hMod : k % 64 < 63) :
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) := by
  unfold expTwoMulFixedCursorInvariant expTwoMulFixedCursorWord at *
  rw [hCursor]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  have hmod : (k + 1) % 64 = k % 64 + 1 := by
    omega
  rw [hdiv, hmod]
  change (exponentWord.getLimbN (3 - k / 64) <<< (k % 64)) <<< 1 =
    exponentWord.getLimbN (3 - k / 64) <<< (k % 64 + 1)
  exact word_shiftLeft_succ _ _


-- @@ L729-739 verbatim
theorem expTwoMulFixedCursorInvariant_succ_reload
    {exponentWord : EvmWord} {k : Nat} {nextLimb : Word}
    (hMod : k % 64 = 63)
    (hNext : nextLimb = exponentWord.getLimbN (3 - (k + 1) / 64)) :
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb := by
  unfold expTwoMulFixedCursorInvariant expTwoMulFixedCursorWord
  rw [hNext]
  have hmod : (k + 1) % 64 = 0 := by
    omega
  rw [hmod]
  simp


-- @@ L741-750 verbatim
theorem expTwoMulFixedCursorInvariant_succ_of_control_no_reload
    {exponentWord : EvmWord} {k : Nat} {e c6 ptr nextLimb evmSp : Word}
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) :=
  expTwoMulFixedCursorInvariant_succ_no_reload hCursor
    (expTwoMulFixedControlInvariant_no_reload_mod hControl hC6)


-- @@ L752-761 verbatim
theorem expTwoMulFixedCursorInvariant_succ_of_control_reload
    {exponentWord : EvmWord} {k : Nat} {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb := by
  have hMod :=
    expTwoMulFixedControlInvariant_reload_mod hControl hC6
  exact expTwoMulFixedCursorInvariant_succ_reload hMod
    (expTwoMulFixedControlInvariant_nextLimb_reload hControl hMod)


-- @@ L763-790 verbatim
private theorem expTwoMulFixedCursorWord_highBit_eq_processedBitWord_aux
    (exponentWord : EvmWord) (q r : Nat)
    (hq : q < 4) (hr : r < 64) :
    ((exponentWord.getLimbN (3 - q) <<< r) >>> 63) =
      (if decide
          (((exponentWord >>> ((3 - q) * 64 + (63 - r))).toNat % 2) = 1)
        then (1 : Word) else 0) := by
  have hbit :
      decide
          (((exponentWord >>> ((3 - q) * 64 + (63 - r))).toNat % 2) = 1) =
        exponentWord.getLsbD ((3 - q) * 64 + (63 - r)) := by
    rw [← Nat.testBit_zero, BitVec.toNat_ushiftRight, Nat.testBit_shiftRight]
    exact BitVec.testBit_toNat exponentWord
  ext i hi
  rw [BitVec.getElem_ushiftRight]
  simp only [EvmWord.getLimbN, EvmWord.getLimb]
  rw [hbit]
  by_cases hi0 : i = 0
  · subst i
    have hnot : ¬63 < r := by omega
    have hidx : 3 - q < 4 := by omega
    simp [BitVec.getElem_extractLsb', hnot, hidx]
    cases exponentWord.getLsbD ((3 - q) * 64 + (63 - r)) <;>
      simp [BitVec.getElem_zero, BitVec.getElem_one]
  · have h64 : ¬63 + i < 64 := by omega
    simp [BitVec.getLsbD_shiftLeft, h64]
    cases exponentWord.getLsbD ((3 - q) * 64 + (63 - r)) <;>
      simp [BitVec.getElem_zero, BitVec.getElem_one, hi0]


-- @@ L792-806 verbatim
theorem expTwoMulFixedCursorWord_highBit_eq_processedBitWord
    (exponentWord : EvmWord) {k : Nat} (hk : k < 256) :
    (expTwoMulFixedCursorWord exponentWord k >>> 63) =
      expTwoMulFixedProcessedBitWord exponentWord k := by
  unfold expTwoMulFixedCursorWord expTwoMulFixedProcessedBitWord
    expTwoMulFixedProcessedBit
  have hq : k / 64 < 4 := by omega
  have hr : k % 64 < 64 := Nat.mod_lt _ (by decide)
  have hshift : (3 - k / 64) * 64 + (63 - k % 64) = 255 - k := by
    have hdecomp : k = 64 * (k / 64) + k % 64 :=
      (Nat.div_add_mod k 64).symm
    omega
  rw [expTwoMulFixedCursorWord_highBit_eq_processedBitWord_aux
    exponentWord (k / 64) (k % 64) hq hr]
  rw [hshift]


-- @@ L808-815 verbatim
theorem expTwoMulFixedCursorInvariant_highBit_eq_processedBitWord
    {exponentWord : EvmWord} {k : Nat} {e : Word}
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hk : k < 256) :
    (e >>> 63) = expTwoMulFixedProcessedBitWord exponentWord k := by
  unfold expTwoMulFixedCursorInvariant at hCursor
  rw [hCursor]
  exact expTwoMulFixedCursorWord_highBit_eq_processedBitWord exponentWord hk


-- @@ L817-837 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hBitZero : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) = 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
  exact
    expTwoMulFixedAccumulatorInvariant_succ_of_squareW_branch
      hk
      (expTwoMulFixedCursorInvariant_highBit_eq_processedBitWord hCursor hk)
      hBitZero
      hInv


-- @@ L839-865 verbatim
theorem expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hBitNe : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) := by
  exact
    expTwoMulFixedAccumulatorInvariant_succ_of_condRw_branch
      hk
      hBase
      (expTwoMulFixedCursorInvariant_highBit_eq_processedBitWord hCursor hk)
      hBitNe
      hInv


-- @@ L867-894 verbatim
theorem expTwoMulFixedNoReloadInvariants_succ_of_squareW
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb evmSp r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hBitZero : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) = 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
        hk hCursor hBitZero hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_no_reload
        hCursor hControl hC6,
      expTwoMulFixedControlInvariant_succ_no_reload hControl hC6⟩


-- @@ L896-928 verbatim
theorem expTwoMulFixedNoReloadInvariants_succ_of_condRw
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb evmSp a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hBitNe : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1)
      (e <<< (1 : BitVec 6).toNat) ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
        hk hBase hCursor hBitNe hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_no_reload
        hCursor hControl hC6,
      expTwoMulFixedControlInvariant_succ_no_reload hControl hC6⟩


-- @@ L930-958 verbatim
theorem expTwoMulFixedReloadInvariants_succ_of_squareW
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb nextNextLimb evmSp r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBitZero : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) = 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
        hk hCursor hBitZero hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6,
      expTwoMulFixedControlInvariant_succ_reload
        hControl hC6 hNextNext⟩


-- @@ L960-994 verbatim
theorem expTwoMulFixedReloadInvariants_succ_of_condRw
    {baseWord exponentWord : EvmWord} {k : Nat}
    {e c6 ptr nextLimb nextNextLimb evmSp
      a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBitNe : e >>> (63 : BitVec 6).toNat +
        signExtend12 (0 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) ∧
    expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb ∧
    expTwoMulFixedControlInvariant exponentWord (k + 1)
      64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp := by
  exact
    ⟨expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
        hk hBase hCursor hBitNe hInv,
      expTwoMulFixedCursorInvariant_succ_of_control_reload hControl hC6,
      expTwoMulFixedControlInvariant_succ_reload
        hControl hC6 hNextNext⟩


-- @@ L996-999 verbatim
@[irreducible]
def expTwoMulFixedCursorAssertion
    (exponentWord : EvmWord) (k : Nat) (e : Word) : Assertion :=
  ⌜expTwoMulFixedCursorInvariant exponentWord k e⌝


-- @@ L1001-1006 verbatim
theorem expTwoMulFixedCursorAssertion_unfold
    {exponentWord : EvmWord} {k : Nat} {e : Word} :
    expTwoMulFixedCursorAssertion exponentWord k e =
      ⌜expTwoMulFixedCursorInvariant exponentWord k e⌝ := by
  delta expTwoMulFixedCursorAssertion
  rfl


-- @@ L1008-1012 verbatim
theorem expTwoMulFixedCursorAssertion_pcFree
    {exponentWord : EvmWord} {k : Nat} {e : Word} :
    (expTwoMulFixedCursorAssertion exponentWord k e).pcFree := by
  rw [expTwoMulFixedCursorAssertion_unfold]
  pcFree


-- @@ L1014-1017 verbatim
instance pcFreeInst_expTwoMulFixedCursorAssertion
    (exponentWord : EvmWord) (k : Nat) (e : Word) :
    Assertion.PCFree (expTwoMulFixedCursorAssertion exponentWord k e) :=
  ⟨expTwoMulFixedCursorAssertion_pcFree⟩


-- @@ L1019-1023 verbatim
@[irreducible]
def expTwoMulFixedControlAssertion
    (exponentWord : EvmWord) (k : Nat)
    (c6 ptr nextLimb evmSp : Word) : Assertion :=
  ⌜expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp⌝


-- @@ L1025-1031 verbatim
theorem expTwoMulFixedControlAssertion_unfold
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word} :
    expTwoMulFixedControlAssertion exponentWord k c6 ptr nextLimb evmSp =
      ⌜expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp⌝ := by
  delta expTwoMulFixedControlAssertion
  rfl


-- @@ L1033-1039 verbatim
theorem expTwoMulFixedControlAssertion_pcFree
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word} :
    (expTwoMulFixedControlAssertion
      exponentWord k c6 ptr nextLimb evmSp).pcFree := by
  rw [expTwoMulFixedControlAssertion_unfold]
  pcFree


-- @@ L1041-1047 verbatim
instance pcFreeInst_expTwoMulFixedControlAssertion
    (exponentWord : EvmWord) (k : Nat)
    (c6 ptr nextLimb evmSp : Word) :
    Assertion.PCFree
      (expTwoMulFixedControlAssertion
        exponentWord k c6 ptr nextLimb evmSp) :=
  ⟨expTwoMulFixedControlAssertion_pcFree⟩


-- @@ L1049-1063 verbatim
/-- The fixed iteration precondition indexed by the semantic iteration count.

    This is the precondition family future fixed-loop induction should recurse
    over, instead of generating one named precondition per concrete iteration. -/
@[irreducible]
def expTwoMulFixedIterPreN
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
    vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
  expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3 **
  expTwoMulFixedCursorAssertion exponentWord k e **
  expTwoMulFixedControlAssertion exponentWord k c6 ptr nextLimb evmSp


-- @@ L1065-1079 verbatim
theorem expTwoMulFixedIterPreN_unfold
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPreN k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
        vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
      expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3 **
      expTwoMulFixedCursorAssertion exponentWord k e **
      expTwoMulFixedControlAssertion exponentWord k c6 ptr nextLimb evmSp) := by
  delta expTwoMulFixedIterPreN
  rfl


-- @@ L1081-1090 verbatim
theorem expTwoMulFixedIterPreN_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPreN k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11).pcFree := by
  rw [expTwoMulFixedIterPreN_unfold]
  pcFree


-- @@ L1092-1101 verbatim
instance pcFreeInst_expTwoMulFixedIterPreN
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPreN k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11) :=
  ⟨expTwoMulFixedIterPreN_pcFree⟩


-- @@ L1103-1116 verbatim
/-- Framed fixed iteration precondition indexed by the semantic iteration
    count. Loop-induction wrappers should use this instead of creating a fresh
    numbered residual precondition for each concrete iteration. -/
@[irreducible]
def expTwoMulFixedIterPreNWithFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (frame : Assertion) : Assertion :=
  expTwoMulFixedIterPreN k baseWord exponentWord
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
  frame


-- @@ L1118-1133 verbatim
theorem expTwoMulFixedIterPreNWithFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} :
    expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame =
      (expTwoMulFixedIterPreN k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
       frame) := by
  delta expTwoMulFixedIterPreNWithFrame
  rfl


-- @@ L1135-1146 verbatim
theorem expTwoMulFixedIterPreNWithFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} [Assertion.PCFree frame] :
    (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame).pcFree := by
  rw [expTwoMulFixedIterPreNWithFrame_unfold]
  pcFree


-- @@ L1148-1159 verbatim
instance pcFreeInst_expTwoMulFixedIterPreNWithFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (frame : Assertion) [Assertion.PCFree frame] :
    Assertion.PCFree
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame) :=
  ⟨expTwoMulFixedIterPreNWithFrame_pcFree⟩


-- @@ L1161-1184 verbatim
theorem expTwoMulFixedIterPreN_pures
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterPreN k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3 ∧
    expTwoMulFixedCursorInvariant exponentWord k e ∧
    expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp := by
  rw [expTwoMulFixedIterPreN_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold] at h
  obtain ⟨_psIter, psSemanticCursorControl, _hDisjointIter, _hUnionIter,
    _hIter, hSemanticCursorControl⟩ := h
  obtain ⟨_psSemantic, psCursorControl, _hDisjointSemantic,
    _hUnionSemantic, hSemantic, hCursorControl⟩ := hSemanticCursorControl
  obtain ⟨_psCursor, _psControl, _hDisjointCursor, _hUnionCursor,
    hCursor, hControl⟩ := hCursorControl
  exact ⟨hSemantic.2, hCursor.2, hControl.2⟩


-- @@ L1186-1202 verbatim
theorem expTwoMulFixedIterPreNWithFrame_pures
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3 ∧
    expTwoMulFixedCursorInvariant exponentWord k e ∧
    expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp := by
  rw [expTwoMulFixedIterPreNWithFrame_unfold] at h
  obtain ⟨_psPre, _psFrame, _hDisjoint, _hUnion, hPre, _hFrame⟩ := h
  exact expTwoMulFixedIterPreN_pures hPre


-- @@ L1204-1204 verbatim
end EvmAsm.Evm64.Exp.Compose
