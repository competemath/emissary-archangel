/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStatePre

  Fixed-loop preconditions that carry the bundled induction state.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterState
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariantWithControl


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L16-16 verbatim
open EvmAsm.Rv64


-- @@ L18-30 verbatim
/-- Fixed iteration precondition indexed by semantic iteration count, carrying
    the bundled accumulator/cursor/control/count state as one pure assertion. -/
@[irreducible]
def expTwoMulFixedIterPreNWithState
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
    tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
  expTwoMulFixedIterStateAssertion baseWord exponentWord k
    iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3


-- @@ L32-46 verbatim
theorem expTwoMulFixedIterPreNWithState_unfold
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
      (expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb sp
        evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
       expTwoMulFixedIterStateAssertion baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3) := by
  delta expTwoMulFixedIterPreNWithState
  rfl


-- @@ L48-57 verbatim
theorem expTwoMulFixedIterPreNWithState_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11).pcFree := by
  rw [expTwoMulFixedIterPreNWithState_unfold]
  pcFree


-- @@ L59-68 verbatim
instance pcFreeInst_expTwoMulFixedIterPreNWithState
    (k : Nat) (baseWord exponentWord : EvmWord) (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11) :=
  ⟨expTwoMulFixedIterPreNWithState_pcFree⟩


-- @@ L70-82 verbatim
/-- Framed version of `expTwoMulFixedIterPreNWithState`. -/
@[irreducible]
def expTwoMulFixedIterPreNWithStateFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (frame : Assertion) : Assertion :=
  expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
    e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
  frame


-- @@ L84-99 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} :
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame =
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
       frame) := by
  delta expTwoMulFixedIterPreNWithStateFrame
  rfl


-- @@ L101-112 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} [Assertion.PCFree frame] :
    (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame).pcFree := by
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold]
  pcFree


-- @@ L114-125 verbatim
instance pcFreeInst_expTwoMulFixedIterPreNWithStateFrame
    (k : Nat) (baseWord exponentWord : EvmWord) (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (frame : Assertion) [Assertion.PCFree frame] :
    Assertion.PCFree
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame) :=
  ⟨expTwoMulFixedIterPreNWithStateFrame_pcFree⟩


-- @@ L127-136 verbatim
private theorem pure_assertion_eq_emp_of_true {p : Prop} (hp : p) :
    (⌜p⌝ : Assertion) = empAssertion := by
  rw [← pure_true_eq_emp]
  funext ps
  apply propext
  constructor
  · intro h
    exact ⟨h.1, trivial⟩
  · intro h
    exact ⟨h.1, hp⟩


-- @@ L138-153 verbatim
theorem expTwoMulFixedIterPreNWithState_pure
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  rw [expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterStateAssertion_unfold] at h
  obtain ⟨_psIter, _psState, _hDisjoint, _hUnion, _hIter, hState⟩ := h
  exact hState.2


-- @@ L155-170 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_pure
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord k
      iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold] at h
  obtain ⟨_psPre, _psFrame, _hDisjoint, _hUnion, hPre, _hFrame⟩ := h
  exact expTwoMulFixedIterPreNWithState_pure hPre


-- @@ L172-199 verbatim
theorem expTwoMulFixedIterPreNWithState_succ_no_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word}
    {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (h :
      expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      (e <<< (1 : BitVec 6).toNat)
      (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_no_reload
    hk hBase hBit hC6 (expTwoMulFixedIterPreNWithState_pure h)


-- @@ L201-230 verbatim
theorem expTwoMulFixedIterPreNWithState_succ_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {controlC6 machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word}
    {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (h :
      expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        nextLimb machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      nextLimb 64 (ptr + signExtend12 (-8 : BitVec 12))
      nextNextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_reload
    hk hBase hBit hC6 hNextNext (expTwoMulFixedIterPreNWithState_pure h)


-- @@ L232-260 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_succ_no_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (h :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      (e <<< (1 : BitVec 6).toNat)
      (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_no_reload
    hk hBase hBit hC6 (expTwoMulFixedIterPreNWithStateFrame_pure h)


-- @@ L262-293 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_succ_reload
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {controlC6 machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (h :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        nextLimb machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount)
      nextLimb 64 (ptr + signExtend12 (-8 : BitVec 12))
      nextNextLimb evmSp
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) :=
  expTwoMulFixedIterStateInvariant_succ_reload
    hk hBase hBit hC6 hNextNext
      (expTwoMulFixedIterPreNWithStateFrame_pure h)


-- @@ L295-310 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_pures
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3 ∧
    expTwoMulFixedCursorInvariant exponentWord k e ∧
    expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb evmSp ∧
    expTwoMulFixedIterCountInvariant k iterCount := by
  exact expTwoMulFixedIterPreNWithStateFrame_pure h


-- @@ L312-344 verbatim
theorem expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame ps := by
  rcases expTwoMulFixedIterPreNWithStateFrame_pures h with
    ⟨h_acc, h_cursor, h_control, h_count⟩
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterStateAssertion_unfold] at h
  rw [pure_assertion_eq_emp_of_true
    ⟨h_acc, h_cursor, h_control, h_count⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  exact h


-- @@ L346-379 verbatim
theorem expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {frame : Assertion} {ps : PartialState}
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (h :
      expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      frame ps := by
  rcases expTwoMulFixedIterPreNWithControlFrame_pures h with
    ⟨h_acc, h_cursor, h_control⟩
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold] at h
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control] at h
  simp only [sepConj_emp_right'] at h
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterStateAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true
    ⟨h_acc, h_cursor, h_control, hCount⟩]
  simp only [sepConj_emp_right']
  exact h


-- @@ L381-405 verbatim
theorem expTwoMulFixedIterPreNWithState_to_iterPreNWithControl
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterPreNWithState k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps) :
    expTwoMulFixedIterPreNWithControl k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 ps := by
  have hFrame :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
        empAssertion ps := by
    rw [expTwoMulFixedIterPreNWithStateFrame_unfold]
    rw [sepConj_emp_right']
    exact h
  have hControlFrame :=
    expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame hFrame
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold] at hControlFrame
  simpa [sepConj_emp_right'] using hControlFrame


-- @@ L407-407 verbatim
end EvmAsm.Evm64.Exp.Compose
