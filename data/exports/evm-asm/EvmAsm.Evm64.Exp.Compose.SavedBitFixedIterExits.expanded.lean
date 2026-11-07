/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits

  Named exit postconditions for the fixed x19 merged EXP iteration.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul


-- @@ L11-11 verbatim
public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-97 verbatim
abbrev expTwoMulFixedIterMergedLoopPost
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let ptrFrame : Assertion :=
    (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
  let skipCondFrame : Assertion :=
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x20 ↦ᵣ c6New) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let skipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x20 ↦ᵣ c6New) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let skipCondRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ rw.getLimbN 3) **
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
    evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  let reloadCondFrame : Assertion :=
    (.x19 ↦ᵣ nextLimb) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let reloadSkipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ nextLimb) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let reloadCondRest : Assertion := skipCondRest
  let skipLoopPost : Assertion :=
    (fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
      ptrFrame
  let reloadLoopPost : Assertion :=
    fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
  fun h => skipLoopPost h ∨ reloadLoopPost h


-- @@ L99-179 verbatim
abbrev expTwoMulFixedIterMergedExitPost
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let ptrFrame : Assertion :=
    (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
  let skipCondFrame : Assertion :=
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x20 ↦ᵣ c6New) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let skipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x20 ↦ᵣ c6New) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let skipCondRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ rw.getLimbN 3) **
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
    evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  let reloadCondFrame : Assertion :=
    (.x19 ↦ᵣ nextLimb) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let reloadSkipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ nextLimb) **
    (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let reloadCondRest : Assertion := skipCondRest
  let skipExitPost : Assertion :=
    (fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
      ptrFrame
  let reloadExitPost : Assertion :=
    fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
  fun h => skipExitPost h ∨ reloadExitPost h


-- @@ L181-214 verbatim
/-- The fixed merged loop-back post is unsatisfiable when the decremented
    iteration count is zero: every loop-back case embeds
    `⌜expTwoMulIterCountNew iterCount ≠ 0⌝`. -/
theorem expTwoMulFixedIterMergedLoopPost_zero_count_false
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (hzero : expTwoMulIterCountNew iterCount = 0) :
    ¬ expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  unfold expTwoMulFixedIterMergedLoopPost
  rintro (hSkipLoop | hReloadLoop)
  · obtain ⟨_, _, _, _, hSkipCases, _⟩ := hSkipLoop
    rcases hSkipCases with hCond | hSkip
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hPure.2 hzero
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hPure.2 hzero
  · rcases hReloadLoop with hCond | hSkip
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hPure.2 hzero
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hPure.2 hzero


-- @@ L216-249 verbatim
/-- The fixed merged exit post is unsatisfiable when the decremented iteration
    count is nonzero: every exit case embeds
    `⌜expTwoMulIterCountNew iterCount = 0⌝`. -/
theorem expTwoMulFixedIterMergedExitPost_nonzero_count_false
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    ¬ expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  unfold expTwoMulFixedIterMergedExitPost
  rintro (hSkipExit | hReloadExit)
  · obtain ⟨_, _, _, _, hSkipCases, _⟩ := hSkipExit
    rcases hSkipCases with hCond | hSkip
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hne hPure.2
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hne hPure.2
  · rcases hReloadExit with hCond | hSkip
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hCond
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hne hPure.2
    · obtain ⟨_, _, _, _, hHeadRest, _⟩ := hSkip
      obtain ⟨_, _, _, _, hTriple, _⟩ := hHeadRest
      obtain ⟨_, _, _, _, _, hX0Pure⟩ := hTriple
      obtain ⟨_, _, _, _, _, hPure⟩ := hX0Pure
      exact hne hPure.2


-- @@ L251-262 verbatim
/-- Vacuous bridge from a non-final fixed merged exit post. -/
theorem exp_fixed_iter_merged_exit_vacuous_bridge
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    {Q : PartialState → Prop} :
    ∀ ps,
      expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps →
      Q ps :=
  fun _ hExit =>
    absurd hExit (expTwoMulFixedIterMergedExitPost_nonzero_count_false hne)


-- @@ L264-279 verbatim
/-- Zero-step body spec from a fixed merged loop-back post whose decremented
    iteration count is zero. -/
theorem exp_fixed_iter_merged_loop_zero_step_vacuous
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hzero : expTwoMulIterCountNew iterCount = 0)
    {Q : Assertion} {entry exit_ : Word} {code : CodeReq} :
    cpsTripleWithin 0 entry exit_ code
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      Q := by
  intro R _ s _ hPR _
  exfalso
  have hP := holdsFor_sepConj_elim_left hPR
  obtain ⟨_, _, h_looppost⟩ := hP
  exact expTwoMulFixedIterMergedLoopPost_zero_count_false hzero h_looppost


-- @@ L281-290 verbatim
abbrev expTwoMulFixedIterMergedExits
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) :
    List (Word × Assertion) :=
  [((base + 44),
      expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base),
   ((base + 296),
      expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)]


-- @@ L292-315 verbatim
/-- Named-exit-list view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  simpa [expTwoMulFixedIterMergedExits, expTwoMulFixedIterMergedLoopPost,
    expTwoMulFixedIterMergedExitPost]
    using
      exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase


-- @@ L317-339 verbatim
/-- Closed-form bound variant of the named-exit-list fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsNBranchWithin
      193
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L341-363 verbatim
/-- Bounded variant of the named-exit-list fixed x19 merged full-iteration
    spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_bounded_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    {nBound : Nat} (hBound : 193 ≤ nBound) :
    cpsNBranchWithin
      nBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsNBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_merged_named_exits_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


-- @@ L365-410 verbatim
/-- Merge one fixed x19 canonical appended-MUL EXP iteration with externally
    supplied continuations for the loop-back and loop-exit edges. -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_spec_within
    {nCont : Nat} {exit_ : Word} {R : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin nCont (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + nCont)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  refine
    cpsNBranchWithin_merge
      (exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase) ?_
  intro ex hmem
  rw [expTwoMulFixedIterMergedExits] at hmem
  cases hmem with
  | head =>
      exact hLoop
  | tail _ htail =>
      cases htail with
      | head =>
          exact hExit
      | tail _ hnil =>
          cases hnil


-- @@ L412-448 verbatim
/-- Variant of `exp_two_mul_fixed_iter_merged_with_continuations_spec_within`
    that permits different bounds for the loop-back and loop-exit
    continuations. -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_max_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin
      (expTwoMulFixedReloadIterStepBound + max nLoop nExit)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit)


-- @@ L450-485 verbatim
/-- Bounded variant of
    `exp_two_mul_fixed_iter_merged_with_continuations_max_spec_within`. -/
theorem exp_two_mul_fixed_iter_merged_with_continuations_bounded_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hBound :
      expTwoMulFixedReloadIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin nBound
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_fixed_iter_merged_with_continuations_max_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase hLoop hExit)


-- @@ L487-523 verbatim
/-- Peel one fixed x19 merged iteration from an `(iterations + 1)`-iteration
    body when both branch continuations are packaged under the
    `iterations`-iteration tail bound. -/
theorem exp_two_mul_fixed_iterations_body_peel_with_continuations_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_bounded_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
      (expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_le_succ
        iterations)


-- @@ L525-563 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_iterations_body_peel_with_continuations_spec_within`,
    exposing each fixed x19 iteration as `193` steps. -/
theorem exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin (iterations * 193)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq iterations] at hLoop hExit
  rw [← expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_fixed_iterations_body_peel_with_continuations_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L565-602 verbatim
/-- Fixed x19 256-iteration loop-body wrapper.

    This is the single concrete 256 instantiation of the parameterized fixed
    loop-body theorem.  The proof delegates to the generic `(n + 1)` body
    composition at `n = 255`; it does not introduce another named
    per-iteration peel. -/
theorem exp_two_mul_256iter_loop_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound 255)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound 255)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound 256)
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  simpa using
    exp_two_mul_fixed_iterations_body_peel_with_continuations_spec_within
      255
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase


-- @@ L604-642 verbatim
/-- Closed-bound form of `exp_two_mul_256iter_loop_spec_within`. -/
theorem exp_two_mul_256iter_loop_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin 49215
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin 49215
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin 49408
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  have hTail : expTwoMulFixedIterationsBodyBound 255 = 49215 := by
    rw [expTwoMulFixedIterationsBodyBound_eq]
  have hFull : expTwoMulFixedIterationsBodyBound 256 = 49408 := by
    rw [expTwoMulFixedIterationsBodyBound_eq]
  rw [← hTail] at hLoop hExit
  rw [← hFull]
  exact
    exp_two_mul_256iter_loop_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L644-682 verbatim
/-- Fixed merged-loop induction step: given any exit bridge for the current
    step's exit condition and any `n`-iteration loop-back continuation, the
    `(n + 1)`-iteration body spec holds from `expTwoMulFixedIterPre`. -/
theorem exp_fixed_loop_body_succ_step
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_two_mul_fixed_iterations_body_peel_with_continuations_closed_bound_spec_within
      n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base (base + 296) R hbase hLoop
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (cpsTripleWithin_extend_code
          (hmono := by
            intro a i h
            cases h)
          (cpsTripleWithin_refl hExit)))


-- @@ L684-709 verbatim
/-- Non-final fixed merged-loop induction step: the current exit edge is
    impossible, so only the `n`-iteration loop-back continuation is needed. -/
theorem exp_fixed_loop_body_nonfinal_succ_step
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_fixed_loop_body_succ_step
    n e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    base R hbase (exp_fixed_iter_merged_exit_vacuous_bridge hne) hLoop


-- @@ L711-737 verbatim
/-- Bounded non-final fixed merged-loop induction step. -/
theorem exp_fixed_loop_body_nonfinal_succ_step_bounded
    (n nBound : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hBound : (n + 1) * 193 ≤ nBound)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin nBound (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_fixed_loop_body_nonfinal_succ_step
      n e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      base R hbase hne hLoop)


-- @@ L739-763 verbatim
/-- Final fixed merged-loop induction step: the loop-back edge is impossible,
    so only an exit bridge is needed. -/
theorem exp_fixed_loop_body_final_succ_step
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin ((0 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_fixed_loop_body_succ_step
    0 e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    base R hbase hExit
    (exp_fixed_iter_merged_loop_zero_step_vacuous hzero)


-- @@ L765-788 verbatim
/-- Closed 193-step variant of `exp_fixed_loop_body_final_succ_step`. -/
theorem exp_fixed_loop_body_final_succ_step_closed_bound
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin 193 (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  simpa using
    exp_fixed_loop_body_final_succ_step
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      base R hbase hzero hExit


-- @@ L790-815 verbatim
/-- Bounded final fixed merged-loop induction step. -/
theorem exp_fixed_loop_body_final_succ_step_bounded
    (nBound : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hBound : 193 ≤ nBound)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin nBound (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_fixed_loop_body_final_succ_step_closed_bound
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      base R hbase hzero hExit)


-- @@ L817-851 verbatim
/-- Peel one fixed x19 merged iteration from the conservative 256-iteration
    body when both branch continuations are packaged under the named
    255-iteration tail bound. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin expTwoMulFixedFullLoopBodyBound
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_bounded_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
      expTwoMulFixedReloadIterStepBound_add_max_fullTail_le_full


-- @@ L853-890 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_spec_within`,
    exposing the conservative 256-iteration body as `49408` steps and the
    255-iteration tail as `49215` steps. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin 49215
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin 49215
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin 49408
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop hExit
  rw [← expTwoMulFixedFullLoopBodyTailBound_eq] at hLoop hExit
  rw [← expTwoMulFixedFullLoopBodyBound_eq]
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L892-930 verbatim
/-- Peel one fixed x19 merged iteration from the conservative 256-iteration
    body, reducing the exit edge to a zero-step assertion bridge. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin expTwoMulFixedFullLoopBodyBound
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base (base + 296) R hbase hLoop
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (cpsTripleWithin_extend_code
          (hmono := by
            intro a i h
            cases h)
          (cpsTripleWithin_refl hExit)))


-- @@ L932-966 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    (cpsTripleWithin 49215
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin 49408
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop
  rw [← expTwoMulFixedFullLoopBodyTailBound_eq] at hLoop
  rw [← expTwoMulFixedFullLoopBodyBound_eq]
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hExit hLoop


-- @@ L968-995 verbatim
/-- Non-final fixed full-tail peel: when the current merged exit edge is
    impossible, only the loop-back tail continuation is needed. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_nonfinal_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin expTwoMulFixedFullLoopBodyBound
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (exp_fixed_iter_merged_exit_vacuous_bridge hne)


-- @@ L997-1024 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_nonfinal_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_nonfinal_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin 49215
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin 49408
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_closed_bound_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (exp_fixed_iter_merged_exit_vacuous_bridge hne)


-- @@ L1026-1053 verbatim
/-- Branch view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec with named loop/exit postconditions. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  simpa [expTwoMulFixedIterMergedExits]
    using
      cpsNBranchWithin_as_cpsBranchWithin
        (exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
          e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 base hbase)


-- @@ L1055-1081 verbatim
/-- Closed-form bound variant of the named fixed x19 merged full-iteration
    branch. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsBranchWithin
      193
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L1083-1108 verbatim
/-- Bounded variant of the named fixed x19 merged full-iteration branch. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_branch_bounded_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    {nBound : Nat} (hBound : 193 ≤ nBound) :
    cpsBranchWithin
      nBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_merged_named_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)



-- @@ L1111-1133 verbatim
/-- Body-only-code-req twins of the named-exits / closed-bound / bounded merged-iter specs (path A, bug fjivz). -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  simpa [expTwoMulFixedIterMergedExits, expTwoMulFixedIterMergedLoopPost,
    expTwoMulFixedIterMergedExitPost]
    using
      exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase


-- @@ L1135-1157 verbatim
/-- Closed-form bound variant of the named-exit-list fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_closed_bound_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsNBranchWithin
      193
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_exits_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L1159-1181 verbatim
/-- Bounded variant of the named-exit-list fixed x19 merged full-iteration
    spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_bounded_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    {nBound : Nat} (hBound : 193 ≤ nBound) :
    cpsNBranchWithin
      nBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsNBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_merged_named_exits_closed_bound_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


-- @@ L1183-1183 verbatim
end EvmAsm.Evm64.Exp.Compose
