/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge

  Bridges between the historical fixed merged postconditions and the named
  case-post presentation used by fixed loop-back bridge proofs.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L17-17 verbatim
open EvmAsm.Rv64


-- @@ L19-26 verbatim
theorem expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base =
    expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base := by
  rfl


-- @@ L28-35 verbatim
theorem expTwoMulFixedIterMergedExitPost_eq_caseExitPost
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base =
    expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base := by
  rfl


-- @@ L37-46 verbatim
abbrev expTwoMulFixedIterCaseExits
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) :
    List (Word × Assertion) :=
  [((base + 44),
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base),
   ((base + 296),
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)]


-- @@ L48-55 verbatim
theorem expTwoMulFixedIterMergedExits_eq_caseExits
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base =
    expTwoMulFixedIterCaseExits iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base := by
  rfl


-- @@ L57-64 verbatim
theorem expTwoMulFixedIterCaseLoopPost_zero_count_false
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (hzero : expTwoMulIterCountNew iterCount = 0) :
    ¬ expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost]
  exact expTwoMulFixedIterMergedLoopPost_zero_count_false hzero


-- @@ L66-73 verbatim
theorem expTwoMulFixedIterCaseExitPost_nonzero_count_false
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    ¬ expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
  exact expTwoMulFixedIterMergedExitPost_nonzero_count_false hne


-- @@ L75-97 verbatim
/-- Named-exit-list view of one fixed x19 merged iteration, stated directly
    with case-post loop and exit assertions. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseExits iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedIterMergedExits_eq_caseExits]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L99-121 verbatim
/-- Closed-form bound variant of the case-post named-exit-list fixed x19
    iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseExits iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L123-144 verbatim
/-- Bounded variant of the case-post named-exit-list fixed x19 iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_bounded_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseExits iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsNBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


-- @@ L146-173 verbatim
/-- Branch view of one fixed x19 merged iteration, stated directly with the
    named case-post loop and exit assertions. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost,
    ← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L175-200 verbatim
/-- Closed-form bound variant of the fixed x19 case-post branch spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_case_posts_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase


-- @@ L202-227 verbatim
/-- Bounded variant of the fixed x19 case-post branch spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_bounded_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
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
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_case_posts_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


-- @@ L229-264 verbatim
/-- Fixed merged-loop induction step using the named case-post loop and exit
    assertions. -/
theorem exp_fixed_loop_body_succ_step_case_posts
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  exact
    exp_fixed_loop_body_succ_step n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase
      (fun ps h => hExit ps (by
        rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
        exact h))
      hLoop


-- @@ L266-292 verbatim
/-- Non-final fixed loop-body succ step using named case-post assertions. -/
theorem exp_fixed_loop_body_nonfinal_succ_step_case_posts
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
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  exact
    exp_fixed_loop_body_nonfinal_succ_step n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hne hLoop


-- @@ L294-320 verbatim
/-- Final fixed loop-body succ step using named case-post assertions. -/
theorem exp_fixed_loop_body_final_succ_step_case_posts
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin ((0 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_fixed_loop_body_final_succ_step
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero
      (fun ps h => hExit ps (by
        rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
        exact h))


-- @@ L322-349 verbatim
/-- Bounded non-final fixed loop-body succ step using named case-post
    assertions. -/
theorem exp_fixed_loop_body_nonfinal_succ_step_case_posts_bounded
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
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin nBound (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_fixed_loop_body_nonfinal_succ_step_case_posts n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hne hLoop)


-- @@ L351-375 verbatim
/-- Closed 193-step final fixed loop-body succ step using named case-post
    assertions. -/
theorem exp_fixed_loop_body_final_succ_step_case_posts_closed_bound
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin 193 (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  simpa using
    exp_fixed_loop_body_final_succ_step_case_posts
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero hExit


-- @@ L377-402 verbatim
/-- Bounded final fixed loop-body succ step using named case-post assertions. -/
theorem exp_fixed_loop_body_final_succ_step_case_posts_bounded
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
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin nBound (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  cpsTripleWithin_mono_nSteps hBound
    (exp_fixed_loop_body_final_succ_step_case_posts_closed_bound
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero hExit)


-- @@ L404-415 verbatim
/-- Vacuous bridge from a non-final fixed case-post exit assertion. -/
theorem exp_fixed_iter_case_exit_vacuous_bridge
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    {Q : PartialState → Prop} :
    ∀ ps,
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps →
      Q ps := by
  rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
  exact exp_fixed_iter_merged_exit_vacuous_bridge hne


-- @@ L417-429 verbatim
/-- Zero-step body spec from a fixed case-post loop-back assertion whose
    decremented iteration count is zero. -/
theorem exp_fixed_iter_case_loop_zero_step_vacuous
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hzero : expTwoMulIterCountNew iterCount = 0)
    {Q : Assertion} {entry exit_ : Word} {code : CodeReq} :
    cpsTripleWithin 0 entry exit_ code
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      Q := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost]
  exact exp_fixed_iter_merged_loop_zero_step_vacuous hzero


-- @@ L431-466 verbatim
/-- Peel one fixed x19 iteration from the conservative 256-iteration body
    using named case-post continuations for both branch targets. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_case_continuations_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
  intro hLoop hExit
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost] at hExit
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L468-503 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_with_case_continuations_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_case_continuations_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin 49215
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin 49215
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
    exp_two_mul_fixed_full_loop_body_peel_tail_with_case_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L505-536 verbatim
/-- Final-count full-tail peel using named case-post assertions: the loop
    branch is impossible, so only the exit continuation is needed. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_final_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
  intro hExit
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_case_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (exp_fixed_iter_case_loop_zero_step_vacuous hzero))
      hExit


-- @@ L538-568 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_case_final_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_final_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0) :
    (cpsTripleWithin 49215
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
  intro hExit
  rw [← expTwoMulFixedFullLoopBodyTailBound_eq] at hExit
  rw [← expTwoMulFixedFullLoopBodyBound_eq]
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_case_final_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hzero hExit


-- @@ L570-601 verbatim
/-- Final-count full-tail peel with an immediate exit implication over named
    case-post assertions. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin expTwoMulFixedFullLoopBodyBound
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_full_loop_body_peel_tail_case_final_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base (base + 296) R hbase hzero
    (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit)))


-- @@ L603-630 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin 49408
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedFullLoopBodyBound_eq]
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_case_final_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero hExit


-- @@ L632-669 verbatim
/-- Peel one fixed x19 iteration from the conservative 256-iteration body
    using named case-post assertions and an explicit exit bridge. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
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
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  exact
    exp_two_mul_fixed_full_loop_body_peel_tail_with_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase
      (fun ps h => hExit ps (by
        rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
        exact h))
      hLoop


-- @@ L671-705 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    (cpsTripleWithin 49215
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
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
    exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hExit hLoop


-- @@ L707-733 verbatim
/-- Non-final fixed full-tail peel using named case-post assertions. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_nonfinal_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
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
  exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (exp_fixed_iter_case_exit_vacuous_bridge hne)


-- @@ L735-762 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_full_loop_body_peel_tail_case_nonfinal_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_body_peel_tail_case_nonfinal_closed_bound_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin 49215
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
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
  exp_two_mul_fixed_full_loop_body_peel_tail_with_case_exit_imp_closed_bound_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base R hbase
    (exp_fixed_iter_case_exit_vacuous_bridge hne)


-- @@ L764-799 verbatim
/-- Merge one fixed x19 iteration with externally supplied continuations,
    stated directly over named case-post assertions. -/
theorem exp_two_mul_fixed_iter_case_posts_with_continuations_spec_within
    {nCont : Nat} {exit_ : Word} {R : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin nCont (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nCont (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost] at hExit
  exact
    exp_two_mul_fixed_iter_merged_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase hLoop hExit


-- @@ L801-836 verbatim
/-- Case-post variant of the fixed x19 iteration continuation wrapper with
    separate loop and exit continuation bounds. -/
theorem exp_two_mul_fixed_iter_case_posts_with_continuations_max_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
    exp_two_mul_fixed_iter_case_posts_with_continuations_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit)


-- @@ L838-872 verbatim
/-- Bounded case-post variant of the fixed x19 iteration continuation wrapper. -/
theorem exp_two_mul_fixed_iter_case_posts_with_continuations_bounded_spec_within
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
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin nExit (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
      (exp_two_mul_fixed_iter_case_posts_with_continuations_max_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase hLoop hExit)


-- @@ L874-908 verbatim
/-- Peel one fixed iteration from an `(iterations + 1)`-iteration body using
    named case-post continuations. -/
theorem exp_two_mul_fixed_iterations_body_peel_with_case_continuations_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R :=
  exp_two_mul_fixed_iter_case_posts_with_continuations_bounded_spec_within
    e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
    v7 v11 base hbase
    (expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_le_succ
      iterations)


-- @@ L910-948 verbatim
/-- Non-final variant of the arbitrary-iteration fixed-body peel.  The exit
    branch is impossible, so the caller only supplies the recursive loop
    continuation. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop
  exact
    exp_two_mul_fixed_iterations_body_peel_with_case_continuations_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base (base + 296) R hbase hLoop
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (cpsTripleWithin_extend_code
          (hmono := by
            intro a i h
            cases h)
          (cpsTripleWithin_refl
            (exp_fixed_iter_case_exit_vacuous_bridge hne))))


-- @@ L950-986 verbatim
/-- Final variant of the arbitrary-iteration fixed-body peel.  The loop branch
    is impossible, so the caller only supplies the exit bridge. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_two_mul_fixed_iterations_body_peel_with_case_continuations_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base (base + 296) R hbase
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (exp_fixed_iter_case_loop_zero_step_vacuous hzero))
      (cpsTripleWithin_mono_nSteps (Nat.zero_le _)
        (cpsTripleWithin_extend_code
          (hmono := by
            intro a i h
            cases h)
          (cpsTripleWithin_refl hExit)))


-- @@ L988-1025 verbatim
/-- Closed-form variant of
    `exp_two_mul_fixed_iterations_body_peel_with_case_continuations_spec_within`. -/
theorem exp_two_mul_fixed_iterations_body_peel_with_case_continuations_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base exit_ : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    (cpsTripleWithin (iterations * 193)
      (base + 296) exit_
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
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
    exp_two_mul_fixed_iterations_body_peel_with_case_continuations_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base exit_ R hbase hLoop hExit


-- @@ L1027-1059 verbatim
/-- Closed-form non-final arbitrary-iteration peel.  This is the arithmetic
    presentation used by Nat induction over the remaining fixed-loop length. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_nonfinal_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0) :
    (cpsTripleWithin (iterations * 193)
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      R) →
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  intro hLoop
  rw [← expTwoMulFixedIterationsBodyBound_eq iterations] at hLoop
  rw [← expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_fixed_iterations_body_peel_case_nonfinal_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hne hLoop


-- @@ L1061-1090 verbatim
/-- Closed-form final arbitrary-iteration peel.  The remaining loop branch is
    impossible, so the theorem exposes only the final exit bridge. -/
theorem exp_two_mul_fixed_iterations_body_peel_case_final_closed_bound_spec_within
    (iterations : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin ((iterations + 1) * 193)
      (base + 44)
      (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_fixed_iterations_body_peel_case_final_spec_within
      iterations
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero hExit


-- @@ L1092-1092 verbatim
end EvmAsm.Evm64.Exp.Compose
