/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

  Named step-count expressions for the two-MUL saved-bit EXP loop
  composition helpers.
-/

module

public import EvmAsm.Evm64.Exp.Compose.Base


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L16-19 verbatim
/-- Instruction bound for one named saved-bit two-MUL iteration, excluding
    externally supplied loop-back and loop-exit continuations. -/
abbrev expTwoMulNamedIterStepBound : Nat :=
  (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))


-- @@ L21-23 verbatim
/-- Bound for the fixed-x19 no-reload saved-bit two-MUL iteration slice. -/
abbrev expTwoMulFixedSkipIterStepBound : Nat :=
  (((((4 + 1) + (17 + 64 + 9)) + 1) + 2) + ((17 + 64 + 9) + 2))


-- @@ L25-27 verbatim
/-- Bound for the fixed-x19 reload saved-bit two-MUL iteration slice. -/
abbrev expTwoMulFixedReloadIterStepBound : Nat :=
  (((((7 + 1) + (17 + 64 + 9)) + 1) + 2) + ((17 + 64 + 9) + 2))


-- @@ L29-31 verbatim
/-- Bound for the prologue/pointer-advance boundary before the saved-bit
    two-MUL loop. -/
abbrev expTwoMulBoundaryPrefixBound : Nat := 6 + 1


-- @@ L33-35 verbatim
/-- Bound for the pointer-restore/epilogue boundary after the saved-bit
    two-MUL loop exits. -/
abbrev expTwoMulBoundarySuffixBound : Nat := 1 + 9


-- @@ L37-40 verbatim
/-- Bound for the named saved-bit two-MUL boundary composition around a loop
    proof with `nSteps`. -/
abbrev expTwoMulBoundaryLoopBound (nSteps : Nat) : Nat :=
  (expTwoMulBoundaryPrefixBound + nSteps) + expTwoMulBoundarySuffixBound


-- @@ L42-44 verbatim
/-- Bound for `iterations` saved-bit two-MUL loop iterations. -/
abbrev expTwoMulIterationsBodyBound (iterations : Nat) : Nat :=
  iterations * expTwoMulNamedIterStepBound


-- @@ L46-49 verbatim
/-- Conservative bound for `iterations` fixed-x19 saved-bit two-MUL loop
    iterations, using the reload-path bound for every iteration. -/
abbrev expTwoMulFixedIterationsBodyBound (iterations : Nat) : Nat :=
  iterations * expTwoMulFixedReloadIterStepBound


-- @@ L51-54 verbatim
/-- Aggregate bound for 256 saved-bit two-MUL loop iterations, excluding the
    prologue/pointer-advance and pointer-restore/epilogue boundary. -/
abbrev expTwoMulFullLoopBodyBound : Nat :=
  expTwoMulIterationsBodyBound 256


-- @@ L56-59 verbatim
/-- Conservative aggregate bound for 256 fixed-x19 saved-bit two-MUL loop
    iterations. -/
abbrev expTwoMulFixedFullLoopBodyBound : Nat :=
  expTwoMulFixedIterationsBodyBound 256


-- @@ L61-64 verbatim
/-- Remaining body bound after peeling one iteration from the 256-iteration
    saved-bit two-MUL loop. -/
abbrev expTwoMulFullLoopBodyTailBound : Nat :=
  expTwoMulIterationsBodyBound 255


-- @@ L66-69 verbatim
/-- Conservative remaining fixed-x19 body bound after peeling one iteration
    from the 256-iteration saved-bit two-MUL loop. -/
abbrev expTwoMulFixedFullLoopBodyTailBound : Nat :=
  expTwoMulFixedIterationsBodyBound 255


-- @@ L71-74 verbatim
/-- Aggregate bound for the full saved-bit two-MUL loop including the
    prologue/pointer-advance and pointer-restore/epilogue boundary. -/
abbrev expTwoMulFullLoopBoundaryBound : Nat :=
  expTwoMulBoundaryLoopBound expTwoMulFullLoopBodyBound


-- @@ L76-78 verbatim
theorem expTwoMulNamedIterStepBound_eq :
    expTwoMulNamedIterStepBound = 189 := by
  norm_num [expTwoMulNamedIterStepBound]


-- @@ L80-82 verbatim
theorem expTwoMulFixedSkipIterStepBound_eq :
    expTwoMulFixedSkipIterStepBound = 190 := by
  norm_num [expTwoMulFixedSkipIterStepBound]


-- @@ L84-86 verbatim
theorem expTwoMulFixedReloadIterStepBound_eq :
    expTwoMulFixedReloadIterStepBound = 193 := by
  norm_num [expTwoMulFixedReloadIterStepBound]


-- @@ L88-91 verbatim
theorem expTwoMulFixedSkipIterStepBound_le_reload :
    expTwoMulFixedSkipIterStepBound ≤ expTwoMulFixedReloadIterStepBound := by
  rw [expTwoMulFixedSkipIterStepBound_eq, expTwoMulFixedReloadIterStepBound_eq]
  omega


-- @@ L93-97 verbatim
theorem expTwoMulBoundaryLoopBound_eq (nSteps : Nat) :
    expTwoMulBoundaryLoopBound nSteps = nSteps + 17 := by
  unfold expTwoMulBoundaryLoopBound expTwoMulBoundaryPrefixBound
    expTwoMulBoundarySuffixBound
  omega


-- @@ L99-101 verbatim
theorem expTwoMulIterationsBodyBound_zero :
    expTwoMulIterationsBodyBound 0 = 0 := by
  rfl


-- @@ L103-105 verbatim
theorem expTwoMulIterationsBodyBound_eq (iterations : Nat) :
    expTwoMulIterationsBodyBound iterations = iterations * 189 := by
  rw [expTwoMulIterationsBodyBound, expTwoMulNamedIterStepBound_eq]


-- @@ L107-109 verbatim
theorem expTwoMulFixedIterationsBodyBound_zero :
    expTwoMulFixedIterationsBodyBound 0 = 0 := by
  rfl


-- @@ L111-113 verbatim
theorem expTwoMulFixedIterationsBodyBound_eq (iterations : Nat) :
    expTwoMulFixedIterationsBodyBound iterations = iterations * 193 := by
  rw [expTwoMulFixedIterationsBodyBound, expTwoMulFixedReloadIterStepBound_eq]


-- @@ L115-119 verbatim
theorem expTwoMulIterationsBodyBound_succ (iterations : Nat) :
    expTwoMulIterationsBodyBound (iterations + 1) =
      expTwoMulNamedIterStepBound + expTwoMulIterationsBodyBound iterations := by
  unfold expTwoMulIterationsBodyBound
  rw [Nat.add_one, Nat.succ_mul, Nat.add_comm]


-- @@ L121-126 verbatim
theorem expTwoMulFixedIterationsBodyBound_succ (iterations : Nat) :
    expTwoMulFixedIterationsBodyBound (iterations + 1) =
      expTwoMulFixedReloadIterStepBound +
        expTwoMulFixedIterationsBodyBound iterations := by
  unfold expTwoMulFixedIterationsBodyBound
  rw [Nat.add_one, Nat.succ_mul, Nat.add_comm]


-- @@ L128-132 verbatim
theorem expTwoMulNamedIterStepBound_add_iterationsBodyBound_le_succ
    (iterations : Nat) :
    expTwoMulNamedIterStepBound + expTwoMulIterationsBodyBound iterations ≤
      expTwoMulIterationsBodyBound (iterations + 1) := by
  rw [expTwoMulIterationsBodyBound_succ]


-- @@ L134-139 verbatim
theorem expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
    (iterations : Nat) :
    expTwoMulFixedReloadIterStepBound +
        expTwoMulFixedIterationsBodyBound iterations ≤
      expTwoMulFixedIterationsBodyBound (iterations + 1) := by
  rw [expTwoMulFixedIterationsBodyBound_succ]


-- @@ L141-148 verbatim
theorem expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_le_succ
    (iterations : Nat) :
    expTwoMulNamedIterStepBound +
        max (expTwoMulIterationsBodyBound iterations)
          (expTwoMulIterationsBodyBound iterations) ≤
      expTwoMulIterationsBodyBound (iterations + 1) := by
  rw [Nat.max_self]
  exact expTwoMulNamedIterStepBound_add_iterationsBodyBound_le_succ iterations


-- @@ L150-159 verbatim
theorem expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_le_succ
    (iterations : Nat) :
    expTwoMulFixedReloadIterStepBound +
        max (expTwoMulFixedIterationsBodyBound iterations)
          (expTwoMulFixedIterationsBodyBound iterations) ≤
      expTwoMulFixedIterationsBodyBound (iterations + 1) := by
  rw [Nat.max_self]
  exact
    expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations


-- @@ L161-167 verbatim
theorem expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_zero_le_succ
    (iterations : Nat) :
    expTwoMulNamedIterStepBound +
        max (expTwoMulIterationsBodyBound iterations) 0 ≤
      expTwoMulIterationsBodyBound (iterations + 1) := by
  rw [Nat.max_eq_left (Nat.zero_le _)]
  exact expTwoMulNamedIterStepBound_add_iterationsBodyBound_le_succ iterations


-- @@ L169-177 verbatim
theorem expTwoMulFixedReloadIterStepBound_add_max_fixedIterationsBodyBound_zero_le_succ
    (iterations : Nat) :
    expTwoMulFixedReloadIterStepBound +
        max (expTwoMulFixedIterationsBodyBound iterations) 0 ≤
      expTwoMulFixedIterationsBodyBound (iterations + 1) := by
  rw [Nat.max_eq_left (Nat.zero_le _)]
  exact
    expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations


-- @@ L179-184 verbatim
theorem expTwoMulIterationsBodyBound_mono {iterations iterations' : Nat}
    (h : iterations ≤ iterations') :
    expTwoMulIterationsBodyBound iterations ≤
      expTwoMulIterationsBodyBound iterations' := by
  unfold expTwoMulIterationsBodyBound
  exact Nat.mul_le_mul_right expTwoMulNamedIterStepBound h


-- @@ L186-191 verbatim
theorem expTwoMulFixedIterationsBodyBound_mono {iterations iterations' : Nat}
    (h : iterations ≤ iterations') :
    expTwoMulFixedIterationsBodyBound iterations ≤
      expTwoMulFixedIterationsBodyBound iterations' := by
  unfold expTwoMulFixedIterationsBodyBound
  exact Nat.mul_le_mul_right expTwoMulFixedReloadIterStepBound h


-- @@ L193-196 verbatim
theorem expTwoMulFullLoopBodyBound_eq :
    expTwoMulFullLoopBodyBound = 48384 := by
  norm_num [expTwoMulFullLoopBodyBound, expTwoMulIterationsBodyBound,
    expTwoMulNamedIterStepBound_eq]


-- @@ L198-201 verbatim
theorem expTwoMulFixedFullLoopBodyBound_eq :
    expTwoMulFixedFullLoopBodyBound = 49408 := by
  norm_num [expTwoMulFixedFullLoopBodyBound, expTwoMulFixedIterationsBodyBound,
    expTwoMulFixedReloadIterStepBound_eq]


-- @@ L203-206 verbatim
theorem expTwoMulFullLoopBodyTailBound_eq :
    expTwoMulFullLoopBodyTailBound = 48195 := by
  norm_num [expTwoMulFullLoopBodyTailBound, expTwoMulIterationsBodyBound,
    expTwoMulNamedIterStepBound_eq]


-- @@ L208-211 verbatim
theorem expTwoMulFixedFullLoopBodyTailBound_eq :
    expTwoMulFixedFullLoopBodyTailBound = 49215 := by
  norm_num [expTwoMulFixedFullLoopBodyTailBound,
    expTwoMulFixedIterationsBodyBound, expTwoMulFixedReloadIterStepBound_eq]


-- @@ L213-218 verbatim
/-- Peel the first named iteration from the 256-iteration body bound. -/
theorem expTwoMulFullLoopBodyBound_eq_iter_plus_tail :
    expTwoMulFullLoopBodyBound =
      expTwoMulNamedIterStepBound + expTwoMulFullLoopBodyTailBound := by
  norm_num [expTwoMulFullLoopBodyBound, expTwoMulFullLoopBodyTailBound,
    expTwoMulNamedIterStepBound_eq]


-- @@ L220-227 verbatim
/-- Peel the first fixed-x19 iteration from the conservative 256-iteration
    body bound. -/
theorem expTwoMulFixedFullLoopBodyBound_eq_iter_plus_tail :
    expTwoMulFixedFullLoopBodyBound =
      expTwoMulFixedReloadIterStepBound +
        expTwoMulFixedFullLoopBodyTailBound := by
  norm_num [expTwoMulFixedFullLoopBodyBound,
    expTwoMulFixedFullLoopBodyTailBound, expTwoMulFixedReloadIterStepBound_eq]


-- @@ L229-234 verbatim
/-- View the 256-iteration full-body bound as one peeled iteration followed by
    the 255-iteration tail. -/
theorem expTwoMulFullLoopBodyBound_eq_tail_succ :
    expTwoMulFullLoopBodyBound = expTwoMulIterationsBodyBound (255 + 1) := by
  rw [expTwoMulFullLoopBodyBound_eq_iter_plus_tail,
    expTwoMulIterationsBodyBound_succ]


-- @@ L236-242 verbatim
/-- View the conservative fixed-x19 256-iteration full-body bound as one
    peeled iteration followed by the 255-iteration tail. -/
theorem expTwoMulFixedFullLoopBodyBound_eq_tail_succ :
    expTwoMulFixedFullLoopBodyBound =
      expTwoMulFixedIterationsBodyBound (255 + 1) := by
  rw [expTwoMulFixedFullLoopBodyBound_eq_iter_plus_tail,
    expTwoMulFixedIterationsBodyBound_succ]


-- @@ L244-249 verbatim
/-- The peeled named iteration plus the 255-iteration tail fits in the
    256-iteration full-body budget. -/
theorem expTwoMulNamedIterStepBound_add_fullTail_le_full :
    expTwoMulNamedIterStepBound + expTwoMulFullLoopBodyTailBound ≤
      expTwoMulFullLoopBodyBound := by
  rw [← expTwoMulFullLoopBodyBound_eq_iter_plus_tail]


-- @@ L251-257 verbatim
/-- The peeled fixed-x19 iteration plus the 255-iteration tail fits in the
    conservative 256-iteration full-body budget. -/
theorem expTwoMulFixedReloadIterStepBound_add_fullTail_le_full :
    expTwoMulFixedReloadIterStepBound +
        expTwoMulFixedFullLoopBodyTailBound ≤
      expTwoMulFixedFullLoopBodyBound := by
  rw [← expTwoMulFixedFullLoopBodyBound_eq_iter_plus_tail]


-- @@ L259-266 verbatim
/-- Same budget fact with the duplicated tail bound shape produced by the
    continuation-composition rule. -/
theorem expTwoMulNamedIterStepBound_add_max_fullTail_le_full :
    expTwoMulNamedIterStepBound +
        max expTwoMulFullLoopBodyTailBound expTwoMulFullLoopBodyTailBound ≤
      expTwoMulFullLoopBodyBound := by
  rw [Nat.max_self]
  exact expTwoMulNamedIterStepBound_add_fullTail_le_full


-- @@ L268-276 verbatim
/-- Fixed-x19 version of the duplicated-tail budget fact produced by the
    continuation-composition rule. -/
theorem expTwoMulFixedReloadIterStepBound_add_max_fullTail_le_full :
    expTwoMulFixedReloadIterStepBound +
        max expTwoMulFixedFullLoopBodyTailBound
          expTwoMulFixedFullLoopBodyTailBound ≤
      expTwoMulFixedFullLoopBodyBound := by
  rw [Nat.max_self]
  exact expTwoMulFixedReloadIterStepBound_add_fullTail_le_full


-- @@ L278-281 verbatim
theorem expTwoMulFullLoopBoundaryBound_eq :
    expTwoMulFullLoopBoundaryBound = 48401 := by
  rw [expTwoMulFullLoopBoundaryBound, expTwoMulBoundaryLoopBound_eq,
    expTwoMulFullLoopBodyBound_eq]


-- @@ L283-283 verbatim
end EvmAsm.Evm64.Exp.Compose
