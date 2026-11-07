module

public import EvmAsm.Evm64.Exp.TwoMulCondShared


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L9-9 verbatim
open EvmAsm.Rv64


-- @@ L11-17 verbatim
@[irreducible]
def expTwoMulIterBaseFrame
    (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)


-- @@ L19-26 verbatim
theorem expTwoMulIterBaseFrame_unfold {evmSp a0 a1 a2 a3 : Word} :
    expTwoMulIterBaseFrame evmSp a0 a1 a2 a3 =
      (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  delta expTwoMulIterBaseFrame
  rfl


-- @@ L28-32 verbatim
theorem expTwoMulIterBaseFrame_pcFree
    {evmSp a0 a1 a2 a3 : Word} :
    (expTwoMulIterBaseFrame evmSp a0 a1 a2 a3).pcFree := by
  rw [expTwoMulIterBaseFrame_unfold]
  pcFree


-- @@ L34-37 verbatim
@[irreducible]
def expTwoMulIterSkipRest
    (bit sp evmSp base : Word) (squareW : EvmWord) : Assertion :=
  expTwoMulSkipLoopRest bit sp evmSp base squareW


-- @@ L39-55 verbatim
theorem expTwoMulIterSkipRest_unfold
    {bit sp evmSp base : Word} {squareW : EvmWord} :
    expTwoMulIterSkipRest bit sp evmSp base squareW =
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ squareW.getLimbN 3) **
       evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  rw [show expTwoMulIterSkipRest bit sp evmSp base squareW =
        expTwoMulSkipLoopRest bit sp evmSp base squareW by
      delta expTwoMulIterSkipRest
      rfl]
  exact expTwoMulSkipLoopRest_unfold


-- @@ L57-64 verbatim
theorem expTwoMulIterSkipRest_pcFree
    {bit sp evmSp base : Word} {squareW : EvmWord} :
    (expTwoMulIterSkipRest bit sp evmSp base squareW).pcFree := by
  rw [show expTwoMulIterSkipRest bit sp evmSp base squareW =
        expTwoMulSkipLoopRest bit sp evmSp base squareW by
      delta expTwoMulIterSkipRest
      rfl]
  exact expTwoMulSkipLoopRest_pcFree


-- @@ L66-69 verbatim
@[irreducible]
def expTwoMulIterCondRest
    (sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord) : Assertion :=
  expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw


-- @@ L71-89 verbatim
theorem expTwoMulIterCondRest_unfold
    {sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord} :
    expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw =
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  rw [show expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw =
        expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw by
      delta expTwoMulIterCondRest
      rfl]
  exact expCondMulLoopRest_unfold


-- @@ L91-98 verbatim
theorem expTwoMulIterCondRest_pcFree
    {sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord} :
    (expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw).pcFree := by
  rw [show expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw =
        expCondMulLoopRest sp evmSp base a0 a1 a2 a3 rw by
      delta expTwoMulIterCondRest
      rfl]
  exact expCondMulLoopRest_pcFree


-- @@ L100-103 verbatim
@[irreducible]
def expTwoMulIterCondFrame (bit : Word) : Assertion :=
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝


-- @@ L105-110 verbatim
theorem expTwoMulIterCondFrame_unfold {bit : Word} :
    expTwoMulIterCondFrame bit =
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝) := by
  delta expTwoMulIterCondFrame
  rfl


-- @@ L112-115 verbatim
theorem expTwoMulIterCondFrame_pcFree {bit : Word} :
    (expTwoMulIterCondFrame bit).pcFree := by
  rw [expTwoMulIterCondFrame_unfold]
  pcFree


-- @@ L117-123 verbatim
@[irreducible]
def expTwoMulIterCondPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜exitCond⌝) ** expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw) **
  expTwoMulIterCondFrame bit


-- @@ L125-133 verbatim
theorem expTwoMulIterCondPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord}
    {exitCond : Prop} :
    expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw exitCond =
      ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜exitCond⌝) ** expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw) **
       expTwoMulIterCondFrame bit) := by
  delta expTwoMulIterCondPost
  rfl


-- @@ L135-142 verbatim
theorem expTwoMulIterCondPost_pcFree
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord}
    {exitCond : Prop} :
    (expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
      exitCond).pcFree := by
  rw [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
    expTwoMulIterCondFrame_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  pcFree


-- @@ L144-150 verbatim
@[irreducible]
def expTwoMulIterSkipPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (squareW : EvmWord)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜exitCond⌝) ** expTwoMulIterSkipRest bit sp evmSp base squareW) **
  expTwoMulIterBaseFrame evmSp a0 a1 a2 a3


-- @@ L152-160 verbatim
theorem expTwoMulIterSkipPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW : EvmWord}
    {exitCond : Prop} :
    expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW exitCond =
      ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜exitCond⌝) ** expTwoMulIterSkipRest bit sp evmSp base squareW) **
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3) := by
  delta expTwoMulIterSkipPost
  rfl


-- @@ L162-169 verbatim
theorem expTwoMulIterSkipPost_pcFree
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW : EvmWord}
    {exitCond : Prop} :
    (expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW
      exitCond).pcFree := by
  rw [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
    expTwoMulIterBaseFrame_unfold, evmWordIs_sp_unfold, evmWordIs_sp32_unfold]
  pcFree


-- @@ L171-179 verbatim
@[irreducible]
def expTwoMulIterLoopPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word)
    (squareW rw : EvmWord) : Assertion :=
  fun h =>
    expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
      (iterCountNew ≠ 0) h ∨
    expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW
      (iterCountNew ≠ 0) h


-- @@ L181-190 verbatim
theorem expTwoMulIterLoopPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord} :
    expTwoMulIterLoopPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw =
      (fun h =>
        expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
          (iterCountNew ≠ 0) h ∨
        expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW
          (iterCountNew ≠ 0) h) := by
  delta expTwoMulIterLoopPost
  rfl


-- @@ L192-199 verbatim
theorem expTwoMulIterLoopPost_pcFree
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord} :
    (expTwoMulIterLoopPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw).pcFree := by
  rw [expTwoMulIterLoopPost_unfold]
  intro h hp
  rcases hp with hp | hp
  · exact expTwoMulIterCondPost_pcFree h hp
  · exact expTwoMulIterSkipPost_pcFree h hp


-- @@ L201-209 verbatim
@[irreducible]
def expTwoMulIterExitPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word)
    (squareW rw : EvmWord) : Assertion :=
  fun h =>
    expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
      (iterCountNew = 0) h ∨
    expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW
      (iterCountNew = 0) h


-- @@ L211-220 verbatim
theorem expTwoMulIterExitPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord} :
    expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw =
      (fun h =>
        expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
          (iterCountNew = 0) h ∨
        expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW
          (iterCountNew = 0) h) := by
  delta expTwoMulIterExitPost
  rfl


-- @@ L222-229 verbatim
theorem expTwoMulIterExitPost_pcFree
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord} :
    (expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw).pcFree := by
  rw [expTwoMulIterExitPost_unfold]
  intro h hp
  rcases hp with hp | hp
  · exact expTwoMulIterCondPost_pcFree h hp
  · exact expTwoMulIterSkipPost_pcFree h hp


-- @@ L231-251 verbatim
@[irreducible]
def expTwoMulIterPre
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word) : Assertion :=
  (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
    regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
    (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
   expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)


-- @@ L253-276 verbatim
theorem expTwoMulIterPre_unfold
    {e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word} :
    expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 =
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3) := by
  delta expTwoMulIterPre
  rfl


-- @@ L278-284 verbatim
theorem expTwoMulIterPre_pcFree
    {e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word} :
    (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3).pcFree := by
  rw [expTwoMulIterPre_unfold, expTwoMulIterBaseFrame_unfold]
  pcFree


-- @@ L286-286 verbatim
end EvmAsm.Evm64.Exp.Compose
