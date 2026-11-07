/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFramedLiveStackPost

  Framed live-stack post surface for the verified fixed-headroom EXP loop.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedHeadroomFullLoop


-- @@ L11-11 verbatim
@[expose] public section


-- @@ L13-13 verbatim
namespace EvmAsm.Evm64.Exp.Compose


-- @@ L15-15 verbatim
open EvmAsm.Rv64


-- @@ L17-26 verbatim
@[irreducible]
def expHeadroomFinalOwnedBaseFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordIs sp (EvmWord.exp baseWord exponentWord) **
     evmWordOwn evmSp) **
    expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
      (EvmWord.exp baseWord exponentWord)


-- @@ L28-39 verbatim
theorem expHeadroomFinalOwnedBaseFrame_unfold
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordIs sp (EvmWord.exp baseWord exponentWord) **
         evmWordOwn evmSp) **
        expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
          (EvmWord.exp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedBaseFrame
  rfl


-- @@ L41-45 verbatim
theorem expHeadroomFinalOwnedBaseFrame_pcFree
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    (expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord).pcFree := by
  rw [expHeadroomFinalOwnedBaseFrame_unfold]
  pcFree


-- @@ L47-51 verbatim
instance pcFreeInst_expHeadroomFinalOwnedBaseFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) :=
  ⟨expHeadroomFinalOwnedBaseFrame_pcFree⟩


-- @@ L53-59 verbatim
@[irreducible]
def expHeadroomFinalFramedLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) ps


-- @@ L61-69 verbatim
theorem expHeadroomFinalFramedLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x12 ↦ᵣ (evmSp + 32)) **
          evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord) ps) := by
  delta expHeadroomFinalFramedLiveStackPost
  rfl


-- @@ L71-80 verbatim
theorem expHeadroomFinalFramedLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalFramedLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hVisible : (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hVisible expHeadroomFinalOwnedBaseFrame_pcFree) ps h_post


-- @@ L82-86 verbatim
instance pcFreeInst_expHeadroomFinalFramedLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalFramedLiveStackPost_pcFree⟩


-- @@ L88-97 verbatim
@[irreducible]
def expHeadroomFinalOwnedScratchFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordOwn sp **
     evmWordOwn evmSp) **
    expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
      (EvmWord.exp baseWord exponentWord)


-- @@ L99-110 verbatim
theorem expHeadroomFinalOwnedScratchFrame_unfold
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordOwn sp **
         evmWordOwn evmSp) **
        expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
          (EvmWord.exp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedScratchFrame
  rfl


-- @@ L112-116 verbatim
theorem expHeadroomFinalOwnedScratchFrame_pcFree
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} :
    (expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord).pcFree := by
  rw [expHeadroomFinalOwnedScratchFrame_unfold]
  pcFree


-- @@ L118-122 verbatim
instance pcFreeInst_expHeadroomFinalOwnedScratchFrame
    (sp evmSp : Word) (baseWord exponentWord scratchWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) :=
  ⟨expHeadroomFinalOwnedScratchFrame_pcFree⟩


-- @@ L124-130 verbatim
@[irreducible]
def expHeadroomFinalOwnedScratchLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  fun ps => ∃ (scratchWord : EvmWord),
    (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
      expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) ps


-- @@ L132-140 verbatim
theorem expHeadroomFinalOwnedScratchLiveStackPost_unfold
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest =
      (fun ps => ∃ (scratchWord : EvmWord),
        (((.x12 ↦ᵣ (evmSp + 32)) **
          evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
          expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord) ps) := by
  delta expHeadroomFinalOwnedScratchLiveStackPost
  rfl


-- @@ L142-151 verbatim
theorem expHeadroomFinalOwnedScratchLiveStackPost_pcFree
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  intro ps h_post
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold] at h_post
  obtain ⟨scratchWord, h_post⟩ := h_post
  have hVisible : (((.x12 ↦ᵣ (evmSp + 32)) **
      evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)).pcFree) := by
    pcFree
  exact (pcFree_sepConj hVisible expHeadroomFinalOwnedScratchFrame_pcFree) ps h_post


-- @@ L153-157 verbatim
instance pcFreeInst_expHeadroomFinalOwnedScratchLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalOwnedScratchLiveStackPost_pcFree⟩


-- @@ L159-167 verbatim
@[irreducible]
def expHeadroomFinalOwnedLoopExtraFrame
    (evmSp : Word) : Assertion :=
  (evmWordOwn (evmSp + signExtend12 ((-128) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-96) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-64) : BitVec 12)) **
    evmWordOwn (evmSp + signExtend12 ((-32) : BitVec 12))) **
    (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
     regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)


-- @@ L169-179 verbatim
theorem expHeadroomFinalOwnedLoopExtraFrame_unfold
    (evmSp : Word) :
    expHeadroomFinalOwnedLoopExtraFrame evmSp =
      ((evmWordOwn (evmSp + signExtend12 ((-128) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-96) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-64) : BitVec 12)) **
        evmWordOwn (evmSp + signExtend12 ((-32) : BitVec 12))) **
        (regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
         regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11)) := by
  delta expHeadroomFinalOwnedLoopExtraFrame
  rfl


-- @@ L181-185 verbatim
theorem expHeadroomFinalOwnedLoopExtraFrame_pcFree
    (evmSp : Word) :
    (expHeadroomFinalOwnedLoopExtraFrame evmSp).pcFree := by
  rw [expHeadroomFinalOwnedLoopExtraFrame_unfold]
  pcFree


-- @@ L187-190 verbatim
instance pcFreeInst_expHeadroomFinalOwnedLoopExtraFrame
    (evmSp : Word) :
    Assertion.PCFree (expHeadroomFinalOwnedLoopExtraFrame evmSp) :=
  ⟨expHeadroomFinalOwnedLoopExtraFrame_pcFree evmSp⟩


-- @@ L192-200 verbatim
@[irreducible]
def expHeadroomFinalOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) : Assertion :=
  ((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordOwn sp **
     evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp


-- @@ L202-212 verbatim
theorem expHeadroomFinalOwnedLeftoverFrame_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord =
      (((.x9 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordOwn sp **
         evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalOwnedLeftoverFrame
  rfl


-- @@ L214-218 verbatim
theorem expHeadroomFinalOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    (expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord).pcFree := by
  rw [expHeadroomFinalOwnedLeftoverFrame_unfold]
  pcFree


-- @@ L220-224 verbatim
instance pcFreeInst_expHeadroomFinalOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord) :=
  ⟨expHeadroomFinalOwnedLeftoverFrame_pcFree sp evmSp baseWord exponentWord⟩


-- @@ L226-232 verbatim
@[irreducible]
def expHeadroomFinalOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord)


-- @@ L234-241 verbatim
theorem expHeadroomFinalOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord)) := by
  delta expHeadroomFinalOwnedLeftoverLiveStackPost
  rfl


-- @@ L243-247 verbatim
theorem expHeadroomFinalOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalOwnedLeftoverLiveStackPost_unfold]
  pcFree


-- @@ L249-253 verbatim
instance pcFreeInst_expHeadroomFinalOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩


-- @@ L255-262 verbatim
@[irreducible]
def expHeadroomFinalCounterOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) : Assertion :=
  (regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) **
     (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
     evmWordOwn sp ** evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp


-- @@ L264-273 verbatim
theorem expHeadroomFinalCounterOwnedLeftoverFrame_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord =
      ((regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) **
         (.x5 ↦ᵣ ((EvmWord.exp baseWord exponentWord).getLimbN 3)) **
         evmWordOwn sp ** evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalCounterOwnedLeftoverFrame
  rfl


-- @@ L275-279 verbatim
theorem expHeadroomFinalCounterOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    (expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord).pcFree := by
  rw [expHeadroomFinalCounterOwnedLeftoverFrame_unfold]
  pcFree


-- @@ L281-284 verbatim
instance pcFreeInst_expHeadroomFinalCounterOwnedLeftoverFrame
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) :
    Assertion.PCFree (expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord) :=
  ⟨expHeadroomFinalCounterOwnedLeftoverFrame_pcFree sp evmSp baseWord exponentWord⟩


-- @@ L286-292 verbatim
@[irreducible]
def expHeadroomFinalCounterOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord)


-- @@ L294-301 verbatim
theorem expHeadroomFinalCounterOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalCounterOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord)) := by
  delta expHeadroomFinalCounterOwnedLeftoverLiveStackPost
  rfl


-- @@ L303-307 verbatim
theorem expHeadroomFinalCounterOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalCounterOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalCounterOwnedLeftoverLiveStackPost_unfold]
  pcFree


-- @@ L309-313 verbatim
instance pcFreeInst_expHeadroomFinalCounterOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalCounterOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalCounterOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩


-- @@ L315-320 verbatim
@[irreducible]
def expHeadroomFinalScratchRegsOwnedLeftoverFrame
    (sp evmSp : Word) : Assertion :=
  (regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
    ((.x2 ↦ᵣ sp) ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp


-- @@ L322-329 verbatim
theorem expHeadroomFinalScratchRegsOwnedLeftoverFrame_unfold
    (sp evmSp : Word) :
    expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp =
      ((regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
        ((.x2 ↦ᵣ sp) ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalScratchRegsOwnedLeftoverFrame
  rfl


-- @@ L331-335 verbatim
theorem expHeadroomFinalScratchRegsOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) :
    (expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp).pcFree := by
  rw [expHeadroomFinalScratchRegsOwnedLeftoverFrame_unfold]
  pcFree


-- @@ L337-340 verbatim
instance pcFreeInst_expHeadroomFinalScratchRegsOwnedLeftoverFrame
    (sp evmSp : Word) :
    Assertion.PCFree (expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp) :=
  ⟨expHeadroomFinalScratchRegsOwnedLeftoverFrame_pcFree sp evmSp⟩


-- @@ L342-348 verbatim
@[irreducible]
def expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp)


-- @@ L350-357 verbatim
theorem expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp)) := by
  delta expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost
  rfl


-- @@ L359-363 verbatim
theorem expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_unfold]
  pcFree


-- @@ L365-369 verbatim
instance pcFreeInst_expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩


-- @@ L371-376 verbatim
@[irreducible]
def expHeadroomFinalFrameRegsOwnedLeftoverFrame
    (sp evmSp : Word) : Assertion :=
  (regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
    (regOwn .x2 ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp


-- @@ L378-385 verbatim
theorem expHeadroomFinalFrameRegsOwnedLeftoverFrame_unfold
    (sp evmSp : Word) :
    expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp =
      ((regOwn .x9 ** (.x0 ↦ᵣ (0 : Word))) **
        (regOwn .x2 ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalFrameRegsOwnedLeftoverFrame
  rfl


-- @@ L387-391 verbatim
theorem expHeadroomFinalFrameRegsOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) :
    (expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp).pcFree := by
  rw [expHeadroomFinalFrameRegsOwnedLeftoverFrame_unfold]
  pcFree


-- @@ L393-396 verbatim
instance pcFreeInst_expHeadroomFinalFrameRegsOwnedLeftoverFrame
    (sp evmSp : Word) :
    Assertion.PCFree (expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp) :=
  ⟨expHeadroomFinalFrameRegsOwnedLeftoverFrame_pcFree sp evmSp⟩


-- @@ L398-404 verbatim
@[irreducible]
def expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp)


-- @@ L406-413 verbatim
theorem expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp)) := by
  delta expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost
  rfl


-- @@ L415-419 verbatim
theorem expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_unfold]
  pcFree


-- @@ L421-425 verbatim
instance pcFreeInst_expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩


-- @@ L427-432 verbatim
@[irreducible]
def expHeadroomFinalAllRegsOwnedLeftoverFrame
    (sp evmSp : Word) : Assertion :=
  (regOwn .x9 ** regOwn .x0) **
    (regOwn .x2 ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
    expHeadroomFinalOwnedLoopExtraFrame evmSp


-- @@ L434-441 verbatim
theorem expHeadroomFinalAllRegsOwnedLeftoverFrame_unfold
    (sp evmSp : Word) :
    expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp =
      ((regOwn .x9 ** regOwn .x0) **
        (regOwn .x2 ** regOwn .x5 ** evmWordOwn sp ** evmWordOwn evmSp) **
        expHeadroomFinalOwnedLoopExtraFrame evmSp) := by
  delta expHeadroomFinalAllRegsOwnedLeftoverFrame
  rfl


-- @@ L443-447 verbatim
theorem expHeadroomFinalAllRegsOwnedLeftoverFrame_pcFree
    (sp evmSp : Word) :
    (expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp).pcFree := by
  rw [expHeadroomFinalAllRegsOwnedLeftoverFrame_unfold]
  pcFree


-- @@ L449-452 verbatim
instance pcFreeInst_expHeadroomFinalAllRegsOwnedLeftoverFrame
    (sp evmSp : Word) :
    Assertion.PCFree (expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp) :=
  ⟨expHeadroomFinalAllRegsOwnedLeftoverFrame_pcFree sp evmSp⟩


-- @@ L454-460 verbatim
@[irreducible]
def expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  (((.x12 ↦ᵣ (evmSp + 32)) **
    evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
    expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp)


-- @@ L462-469 verbatim
theorem expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_unfold
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest =
      ((((.x12 ↦ᵣ (evmSp + 32)) **
        evmStackIs (evmSp + 32) (EvmWord.exp baseWord exponentWord :: rest)) **
        expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp)) := by
  delta expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
  rfl


-- @@ L471-475 verbatim
theorem expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_pcFree
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    (expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest).pcFree := by
  rw [expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_unfold]
  pcFree


-- @@ L477-481 verbatim
instance pcFreeInst_expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost
    (sp evmSp : Word) (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest) :=
  ⟨expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_pcFree sp evmSp baseWord exponentWord rest⟩


-- @@ L483-494 verbatim
private theorem expHeadroomFinalOwnedBaseFrame_to_ownedScratchFrame
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord} {ps : PartialState}
    (h : expHeadroomFinalOwnedBaseFrame sp evmSp baseWord exponentWord scratchWord ps) :
    expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord ps := by
  rw [expHeadroomFinalOwnedBaseFrame_unfold] at h
  rw [expHeadroomFinalOwnedScratchFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono
      (sepConj_mono (fun _ h => h)
        (sepConj_mono (fun _ h => h)
          (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h) (fun _ h => h))))
      (fun _ h => h)) _ h


-- @@ L496-506 verbatim
theorem expHeadroomFinalFramedLiveStackPost_to_ownedScratchLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalFramedLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalOwnedBaseFrame_to_ownedScratchFrame h_frame) _ h



-- @@ L509-544 verbatim
private theorem expHeadroomFinalLoopExtraFrame_to_ownedLoopExtraFrame
    {evmSp : Word} {baseWord exponentWord scratchWord resultWord : EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalLoopExtraFrame evmSp baseWord exponentWord scratchWord
        resultWord ps) :
    expHeadroomFinalOwnedLoopExtraFrame evmSp ps := by
  rw [expHeadroomFinalLoopExtraFrame_unfold] at h
  rw [expHeadroomFinalOwnedLoopExtraFrame_unfold]
  rw [evmStackIs_cons, evmStackIs_cons, evmStackIs_cons, evmStackIs_cons,
    evmStackIs_nil] at h
  simp only [sepConj_emp_right'] at h
  rw [show (evmSp + signExtend12 ((-128) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-96) : BitVec 12) from by
        rw [show (signExtend12 ((-128) : BitVec 12) : Word) =
            18446744073709551488 from by decide,
          show (signExtend12 ((-96) : BitVec 12) : Word) =
            18446744073709551520 from by decide]
        bv_omega] at h
  rw [show (evmSp + signExtend12 ((-96) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-64) : BitVec 12) from by
        rw [show (signExtend12 ((-96) : BitVec 12) : Word) =
            18446744073709551520 from by decide,
          EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]
        bv_omega] at h
  rw [show (evmSp + signExtend12 ((-64) : BitVec 12) + 32 : Word) =
      evmSp + signExtend12 ((-32) : BitVec 12) from by
        rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
          EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg32]
        bv_omega] at h
  exact sepConj_mono
    (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
      (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
        (sepConj_mono (fun _ h => evmWordIs_to_evmWordOwn h)
          (fun _ h => evmWordIs_to_evmWordOwn h))))
    (fun _ h_regs => h_regs) _ h


-- @@ L546-557 verbatim
private theorem expHeadroomFinalOwnedScratchFrame_to_ownedLeftoverFrame
    {sp evmSp : Word} {baseWord exponentWord scratchWord : EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalOwnedScratchFrame sp evmSp baseWord exponentWord scratchWord
        ps) :
    expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord ps := by
  rw [expHeadroomFinalOwnedScratchFrame_unfold] at h
  rw [expHeadroomFinalOwnedLeftoverFrame_unfold]
  exact sepConj_mono (fun _ h => h)
    (sepConj_mono (fun _ h => h)
      (fun _ h_frame => expHeadroomFinalLoopExtraFrame_to_ownedLoopExtraFrame h_frame)) _ h


-- @@ L559-571 verbatim
theorem expHeadroomFinalOwnedScratchLiveStackPost_to_ownedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalOwnedScratchLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalOwnedScratchLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalOwnedScratchFrame_to_ownedLeftoverFrame h_frame) _ h



-- @@ L574-582 verbatim
private theorem expHeadroomFinalOwnedLeftoverFrame_to_counterOwnedLeftoverFrame
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {ps : PartialState}
    (h : expHeadroomFinalOwnedLeftoverFrame sp evmSp baseWord exponentWord ps) :
    expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord ps := by
  rw [expHeadroomFinalOwnedLeftoverFrame_unfold] at h
  rw [expHeadroomFinalCounterOwnedLeftoverFrame_unfold]
  exact sepConj_mono
    (sepConj_mono (fun st h => regIs_implies_regOwn .x9 st h) (fun _ h => h))
    (fun _ h => h) _ h


-- @@ L584-595 verbatim
theorem expHeadroomFinalOwnedLeftoverLiveStackPost_to_counterOwnedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalCounterOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalOwnedLeftoverLiveStackPost_unfold] at h
  rw [expHeadroomFinalCounterOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalOwnedLeftoverFrame_to_counterOwnedLeftoverFrame h_frame) _ h



-- @@ L598-607 verbatim
private theorem expHeadroomFinalCounterOwnedLeftoverFrame_to_scratchRegsOwnedLeftoverFrame
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {ps : PartialState}
    (h : expHeadroomFinalCounterOwnedLeftoverFrame sp evmSp baseWord exponentWord ps) :
    expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp ps := by
  rw [expHeadroomFinalCounterOwnedLeftoverFrame_unfold] at h
  rw [expHeadroomFinalScratchRegsOwnedLeftoverFrame_unfold]
  exact sepConj_mono_right
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono_left (fun st h => regIs_implies_regOwn .x5 st h)))) _ h


-- @@ L609-620 verbatim
theorem expHeadroomFinalCounterOwnedLeftoverLiveStackPost_to_scratchRegsOwnedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalCounterOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalCounterOwnedLeftoverLiveStackPost_unfold] at h
  rw [expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalCounterOwnedLeftoverFrame_to_scratchRegsOwnedLeftoverFrame h_frame) _ h



-- @@ L623-630 verbatim
private theorem expHeadroomFinalScratchRegsOwnedLeftoverFrame_to_frameRegsOwnedLeftoverFrame
    {sp evmSp : Word} {ps : PartialState}
    (h : expHeadroomFinalScratchRegsOwnedLeftoverFrame sp evmSp ps) :
    expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp ps := by
  rw [expHeadroomFinalScratchRegsOwnedLeftoverFrame_unfold] at h
  rw [expHeadroomFinalFrameRegsOwnedLeftoverFrame_unfold]
  exact sepConj_mono_right
    (sepConj_mono_left (sepConj_mono_left (fun st h => regIs_implies_regOwn .x2 st h))) _ h


-- @@ L632-643 verbatim
theorem expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_to_frameRegsOwnedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalScratchRegsOwnedLeftoverLiveStackPost_unfold] at h
  rw [expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalScratchRegsOwnedLeftoverFrame_to_frameRegsOwnedLeftoverFrame h_frame) _ h



-- @@ L646-653 verbatim
private theorem expHeadroomFinalFrameRegsOwnedLeftoverFrame_to_allRegsOwnedLeftoverFrame
    {sp evmSp : Word} {ps : PartialState}
    (h : expHeadroomFinalFrameRegsOwnedLeftoverFrame sp evmSp ps) :
    expHeadroomFinalAllRegsOwnedLeftoverFrame sp evmSp ps := by
  rw [expHeadroomFinalFrameRegsOwnedLeftoverFrame_unfold] at h
  rw [expHeadroomFinalAllRegsOwnedLeftoverFrame_unfold]
  exact sepConj_mono_left
    (sepConj_mono_right (fun st h => regIs_implies_regOwn .x0 st h)) _ h


-- @@ L655-666 verbatim
theorem expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_to_allRegsOwnedLeftoverLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h :
      expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps) :
    expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost sp evmSp baseWord exponentWord rest
        ps := by
  rw [expHeadroomFinalFrameRegsOwnedLeftoverLiveStackPost_unfold] at h
  rw [expHeadroomFinalAllRegsOwnedLeftoverLiveStackPost_unfold]
  exact sepConj_mono (fun _ h => h)
    (fun _ h_frame => expHeadroomFinalFrameRegsOwnedLeftoverFrame_to_allRegsOwnedLeftoverFrame h_frame) _ h



-- @@ L669-679 verbatim
theorem expHeadroomFinalCleanOwnedBaseLiveStackPost_to_framedLiveStackPost
    {sp evmSp : Word} {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {ps : PartialState}
    (h : expHeadroomFinalCleanOwnedBaseLiveStackPost sp evmSp baseWord exponentWord rest ps) :
    expHeadroomFinalFramedLiveStackPost sp evmSp baseWord exponentWord rest ps := by
  rw [expHeadroomFinalCleanOwnedBaseLiveStackPost_unfold] at h
  obtain ⟨scratchWord, h⟩ := h
  rw [expHeadroomFinalFramedLiveStackPost_unfold]
  refine ⟨scratchWord, ?_⟩
  rw [expHeadroomFinalOwnedBaseFrame_unfold]
  xperm_hyp h



-- @@ L682-682 verbatim
end EvmAsm.Evm64.Exp.Compose
