/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part01A


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 01, continuation 02 -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open StateTransition (EvalsToInTime)


-- @@ L19-19 verbatim
namespace GapCVP


-- @@ L21-21 verbatim
open GapCVP.TraceGolf (oneStep rebound)


-- @@ L23-23 verbatim
namespace CLCompleteVerifierSimulation


-- @@ L25-25 verbatim
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates


-- @@ L27-27 verbatim
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows


-- @@ L29-29 verbatim
open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLExactVerifierTransition


-- @@ L31-31 verbatim
open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter


-- @@ L33-35 verbatim
/-- GapCVP reduction support. -/
abbrev PairedInputBlock (tm : Turing.FinTM2) :=
  Fin (blockSize tm) → PairedInputTag


-- @@ L37-39 verbatim
/-- GapCVP reduction support. -/
abbrev PhaseMaskBlock (tm : Turing.FinTM2) :=
  Fin (blockSize tm) → Bool


-- @@ L41-50 verbatim
/-- GapCVP reduction support. -/
def pairedInputBlockAt (tm : Turing.FinTM2)
    (width : ℕ) (x certificate : List Bool)
    (position : Fin (width + 1)) : PairedInputBlock tm :=
  fun offset =>
    if position.val * blockSize tm + offset.val < width + 1 then
      pairedInputTagAt x certificate
        (position.val * blockSize tm + offset.val)
    else
      .blank


-- @@ L52-57 verbatim
/-- GapCVP reduction support. -/
def phaseRangeBlockAt (tm : Turing.FinTM2)
    (width : ℕ)
    (position : Fin (width + 1)) : PhaseMaskBlock tm :=
  fun offset =>
    decide (position.val * blockSize tm + offset.val < width + 1)


-- @@ L59-70 verbatim
/-- GapCVP reduction support. -/
def phaseBudgetBlockAt
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (position : Fin (rowWidth bound machine x + 1)) :
    PhaseMaskBlock machine.tm :=
  fun offset =>
    decide
      (position.val * blockSize machine.tm + offset.val <
        x.length + bound.eval x.length)


-- @@ L72-91 verbatim
/-- GapCVP reduction support. -/
def initialPairedAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (tag : PairedInputTag) : CellAtom machine.tm := by
  classical
  exact match tag with
    | .bit bit =>
        if stack = machine.tm.k₀ then
          canonicalCellAtom machine machine.tm.k₀
            (machine.inputAlphabet.invFun bit)
            (by
              simp only [SupportedStackValue, decide_eq_true_eq]
              exact ⟨some (.inl bit),
                cellAtomValue_input machine bit⟩)
        else
          none
    | .marker => none
    | .blank => none


-- @@ L93-109 verbatim
/-- GapCVP reduction support. -/
def initializedPhaseBlock
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (old : BlockCell machine.tm)
    (payload : PairedInputBlock machine.tm)
    (range : PhaseMaskBlock machine.tm) : BlockCell machine.tm :=
  fun offset =>
    if range offset then
      ((old offset).1,
        some
          (configurationControl machine.tm
            (Turing.initList machine.tm [])),
        fun stack => initialPairedAtom machine stack (payload offset),
        (Turing.initList machine.tm []).l.isSome)
    else
      blankCell machine.tm


-- @@ L111-128 verbatim
/-- GapCVP reduction support. -/
structure CompletePhaseCell (tm : Turing.FinTM2) where
  /-- GapCVP reduction support. -/
  mode : PhaseTag
  /-- GapCVP reduction support. -/
  script : ScriptBlockCell tm
  /-- GapCVP reduction support. -/
  payload : PairedInputBlock tm
  /-- GapCVP reduction support. -/
  payloadHead : PairedInputBlock tm
  /-- GapCVP reduction support. -/
  range : PhaseMaskBlock tm
  /-- GapCVP reduction support. -/
  rangeHead : PhaseMaskBlock tm
  /-- GapCVP reduction support. -/
  budget : PhaseMaskBlock tm
  /-- GapCVP reduction support. -/
  guessBit : Bool


-- @@ L130-156 verbatim
noncomputable instance instFintypeCompletePhaseCell
    (tm : Turing.FinTM2) : Fintype (CompletePhaseCell tm) := by
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  exact Fintype.ofEquiv
    (PhaseTag × ScriptBlockCell tm ×
      PairedInputBlock tm × PairedInputBlock tm ×
      PhaseMaskBlock tm × PhaseMaskBlock tm ×
      PhaseMaskBlock tm × Bool)
    { toFun := fun value =>
        ⟨value.1, value.2.1, value.2.2.1,
          value.2.2.2.1, value.2.2.2.2.1,
          value.2.2.2.2.2.1, value.2.2.2.2.2.2.1,
          value.2.2.2.2.2.2.2⟩
      invFun := fun value =>
        (value.mode, value.script, value.payload,
          value.payloadHead, value.range, value.rangeHead,
          value.budget, value.guessBit)
      left_inv := by
        rintro ⟨mode, script, payload, payloadHead,
          range, rangeHead, budget, guessBit⟩
        rfl
      right_inv := by
        rintro ⟨mode, script, payload, payloadHead,
          range, rangeHead, budget, guessBit⟩
        rfl }


-- @@ L158-161 verbatim
/-- GapCVP reduction support. -/
abbrev CompletePhaseWindow (tm : Turing.FinTM2) :=
  CompletePhaseCell tm × CompletePhaseCell tm ×
    CompletePhaseCell tm × CompletePhaseCell tm


-- @@ L163-166 verbatim
/-- GapCVP reduction support. -/
def completeMachineBlock (tm : Turing.FinTM2)
    (cell : CompletePhaseCell tm) : BlockCell tm :=
  cell.script.1.1


-- @@ L168-171 verbatim
/-- GapCVP reduction support. -/
def completeMachineHead (tm : Turing.FinTM2)
    (cell : CompletePhaseCell tm) : BlockCell tm :=
  cell.script.1.2


-- @@ L173-176 verbatim
/-- GapCVP reduction support. -/
def completeIsFirstBlock (tm : Turing.FinTM2)
    (cell : CompletePhaseCell tm) : Bool :=
  cell.script.2.2


-- @@ L178-182 verbatim
/-- GapCVP reduction support. -/
def lastPhaseOffset (tm : Turing.FinTM2) : Fin (blockSize tm) :=
  ⟨blockSize tm - 1, by
    have hpositive := blockSize_pos tm
    omega⟩


-- @@ L184-195 verbatim
/-- GapCVP reduction support. -/
def phaseLeftOffset {α : Type}
    (tm : Turing.FinTM2)
    (first : Bool)
    (left center : Fin (blockSize tm) → α)
    (offset : Fin (blockSize tm)) : α :=
  if hzero : offset.val = 0 then
    if first then center offset else left (lastPhaseOffset tm)
  else
    center ⟨offset.val - 1, by
      have hlt := offset.isLt
      omega⟩


-- @@ L197-205 verbatim
/-- GapCVP reduction support. -/
def phaseRightOffset {α : Type}
    (tm : Turing.FinTM2)
    (center right : Fin (blockSize tm) → α)
    (offset : Fin (blockSize tm)) : α :=
  if hnext : offset.val + 1 < blockSize tm then
    center ⟨offset.val + 1, hnext⟩
  else
    right ⟨0, blockSize_pos tm⟩


-- @@ L207-226 verbatim
/-- GapCVP reduction support. -/
def completeWitnessWindow
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm)
    (offset : Fin (blockSize tm)) : GuessPhaseWindow :=
  (phaseLeftOffset tm
      (completeIsFirstBlock tm window.2.1)
      (fun position =>
        (completeMachineBlock tm window.1 position).1)
      (fun position =>
        (completeMachineBlock tm window.2.1 position).1)
      offset,
    (completeMachineBlock tm window.2.1 offset).1,
    phaseRightOffset tm
      (fun position =>
        (completeMachineBlock tm window.2.1 position).1)
      (fun position =>
        (completeMachineBlock tm window.2.2.1 position).1)
      offset,
    (completeMachineBlock tm window.2.2.2 offset).1)


-- @@ L228-240 verbatim
/-- GapCVP reduction support. -/
def completePayloadWindow
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm)
    (offset : Fin (blockSize tm)) :
    PairedInputTag × PairedInputTag × PairedInputTag × PairedInputTag :=
  (phaseLeftOffset tm
      (completeIsFirstBlock tm window.2.1)
      window.1.payload window.2.1.payload offset,
    window.2.1.payload offset,
    phaseRightOffset tm
      window.2.1.payload window.2.2.1.payload offset,
    window.2.2.2.payload offset)


-- @@ L242-258 verbatim
/-- GapCVP reduction support. -/
noncomputable def PairedInputGuessAllowed
    (bit : Bool)
    (window :
      PairedInputTag × PairedInputTag ×
        PairedInputTag × PairedInputTag) : Bool :=
  @decide (
  (window.2.1 = .marker ∧
    window.2.2.1 = .blank ∧
      window.2.2.2 = .bit (.inr bit)) ∨
  (window.2.1 ≠ .marker ∧
    window.1 = .marker ∧
      window.2.2.2 = .marker) ∨
  (window.2.1 ≠ .marker ∧
    window.1 ≠ .marker ∧
      window.2.2.2 = window.2.1)
  ) (Classical.propDecidable _)

-- @@ L259-268 verbatim
/-- GapCVP reduction support. -/
noncomputable def BroadcastWitnessGuessAllowed
    (bit : Bool)
    (window : GuessPhaseWindow) : Bool :=
  @decide (
  GuessPhaseAllowed window ∧
    (window.2.1 = .accepting →
      window.2.2.2 =
        if bit then PhaseTag.verifying else PhaseTag.guessing)
  ) (Classical.propDecidable _)

-- @@ L269-282 verbatim
/-- GapCVP reduction support. -/
noncomputable def CompletePhaseCoherent
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm) : Bool :=
  @decide (
  window.1.mode = window.2.1.mode ∧
    window.2.2.1.mode = window.2.1.mode ∧
    window.1.guessBit = window.2.1.guessBit ∧
    window.2.2.1.guessBit = window.2.1.guessBit ∧
    window.1.payloadHead = window.2.1.payloadHead ∧
    window.2.2.1.payloadHead = window.2.1.payloadHead ∧
    window.1.rangeHead = window.2.1.rangeHead ∧
    window.2.2.1.rangeHead = window.2.1.rangeHead
  ) (Classical.propDecidable _)

-- @@ L283-288 verbatim
/-- GapCVP reduction support. -/
def completeScriptWindow
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm) : ScriptBlockWindow tm :=
  (window.1.script, window.2.1.script,
    window.2.2.1.script, window.2.2.2.script)


-- @@ L290-302 verbatim
/-- GapCVP reduction support. -/
noncomputable def CompleteStaticTracksPreserved
    (tm : Turing.FinTM2)
    (window : CompletePhaseWindow tm) : Bool :=
  @decide (
  window.2.2.2.payload = window.2.1.payload ∧
    window.2.2.2.payloadHead = window.2.1.payloadHead ∧
    window.2.2.2.range = window.2.1.range ∧
    window.2.2.2.rangeHead = window.2.1.rangeHead ∧
    window.2.2.2.budget = window.2.1.budget ∧
    completeIsFirstBlock tm window.2.2.2 =
      completeIsFirstBlock tm window.2.1
  ) (Classical.propDecidable _)

-- @@ L303-316 verbatim
/-- GapCVP reduction support. -/
def canonicalGuessingScriptRow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (hint : FiniteVerifierHint machine.tm) :
    ScriptBlockRow machine.tm width :=
  fun position =>
    ((packRow machine.tm width
        (guessingRow machine.tm width certificate) position,
      packRow machine.tm width
        (guessingRow machine.tm width certificate) 0),
      hint, decide (position.val = 0))


-- @@ L318-339 verbatim
/-- GapCVP reduction support. -/
def initialPhaseCell
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (position : Fin (rowWidth bound machine x + 1)) :
    CompletePhaseCell machine.tm where
  mode := .guessing
  script := canonicalGuessingScriptRow machine
    (rowWidth bound machine x) []
    (defaultVerifierHint machine.tm) position
  payload := pairedInputBlockAt machine.tm
    (rowWidth bound machine x) x [] position
  payloadHead := pairedInputBlockAt machine.tm
    (rowWidth bound machine x) x [] 0
  range := phaseRangeBlockAt machine.tm
    (rowWidth bound machine x) position
  rangeHead := phaseRangeBlockAt machine.tm
    (rowWidth bound machine x) 0
  budget := phaseBudgetBlockAt bound machine x position
  guessBit := false


-- @@ L341-351 verbatim
/-- GapCVP reduction support. -/
def acceptingPhaseCell
    (tm : Turing.FinTM2) : CompletePhaseCell tm where
  mode := .accepting
  script := defaultScriptBlockCell tm
  payload := fun _ => .blank
  payloadHead := fun _ => .blank
  range := fun _ => false
  rangeHead := fun _ => false
  budget := fun _ => false
  guessBit := false


-- @@ L353-375 verbatim
/-- GapCVP reduction support. -/
noncomputable def AcceptingPhaseBlock
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (cell : CompletePhaseCell machine.tm) : Bool :=
  @decide (
  machineControlOfBlock machine.tm
      (completeMachineHead machine.tm cell) =
    some
      ((Turing.haltList machine.tm
          (verifierOutput machine true)).l,
        (Turing.haltList machine.tm
          (verifierOutput machine true)).var) ∧
    ∀ (offset : Fin (blockSize machine.tm))
      (stack : machine.tm.K),
      cellAtomValue machine stack
        ((completeMachineBlock machine.tm cell offset).2.2.1 stack) =
        if completeIsFirstBlock machine.tm cell ∧ offset.val = 0 then
          ((Turing.haltList machine.tm
            (verifierOutput machine true)).stk stack)[0]?
        else
          none
  ) (Classical.propDecidable _)

-- @@ L376-392 verbatim
/-- GapCVP reduction support. -/
noncomputable def CompleteInitializationAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  window.2.2.2.mode = .verifying ∧
    CompleteStaticTracksPreserved machine.tm window ∧
    completeMachineBlock machine.tm window.2.2.2 =
      initializedPhaseBlock machine
        (completeMachineBlock machine.tm window.2.1)
        window.2.1.payload window.2.1.range ∧
    completeMachineHead machine.tm window.2.2.2 =
      initializedPhaseBlock machine
        (completeMachineHead machine.tm window.2.1)
        window.2.1.payloadHead window.2.1.rangeHead
  ) (Classical.propDecidable _)

-- @@ L393-403 verbatim
/-- GapCVP reduction support. -/
noncomputable def CompleteVerificationAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  window.2.2.2.mode = .verifying ∧
    CompleteStaticTracksPreserved machine.tm window ∧
    scriptBlockAllowed machine
      (completeScriptWindow machine.tm window) = true
  ) (Classical.propDecidable _)

-- @@ L404-412 verbatim
/-- GapCVP reduction support. -/
noncomputable def CompleteAcceptanceAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : CompletePhaseWindow machine.tm) : Bool :=
  @decide (
  window.2.2.2 = acceptingPhaseCell machine.tm ∧
    AcceptingPhaseBlock machine window.2.1
  ) (Classical.propDecidable _)

-- @@ L413-415 verbatim
private def defaultCompletePhaseCell
    (tm : Turing.FinTM2) : CompletePhaseCell tm :=
  acceptingPhaseCell tm


-- @@ L417-419 verbatim
/-- GapCVP reduction support. -/
def completePhaseSymbolCount (tm : Turing.FinTM2) : ℕ :=
  Fintype.card (CompletePhaseCell tm) - 1


-- @@ L421-428 verbatim
theorem completePhaseSymbolCount_card
    (tm : Turing.FinTM2) :
    completePhaseSymbolCount tm + 1 =
      Fintype.card (CompletePhaseCell tm) := by
  have hpositive : 0 < Fintype.card (CompletePhaseCell tm) :=
    Fintype.card_pos_iff.mpr ⟨defaultCompletePhaseCell tm⟩
  unfold completePhaseSymbolCount
  omega


-- @@ L430-436 verbatim
/-- GapCVP reduction support. -/
def completePhaseSymbolEquiv
    (tm : Turing.FinTM2) :
    CompletePhaseCell tm ≃ Symbol (completePhaseSymbolCount tm) :=
  (Fintype.equivFin (CompletePhaseCell tm)).trans
    (Equiv.cast (congrArg Fin
      (completePhaseSymbolCount_card tm).symm))


-- @@ L438-438 verbatim
end CLCompleteVerifierSimulation



-- @@ L441-441 verbatim
end GapCVP


-- @@ L443-443 verbatim
end
