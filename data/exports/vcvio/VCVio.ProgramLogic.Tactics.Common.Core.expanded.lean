/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Match.MatcherApp
public meta import Lean.Meta.Sym.Pattern
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.ProgramLogic.NotationCore


-- @@ L15-19 verbatim
/-!
# VCGen Planner Core

Shared planning infrastructure for the unary and relational VCGen tactics.
-/


-- @@ L21-21 verbatim
public meta section


-- @@ L23-23 verbatim
open Lean Elab Tactic Meta


-- @@ L25-25 verbatim
namespace OracleComp.ProgramLogic


-- @@ L27-30 verbatim
register_option vcvio.vcgen.maxPasses : Nat := {
  defValue := 64
  descr := "Maximum number of exhaustive vcgen/rvcgen passes before requiring manual stepping."
}


-- @@ L32-35 verbatim
register_option vcvio.vcgen.traceSteps : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for chosen vcgen/rvcgen planned steps."
}


-- @@ L37-40 verbatim
register_option vcvio.vcgen.time : Bool := {
  defValue := false
  descr := "Emit cumulative timing for internal vcgen/rvcgen planner phases."
}


-- @@ L42-45 verbatim
register_option vcvio.vcgen.traceCachedRules : Bool := {
  defValue := false
  descr := "Emit opt-in trace messages for cached `@[vcspec]` backward-rule hits and misses."
}


-- @@ L47-60 verbatim
structure VCGenTimingData where
  previewNs : UInt64 := 0
  structuralNs : UInt64 := 0
  wpStepNs : UInt64 := 0
  probPlannerNs : UInt64 := 0
  localHintNs : UInt64 := 0
  registeredNs : UInt64 := 0
  cachedRuleBuildNs : UInt64 := 0
  cachedRuleHits : Nat := 0
  cachedRuleMisses : Nat := 0
  closeNs : UInt64 := 0
  passNs : UInt64 := 0
  finishNs : UInt64 := 0
  deriving Inhabited


-- @@ L62-62 verbatim
initialize vcGenTimingRef : IO.Ref VCGenTimingData ← IO.mkRef {}


-- @@ L64-69 verbatim
def timeNs {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m]
    (k : m α) : m (α × UInt64) := do
  let start ← IO.monoNanosNow
  let a ← k
  let stop ← IO.monoNanosNow
  return (a, (stop - start).toUInt64)


-- @@ L71-72 verbatim
private def addVCGenTiming (f : VCGenTimingData → VCGenTimingData) : BaseIO Unit :=
  vcGenTimingRef.modify f


-- @@ L74-75 verbatim
private def addPreviewTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with previewNs := d.previewNs + ns }


-- @@ L77-78 verbatim
private def addStructuralTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with structuralNs := d.structuralNs + ns }


-- @@ L80-81 verbatim
private def addWpStepTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with wpStepNs := d.wpStepNs + ns }


-- @@ L83-84 verbatim
private def addProbPlannerTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with probPlannerNs := d.probPlannerNs + ns }


-- @@ L86-87 verbatim
private def addLocalHintTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with localHintNs := d.localHintNs + ns }


-- @@ L89-90 verbatim
private def addRegisteredTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with registeredNs := d.registeredNs + ns }


-- @@ L92-93 verbatim
def addCachedRuleBuildTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleBuildNs := d.cachedRuleBuildNs + ns }


-- @@ L95-96 verbatim
def addCachedRuleHit : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleHits := d.cachedRuleHits + 1 }


-- @@ L98-99 verbatim
def addCachedRuleMiss : BaseIO Unit :=
  addVCGenTiming fun d => { d with cachedRuleMisses := d.cachedRuleMisses + 1 }


-- @@ L101-102 verbatim
private def addCloseTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with closeNs := d.closeNs + ns }


-- @@ L104-105 verbatim
private def addPassTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with passNs := d.passNs + ns }


-- @@ L107-108 verbatim
private def addFinishTime (ns : UInt64) : BaseIO Unit :=
  addVCGenTiming fun d => { d with finishNs := d.finishNs + ns }


-- @@ L110-116 verbatim
def withVCGenTiming {α : Type} (add : UInt64 → BaseIO Unit) (k : TacticM α) : TacticM α := do
  if vcvio.vcgen.time.get (← getOptions) then
    let (a, ns) ← timeNs k
    add ns
    return a
  else
    k


-- @@ L118-119 verbatim
def withVCGenPreviewTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPreviewTime k


-- @@ L121-122 verbatim
def withVCGenStructuralTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addStructuralTime k


-- @@ L124-125 verbatim
def withVCGenWpStepTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addWpStepTime k


-- @@ L127-128 verbatim
def withVCGenProbPlannerTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addProbPlannerTime k


-- @@ L130-131 verbatim
def withVCGenLocalHintTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addLocalHintTime k


-- @@ L133-134 verbatim
def withVCGenRegisteredTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addRegisteredTime k


-- @@ L136-137 verbatim
def withVCGenCloseTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addCloseTime k


-- @@ L139-140 verbatim
def withVCGenPassTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addPassTime k


-- @@ L142-143 verbatim
def withVCGenFinishTiming {α : Type} (k : TacticM α) : TacticM α :=
  withVCGenTiming addFinishTime k


-- @@ L145-147 verbatim
def resetVCGenTimingIfEnabled : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    vcGenTimingRef.set {}


-- @@ L149-150 verbatim
private def formatNsMs (ns : UInt64) : String :=
  s!"{ns / 1000000}ms"


-- @@ L152-161 verbatim
def logVCGenTimingIfEnabled (label : String) : TacticM Unit := do
  if vcvio.vcgen.time.get (← getOptions) then
    let d ← vcGenTimingRef.get
    logInfo m!"[{label} timing] preview={formatNsMs d.previewNs}, \
      structural={formatNsMs d.structuralNs}, wpStep={formatNsMs d.wpStepNs}, \
      probPlanner={formatNsMs d.probPlannerNs}, localHints={formatNsMs d.localHintNs}, \
      registered={formatNsMs d.registeredNs}, \
      cachedRules={formatNsMs d.cachedRuleBuildNs} \
      (hits={d.cachedRuleHits}, misses={d.cachedRuleMisses}), close={formatNsMs d.closeNs}, \
      passes={formatNsMs d.passNs}, finish={formatNsMs d.finishNs}"


-- @@ L163-167 verbatim
def withVCGenRunTiming {α : Type} (label : String) (k : TacticM α) : TacticM α := do
  resetVCGenTimingIfEnabled
  let a ← k
  logVCGenTimingIfEnabled label
  return a


-- @@ L169-173 verbatim
structure PlannedStep where
  label : String
  replayText : String
  run : TacticM Bool
  notes : List String := []


-- @@ L175-177 verbatim
structure PreviewResult where
  ok : Bool
  goalCount : Nat


-- @@ L179-180 verbatim
def withStepNotes (step : PlannedStep) (notes : List String) : PlannedStep :=
  { step with notes := step.notes ++ notes }


-- @@ L182-183 verbatim
def formatCandidateNames (names : Array Name) : String :=
  String.intercalate ", " <| names.toList.map fun name => s!"`{name}`"


-- @@ L185-189 verbatim
def previewAction (action : TacticM Bool) : TacticM Bool := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  saved.restore
  return ok


-- @@ L191-196 verbatim
def previewActionWithGoals (action : TacticM Bool) : TacticM PreviewResult := do
  let saved ← saveState
  let ok ← withVCGenPreviewTiming action
  let goalCount := (← getGoals).length
  saved.restore
  return { ok, goalCount }


-- @@ L198-199 verbatim
def previewPlannedStep (step : PlannedStep) : TacticM Bool :=
  previewAction step.run


-- @@ L201-202 verbatim
def previewPlannedStepWithGoals (step : PlannedStep) : TacticM PreviewResult :=
  previewActionWithGoals step.run


-- @@ L204-205 verbatim
def renderPlannedStepPreview (step : PlannedStep) (preview : PreviewResult) : String :=
  s!"{step.replayText} -> {preview.goalCount} goal(s)"


-- @@ L207-214 verbatim
def attachPlannerChoiceNotes
    (step : PlannedStep) (preview : PreviewResult) (alternatives : Array String) : PlannedStep :=
  withStepNotes step <|
    [s!"planner preview leaves {preview.goalCount} goal(s)"] ++
      if alternatives.isEmpty then
        []
      else
        [s!"alternatives: {String.intercalate "; " alternatives.toList}"]


-- @@ L216-239 verbatim
def chooseBestPlannedStepCandidate? (steps : Array PlannedStep) :
    TacticM (Option (PlannedStep × PreviewResult)) := do
  let traceSteps := vcvio.vcgen.traceSteps.get (← getOptions)
  let mut best? : Option (PlannedStep × PreviewResult) := none
  let mut accepted : Array String := #[]
  for step in steps do
    let preview ← previewPlannedStepWithGoals step
    if preview.ok then
      if traceSteps then
        accepted := accepted.push (renderPlannedStepPreview step preview)
      match best? with
      | none => best? := some (step, preview)
      | some (_, bestPreview) =>
          if preview.goalCount < bestPreview.goalCount then
            best? := some (step, preview)
      if !traceSteps && preview.goalCount == 0 then
        return some (step, preview)
  match best? with
  | none => return none
  | some (step, preview) =>
      if traceSteps then
        let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
        return some (attachPlannerChoiceNotes step preview alternatives, preview)
      return some (step, preview)


-- @@ L241-245 verbatim
def logPlannedStep (step : PlannedStep) (beforeGoals afterGoals : Nat) : TacticM Unit := do
  if vcvio.vcgen.traceSteps.get (← getOptions) then
    logInfo m!"[{step.label}] {step.replayText} (goals {beforeGoals} -> {afterGoals})"
    for note in step.notes do
      logInfo m!"  {note}"


-- @@ L247-253 verbatim
def executePlannedStep (step : PlannedStep) : TacticM Bool := do
  let beforeGoals := (← getGoals).length
  let ok ← step.run
  if ok then
    let afterGoals := (← getGoals).length
    logPlannedStep step beforeGoals afterGoals
  return ok


-- @@ L255-260 verbatim
def renderPassReplayLine (steps : Array PlannedStep) : Option String :=
  if steps.isEmpty then
    none
  else
    let body := String.intercalate " | " <| steps.toList.map (·.replayText)
    some s!"all_goals first | {body} | skip"


-- @@ L262-263 verbatim
def whnfReducible (e : Expr) : MetaM Expr :=
  withReducible <| whnf e


-- @@ L265-285 verbatim
/-- Normalize the reducible oracle wrappers in a goal-side computation so its
key agrees with the patterns produced by `Sym.mkPatternFromDeclWithKey`.
`Sym.DiscrTree.getMatch` is purely structural, and those stored patterns unfold
`OracleComp`, `OracleQuery`, and `OracleSpec.toPFunctor` to the underlying
structure constructor.

Do not use the more general `Sym.preprocessType` here. Besides being intended
for declaration types rather than terms, in Lean 4.33 it also unfolds reducible
user programs. A program containing a matcher can then make later
definitional equality reduce a matcher with loose de Bruijn variables and
panic in `whnfEasyCases`. The wrappers below are the only newly
reducible declarations whose shapes registry lookup needs to expose. -/
def symMatchKey (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (pre := fun e => do
    let some declName := e.getAppFn.constName? | return .continue
    unless declName == ``OracleComp || declName == ``OracleQuery ||
        declName == ``OracleSpec.toPFunctor do
      return .continue
    let some value ← unfoldDefinition? e | return .continue
    return .visit value)


-- @@ L287-288 verbatim
def headConstName? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?


-- @@ L290-295 verbatim
def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _h : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none


-- @@ L297-298 verbatim
def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  (e.find? fun e' => e'.consumeMData.getAppFn.isConstOf head).map Expr.consumeMData


-- @@ L300-309 verbatim
def relTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelTriple target then
    let args ← trailingArgs? app 3
    let #[oa, ob, post] := args | none
    some (oa, ob, post)
  else
    let app ← findAppWithHead? ``Std.Do'.RelTriple target
    let args ← trailingArgs? app 6
    let #[_pre, oa, ob, post, _epost₁, _epost₂] := args | none
    some (oa, ob, post)


-- @@ L311-315 verbatim
def relWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``OracleComp.ProgramLogic.Relational.RelWP target
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)


-- @@ L317-321 verbatim
def stdDoRelTripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr × Expr) := do
  let app ← findAppWithHead? ``Std.Do'.RelTriple target
  let args ← trailingArgs? app 6
  let #[pre, oa, ob, post, _epost₁, _epost₂] := args | none
  some (pre, oa, ob, post)


-- @@ L323-329 verbatim
private def findWpApp? (target : Expr) : Option (Expr × Nat) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.wp target then
    some (app, 2)
  else if let some app := findAppWithHead? ``Std.Do'.wp target then
    some (app, 3)
  else
    none


-- @@ L331-334 verbatim
def wpGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some args[0]!


-- @@ L336-339 verbatim
def wpGoalParts? (target : Expr) : Option (Expr × Expr) := do
  let (app, k) ← findWpApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!)


-- @@ L341-349 verbatim
def rawWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let target := target.consumeMData
  if target.isAppOfArity ``LE.le 4 then
    let pre := target.getArg! 2
    let rhs := target.getArg! 3
    let (oa, post) ← wpGoalParts? rhs
    some (pre, oa, post)
  else
    none


-- @@ L351-357 verbatim
private def findTripleApp? (target : Expr) : Option (Expr × Nat) := do
  if let some app := findAppWithHead? ``OracleComp.ProgramLogic.Triple target then
    some (app, 3)
  else if let some app := findAppWithHead? ``Std.Do'.Triple target then
    some (app, 4)
  else
    none


-- @@ L359-362 verbatim
def tripleGoalComp? (target : Expr) : Option Expr := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some args[1]!


-- @@ L364-367 verbatim
def tripleGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let (app, k) ← findTripleApp? target
  let args ← trailingArgs? app k
  some (args[0]!, args[1]!, args[2]!)


-- @@ L369-370 verbatim
def isSimulateQAction (e : Expr) : Bool :=
  (findAppWithHead? ``simulateQ e).isSome


-- @@ L372-373 verbatim
def hasStateTRunExpr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run e).isSome


-- @@ L375-376 verbatim
def hasStateTRun'Expr (e : Expr) : Bool :=
  (findAppWithHead? ``StateT.run' e).isSome


-- @@ L378-379 verbatim
def hasStateTRunLike (e : Expr) : Bool :=
  hasStateTRunExpr e || hasStateTRun'Expr e


-- @@ L381-382 verbatim
def hasSimulateQRunLike (e : Expr) : Bool :=
  isSimulateQAction e && hasStateTRunLike e


-- @@ L384-385 verbatim
def isEqRelPost (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.ProgramLogic.Relational.EqRel e).isSome


-- @@ L387-389 verbatim
def isBindExpr (e : Expr) : Bool :=
  let fn := e.consumeMData.getAppFn
  fn.isConstOf ``Bind.bind || fn.isConstOf ``StateT.bind


-- @@ L391-392 verbatim
def isPureExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Pure.pure


-- @@ L394-396 verbatim
def isIfExpr (e : Expr) : Bool :=
  let fn := e.consumeMData.getAppFn
  fn.isConstOf ``ite || fn.isConstOf ``dite


-- @@ L398-399 verbatim
def isMapExpr (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``Functor.map


-- @@ L401-402 verbatim
def isReplicateExpr (e : Expr) : Bool :=
  (findAppWithHead? ``OracleComp.replicate e).isSome


-- @@ L404-405 verbatim
def isListMapMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.mapM e).isSome


-- @@ L407-408 verbatim
def isListFoldlMExpr (e : Expr) : Bool :=
  (findAppWithHead? ``List.foldlM e).isSome


-- @@ L410-411 verbatim
def isReplicateHead (e : Expr) : Bool :=
  (headConstName? e) == some ``OracleComp.replicate


-- @@ L413-414 verbatim
def isListMapMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.mapM


-- @@ L416-417 verbatim
def isListFoldlMHead (e : Expr) : Bool :=
  (headConstName? e) == some ``List.foldlM


-- @@ L419-420 verbatim
def isGameEquivGoal (target : Expr) : Bool :=
  target.consumeMData.getAppFn.isConstOf ``OracleComp.ProgramLogic.GameEquiv


-- @@ L422-429 verbatim
def isEvalDistEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    (findAppWithHead? ``evalSPMF lhs).isSome && (findAppWithHead? ``evalSPMF rhs).isSome
  else
    false


-- @@ L431-443 verbatim
/-- Check if a goal is an equality with probability expressions on both sides. -/
def isProbEqGoal (target : Expr) : Bool :=
  let target := target.consumeMData
  if target.isAppOfArity ``Eq 3 then
    let lhs := target.getArg! 1
    let rhs := target.getArg! 2
    let lhsHasProb := (findAppWithHead? ``probEvent lhs).isSome ||
                       (findAppWithHead? ``probOutput lhs).isSome
    let rhsHasProb := (findAppWithHead? ``probEvent rhs).isSome ||
                       (findAppWithHead? ``probOutput rhs).isSome
    lhsHasProb && rhsHasProb
  else
    false


-- @@ L445-446 verbatim
def tryEvalTacticSyntax (stx : Syntax) : TacticM Bool :=
  (evalTactic stx *> pure true) <|> pure false


-- @@ L448-462 verbatim
def focusFirstGoalSatisfying (pred : Expr → Bool) : TacticM Bool := do
  let goals ← getGoals
  let mut matched? : Option MVarId := none
  let mut rest : Array MVarId := #[]
  for goal in goals do
    let target ← instantiateMVars (← goal.getType)
    if matched?.isNone && pred target then
      matched? := some goal
    else
      rest := rest.push goal
  match matched? with
  | none => return false
  | some goal =>
      setGoals (goal :: rest.toList)
      return true


-- @@ L464-479 verbatim
def runBoundedPasses (label : String) (step : TacticM Bool) : TacticM Nat := do
  let maxPasses := vcvio.vcgen.maxPasses.get (← getOptions)
  let mut passes := 0
  while passes < maxPasses do
    if ← withVCGenPassTiming step then
      passes := passes + 1
    else
      return passes
  let saved ← saveState
  let more ← withVCGenPassTiming step
  saved.restore
  if more then
    throwError m!
      "{label}: exhausted the configured pass budget ({maxPasses}).\n\
      Increase `set_option vcvio.vcgen.maxPasses <n>` or keep stepping manually."
  return passes


-- @@ L481-499 verbatim
def runBoundedPassesCollect {α : Type} (label : String)
    (step : TacticM (Array α)) : TacticM (Array (Array α)) := do
  let maxPasses := vcvio.vcgen.maxPasses.get (← getOptions)
  let mut passes := 0
  let mut batches := #[]
  while passes < maxPasses do
    let batch ← withVCGenPassTiming step
    if batch.isEmpty then
      return batches
    passes := passes + 1
    batches := batches.push batch
  let saved ← saveState
  let more ← withVCGenPassTiming step
  saved.restore
  if !more.isEmpty then
    throwError m!
      "{label}: exhausted the configured pass budget ({maxPasses}).\n\
      Increase `set_option vcvio.vcgen.maxPasses <n>` or keep stepping manually."
  return batches


-- @@ L501-501 verbatim
end OracleComp.ProgramLogic
