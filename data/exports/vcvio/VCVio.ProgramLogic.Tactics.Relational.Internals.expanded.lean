/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Quantitative
public import VCVio.ProgramLogic.Relational.Loom.Quantitative
public import VCVio.ProgramLogic.Relational.SimulateQ
public meta import VCVio.ProgramLogic.Tactics.Common


-- @@ L14-18 verbatim
/-!
# Relational VCGen Internals

Implementation details for the relational VCGen planner and step selection.
-/


-- @@ L20-20 verbatim
public meta section


-- @@ L22-22 verbatim
open Lean Elab Tactic Meta


-- @@ L24-24 verbatim
namespace OracleComp.ProgramLogic

-- @@ L25-25 verbatim
namespace TacticInternals

-- @@ L26-26 verbatim
namespace Relational


-- @@ L28-33 verbatim
/-! ### Registered VC-spec rules

Centralized `@[vcspec]` registrations for the relational planner. Lemmas added here become
candidates for the registered-rule branch of `rvcstep`/`rvcgen` (and surface in the
"Registered `@[vcspec]` candidates" hint when the planner gets stuck), in addition to any
structural rule that `runRVCGenCore` already tries by goal shape. -/


-- @@ L35-60 verbatim
attribute [vcspec]
  -- Core relational rules from `Relational/Basic.lean`
  OracleComp.ProgramLogic.Relational.relTriple_pure_pure
  OracleComp.ProgramLogic.Relational.relTriple_bind
  OracleComp.ProgramLogic.Relational.relTriple_map
  OracleComp.ProgramLogic.Relational.relTriple_if
  OracleComp.ProgramLogic.Relational.relTriple_replicate
  OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel
  OracleComp.ProgramLogic.Relational.relTriple_list_mapM
  OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel
  OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
  OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same
  OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij
  OracleComp.ProgramLogic.Relational.relTriple_uniformSample_refl
  -- Quantitative rules from the default `Std.Do'.RelTriple` carrier.
  OracleComp.ProgramLogic.Relational.Loom.relTriple_pure
  OracleComp.ProgramLogic.Relational.Loom.relTriple_bind
  OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_bij
  OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl
  OracleComp.ProgramLogic.Relational.Loom.relTriple_query_bij
  OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl
  -- Raw relational WP rule from the Std.Do bridge
  Std.Do'.RelWP.rwp_pure
  -- `simulateQ`-aware rules from `Relational/SimulateQ.lean`
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
  OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_query_map_eq


-- @@ L62-63 verbatim
private def mkRVCGenPlannedStep (label replayText : String) (run : TacticM Bool) : PlannedStep :=
  { label, replayText, run }


-- @@ L65-68 verbatim
private structure RelGoalShape where
  oa : Expr
  ob : Expr
  isStdDo : Bool


-- @@ L70-76 verbatim
private def relGoalShape? (target : Expr) : Option RelGoalShape := do
  if let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target then
    some { oa, ob, isStdDo := true }
  else if let some (oa, ob, _post) := relTripleGoalParts? target then
    some { oa, ob, isStdDo := false }
  else
    none


-- @@ L78-85 verbatim
private def currentRelGoalShape? : TacticM (Option RelGoalShape) := do
  let target ← instantiateMVars (← getMainTarget)
  match relGoalShape? target with
  | none => return none
  | some shape =>
      let oa ← whnfReducible (← instantiateMVars shape.oa)
      let ob ← whnfReducible (← instantiateMVars shape.ob)
      return some { shape with oa, ob }


-- @@ L87-91 verbatim
private def relCompsDefEq (oa ob : Expr) : TacticM Bool := do
  let saved ← saveState
  let ok ← isDefEq oa ob
  saved.restore
  return ok


-- @@ L93-101 verbatim
private def propClosesByTrivial (prop : Expr) : TacticM Bool := do
  let saved ← saveState
  let goal ← mkFreshExprMVar prop
  let goalId := goal.mvarId!
  setGoals [goalId]
  let ok ← tryEvalTacticSyntax (← `(tactic| trivial))
  let closed := ok && (← getGoals).isEmpty
  saved.restore
  return closed


-- @@ L103-116 verbatim
private def relPostIsVacuous (post : Expr) : TacticM Bool := do
  let post ← instantiateMVars post
  let postTy ← whnf (← inferType post)
  let .forallE _ α body _ := postTy.consumeMData
    | return false
  let body ← whnf body
  let .forallE _ β _ _ := body.consumeMData
    | return false
  withLocalDeclD `a α fun a => do
    withLocalDeclD `b β fun b => do
      let prop ← whnfReducible (← instantiateMVars (mkApp2 post a b))
      if prop.isConstOf ``True then
        return true
      propClosesByTrivial prop


-- @@ L118-209 verbatim
/-- Attempt to close the current relational/eRHL leaf goal with the canonical fast paths.

Tries, in order:
* `assumption` (catches a hypothesis matching the relational triple verbatim);
* quantitative `Std.Do'.RelTriple` pure-pure leaves;
* `relTriple_refl` (identical computations, equality coupling);
* `relTriple_eqRel_of_eq rfl` (syntactically identical computations);
* `relTriple_pure_pure rfl` (`pure x ⨯ pure x` with reflexive postcondition);
* `relTriple_pure_pure` together with `assumption` (`pure a ⨯ pure b` with `R a b` in scope);
* a small proof-search variant of `relTriple_pure_pure` using `rfl`, `assumption`, or
  a symmetric assumption for the value-level relation;
* the same closers after `subst_vars` (resolves goals where the pure values are
  syntactically distinct but unified via local equality hypotheses);
* `relTriple_true _ _` / `relTriple_post_const` only when the postcondition has first
  been classified as vacuous.

The vacuous-postcondition rules are intentionally last and guarded. Applying them blindly to
non-vacuous pure leaves can create expensive failed elaboration attempts and obscure the
predictable pure/reflexive close path. -/
def tryCloseRelGoalImmediate : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic| assumption)) then
    return true
  let target ← instantiateMVars (← getMainTarget)
  let relTriplePost? := relTripleGoalParts? target |>.map (fun (_, _, post) => post)
  let some shape ← currentRelGoalShape? | return false
  if shape.isStdDo then
    if isPureExpr shape.oa && isPureExpr shape.ob then
      return (← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _)))
    return false
  if ← relCompsDefEq shape.oa shape.ob then
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) then
      return true
  if isPureExpr shape.oa && isPureExpr shape.ob then
    if ← tryEvalTacticSyntax (← `(tactic|
        exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_ <;>
          first | rfl | assumption | symm; assumption)) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        (try subst_vars
         first
           | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
           | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
           | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
           | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)))) then
      return true
    if ← tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> (symm; assumption))) then
      return true
  if let some post := relTriplePost? then
    if ← relPostIsVacuous post then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_post_const
            (fun _ _ => by trivial))) then
        return true
  let saved ← saveState
  if ← tryEvalTacticSyntax (← `(tactic| subst_vars)) then
    let some shape ← currentRelGoalShape? | saved.restore; return false
    if !shape.isStdDo && (← relCompsDefEq shape.oa shape.ob) then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl)) then
        return true
    if !shape.isStdDo && isPureExpr shape.oa && isPureExpr shape.ob then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;> assumption)) then
        return true
      if ← tryEvalTacticSyntax (← `(tactic|
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_ <;>
            first | rfl | assumption | symm; assumption)) then
        return true
    if shape.isStdDo && isPureExpr shape.oa && isPureExpr shape.ob then
      if ← tryEvalTacticSyntax (← `(tactic|
          exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _)) then
        return true
    saved.restore
  return false


-- @@ L211-220 verbatim
private def relationalGoalParts? (target : Expr) : Option (Expr × Expr × Expr) :=
  match relTripleGoalParts? target with
  | some parts => some parts
  | none =>
      match relWPGoalParts? target with
      | some parts => some parts
      | none =>
          match stdDoRelTripleGoalParts? target with
          | some (_, oa, ob, post) => some (oa, ob, post)
          | none => none


-- @@ L222-223 verbatim
private def isStdDoRelTripleGoal (target : Expr) : Bool :=
  (stdDoRelTripleGoalParts? target).isSome


-- @@ L225-226 verbatim
private def sameMVarId (x y : MVarId) : Bool :=
  x.name == y.name


-- @@ L228-238 verbatim
private def stripSuffix? (xs suffix : List MVarId) : Option (List MVarId) :=
  if xs.length < suffix.length then
    none
  else
    let splitAt := xs.length - suffix.length
    let pref := xs.take splitAt
    let tail := xs.drop splitAt
    if (tail.zip suffix).all fun (x, y) => sameMVarId x y then
      some pref
    else
      none


-- @@ L240-246 verbatim
private def ownedSubgoalsAfterMainStep (before after : List MVarId) : List MVarId × List MVarId :=
  match before with
  | [] => (after, [])
  | _ :: rest =>
      match stripSuffix? after rest with
      | some owned => (owned, rest)
      | none => (after, [])


-- @@ L248-259 verbatim
def tryLowerRelGoal : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if relationalGoalParts? target |>.isSome then
    return false
  if isGameEquivGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.GameEquiv.of_relTriple))
  else if isEvalDistEqGoal target then
    tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.evalSPMF_eq_of_relTriple_eqRel))
  else
    return false


-- @@ L261-270 verbatim
/-- Normalize the monad structure of both sides of a relational/eRHL goal.

Applies the standard set of monad simplification lemmas (right-association, pure-bind
elimination, `bind_pure_comp`, `Functor.map_map`, `map_pure`) to flatten nested binds
and strip pure-bind layers so that downstream rule selection (especially
`relTriple_bind`) sees aligned structures on both sides. The pass is best-effort:
`try simp only` always succeeds and leaves the goal unchanged when no lemma applies. -/
def tryNormalizeRelBindStructure : TacticM Unit := do
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, bind_pure_comp, Functor.map_map, map_pure]))


-- @@ L272-274 verbatim
def runERelPureRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _))


-- @@ L276-280 verbatim
def runERelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl))


-- @@ L282-284 verbatim
def runERelBindRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.Loom.relTriple_bind ?_ ?_))


-- @@ L286-288 verbatim
def runERelBindRuleUsing (cut : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.Loom.relTriple_bind (cut := $cut) ?_ ?_))


-- @@ L290-300 verbatim
private def runStdDoRelTripleBindLeftRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && !isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_left_le _ _ _ _ _ _)))


-- @@ L302-312 verbatim
private def runStdDoRelTripleBindRightRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post) := stdDoRelTripleGoalParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless !isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_right_le _ _ _ _ _ _)))


-- @@ L314-321 verbatim
/-- Monad-law normalization used as a fallback when a direct `relTriple_bind`
attempt fails. Flattens nested binds (`bind_assoc`) and reduces `pure_bind` so
that `commit`-style intermediate computations (e.g. `do x ← oa; pure (x, x)`)
align with the corresponding flat form on the other side. -/
def tryFlattenRelBindGoal : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
      OracleComp.bind_pure_comp]))


-- @@ L323-342 verbatim
private def tryCloseRelOwnedGoal : TacticM Bool := do
  let ok ← tryCloseRelGoalImmediate
  if ok then
    return (← getGoals).isEmpty
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | assumption
        | trivial
        | (intro _; assumption)
        | (simp only [OracleComp.ProgramLogic.Relational.EqRel]; symm; assumption)))
  if ok then
    return (← getGoals).isEmpty
  let target ← instantiateMVars (← getMainTarget)
  if (relationalGoalParts? target).isSome || (findAppWithHead? ``Std.Do'.rwp target).isSome then
    return false
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | simp only [Lean.Order.PartialOrder.rel]
        | (repeat intro; split_ifs <;> simp only [Lean.Order.PartialOrder.rel])))
  return ok && (← getGoals).isEmpty


-- @@ L344-352 verbatim
private def closeOwnedRelSubgoals (owned : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in owned do
    if ← goal.isAssigned then
      continue
    setGoals [goal]
    unless ← tryCloseRelOwnedGoal do
      remaining := remaining ++ (← getGoals)
  return remaining


-- @@ L354-376 verbatim
/-- Cheap owned-goal closer used after explicit user-guided decomposition.

This avoids the heavier relational leaf closer and its fallback simplification. In particular,
`rvcstep using R` should close the sample side of a bind and close only trivial continuations
such as `intros; assumption`, otherwise leaving the continuation for the user's proof script. -/
private def tryCloseRelOwnedGoalCheap : TacticM Bool := do
  let ok ← tryEvalTacticSyntax (← `(tactic|
      first
        | assumption
        | trivial
        | (intros; assumption)
        | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
        | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;>
            first | rfl | assumption | symm; assumption)
        | (intros
           subst_vars
           first
             | assumption
             | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
             | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure <;>
                first | rfl | assumption | symm; assumption))
        | (simp only [OracleComp.ProgramLogic.Relational.EqRel]; symm; assumption)))
  return ok && (← getGoals).isEmpty


-- @@ L378-387 verbatim
/-- Run `tryCloseRelOwnedGoalCheap` on exactly the listed owned goals, preserving failures. -/
private def closeOwnedRelSubgoalsCheap (owned : List MVarId) : TacticM (List MVarId) := do
  let mut remaining : List MVarId := []
  for goal in owned do
    if ← goal.isAssigned then
      continue
    setGoals [goal]
    unless ← tryCloseRelOwnedGoalCheap do
      remaining := remaining ++ (← getGoals)
  return remaining


-- @@ L389-408 verbatim
/-- After `relTriple_bind ?_ ?_` produces `[sample, continuation, …pre-existing]`,
this helper tries to auto-close the sample subgoal (typically `RelTriple oa oa
(EqRel _)` closes via `relTriple_refl`) and the continuation subgoal in isolation,
then puts any unclosed continuation first for the user's natural `intro`-style flow.

Pre-existing goals (those already in the goal list before `relTriple_bind` produced
the two new subgoals at the head) are preserved unchanged at the tail; the helper
never touches or reorders them. This guards against the multi-goal scenario where
`rvcstep` is invoked on a goal sitting alongside other open goals (for example,
after `constructor`): a naive close-then-swap would, when the sample closes,
swap the continuation with an unrelated trailing goal, and a follow-up close pass
could fire on it. -/
def closeSampleAndReorderBindGoals : TacticM Unit := do
  let goalsBefore ← getGoals
  match goalsBefore with
  | sample :: continuation :: rest =>
      let postSample ← closeOwnedRelSubgoals [sample]
      let postCont ← closeOwnedRelSubgoals [continuation]
      setGoals (postCont ++ postSample ++ rest)
  | _ => pure ()


-- @@ L410-422 verbatim
/-- Close the bind sample subgoal normally and the continuation only by cheap closers.

This is the explicit-cut variant of `closeSampleAndReorderBindGoals`, used by
`rvcstep using R`. Supplying `R` is already the strategic choice, so the tactic should not
run the full continuation closer and accidentally search through the user-owned continuation. -/
private def closeSampleAndCheapContinuation : TacticM Unit := do
  let goalsBefore ← getGoals
  match goalsBefore with
  | sample :: continuation :: rest =>
      let postSample ← closeOwnedRelSubgoals [sample]
      let postCont ← closeOwnedRelSubgoalsCheap [continuation]
      setGoals (postCont ++ postSample ++ rest)
  | _ => pure ()


-- @@ L424-451 verbatim
def runRelBindRule : TacticM Bool := do
  tryNormalizeRelBindStructure
  if (← getGoals).isEmpty then
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_)) then
    closeSampleAndReorderBindGoals
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_)) then
    closeSampleAndReorderBindGoals
    return true
  -- Fallback: flatten nested binds via monad laws and retry the EqRel-bind cut.
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind
         (R := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))) then
    closeSampleAndReorderBindGoals
    return true
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind ?_ ?_))) then
    closeSampleAndReorderBindGoals
    return true
  return false


-- @@ L453-523 verbatim
/-- Bijection-coupling interpretation of an `rvcstep using f` hint when both sides
of a bind start with a uniform sample / query.

Given a goal `RelTriple ((⋯ : OracleComp _ α) >>= fa) ((⋯ : OracleComp _ α) >>= fb) S`,
applies a specialized bind-bijection rule when possible. The continuation then
mentions only the left sample, with the right sample already rewritten to `f a`.

Resulting goal order:
1. The continuation `RelTriple (fa a) (fb (f a)) S` for an arbitrary fresh `a`.
2. The bijectivity side condition `Function.Bijective f`.
3. Any prior trailing goals.

Returns `true` iff every step of the recipe fired; otherwise restores state and
returns `false` so a caller can try a different interpretation of the hint. -/
def runRelBindBijRuleUsing (f : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  -- Best-effort normalization so `<$>` / `bind_pure_comp` shapes are also
  -- recognized as bind-on-both-sides for the purposes of the recipe.
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Functor.map_map,
      map_pure, map_bind]))
  if ← tryEvalTacticSyntax (← `(tactic|
      first
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind_uniformSample_bij
            (f := $f) ?_ ?_
        | refine OracleComp.ProgramLogic.Relational.relTriple_bind_query_bij
            _ (f := $f) ?_ ?_)) then
    match ← getGoals with
    | cont :: bijGoals =>
        setGoals [cont]
        let _ ← tryEvalTacticSyntax (← `(tactic| intro x))
        discard <| tryCloseRelOwnedGoalCheap
        let contGoals ← getGoals
        setGoals (contGoals ++ bijGoals)
        return true
    | _ =>
        saved.restore
        return false
  saved.restore
  let saved ← saveState
  let _ ← tryEvalTacticSyntax (← `(tactic|
    try simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Functor.map_map,
      map_pure, map_bind]))
  unless ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (R := fun a b => b = $f a) ?_ ?_)) do
    saved.restore
    return false
  let bindGoals ← getGoals
  match bindGoals with
  | sample :: cont :: rest =>
      setGoals [sample]
      let sampleClosed ← tryEvalTacticSyntax (← `(tactic|
        first
          | refine OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij
              (f := $f) ?_ _ (fun _ => rfl)
          | refine OracleComp.ProgramLogic.Relational.relTriple_query_bij
              _ (f := $f) ?_ _ (fun _ => rfl)))
      unless sampleClosed do
        saved.restore
        return false
      let bijGoals ← getGoals
      setGoals [cont]
      let _ ← tryEvalTacticSyntax (← `(tactic| intro _ _ heq; subst heq))
      discard <| tryCloseRelOwnedGoalCheap
      let contGoals ← getGoals
      setGoals (contGoals ++ bijGoals ++ rest)
      return true
  | _ =>
      saved.restore
      return false


-- @@ L525-541 verbatim
def runRelBindRuleUsing (R : TSyntax `term) : TacticM Bool := do
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_)) then
    closeSampleAndCheapContinuation
    return true
  -- Fallback 1: flatten nested binds and retry with the explicit cut.
  if ← tryEvalTacticSyntax (← `(tactic|
      (simp only [bind_assoc, pure_bind, bind_pure_comp, map_pure, map_bind,
        OracleComp.bind_pure_comp]
       refine OracleComp.ProgramLogic.Relational.relTriple_bind (R := $R) ?_ ?_))) then
    closeSampleAndCheapContinuation
    return true
  -- Fallback 2: hint may be a bijection `f : α → α` (not a relation).
  -- Try the bijection-coupling recipe used when both sides bind a uniform sample.
  if ← runRelBindBijRuleUsing R then
    return true
  return false


-- @@ L543-545 verbatim
def runRelMapRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_map))


-- @@ L547-551 verbatim
def runRelReplicateRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_replicate))


-- @@ L553-558 verbatim
def runRelMapMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
      (Rin := OracleComp.ProgramLogic.Relational.EqRel _) ?_ ?_))


-- @@ L560-564 verbatim
private def closeRelAssumptionSideGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  let (owned, rest) := ownedSubgoalsAfterMainStep before after
  let remainingOwned ← closeOwnedRelSubgoals owned
  setGoals (remainingOwned ++ rest)


-- @@ L566-573 verbatim
def runRelMapMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_list_mapM
        (Rin := $R) ?_ ?_)) then
    closeRelAssumptionSideGoals before
    return true
  return false


-- @@ L575-577 verbatim
def runRelFoldlMRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same))


-- @@ L579-586 verbatim
def runRelFoldlMRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      refine OracleComp.ProgramLogic.Relational.relTriple_list_foldlM
        (Rin := $R) ?_ ?_ ?_)) then
    closeRelAssumptionSideGoals before
    return true
  return false


-- @@ L588-592 verbatim
def runRelRndRuleUsing (f : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij _ (f := $f) <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij (f := $f) <;> skip))


-- @@ L594-603 verbatim
def runRelRndRuleWithContextBijection : TacticM Bool := withMainContext do
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if let some app := findAppWithHead? ``Function.Bijective type then
        if let some args := trailingArgs? app 1 then
          let fStx ← PrettyPrinter.delab args[0]!
          if ← runRelRndRuleUsing fStx then
            return true
  return false


-- @@ L605-614 verbatim
def runRelRndRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_query _)) <||>
  tryEvalTacticSyntax (← `(tactic|
    exact OracleComp.ProgramLogic.Relational.relTriple_refl _)) <||>
  runRelRndRuleWithContextBijection <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_query_bij <;> [skip])) <||>
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij <;> skip))


-- @@ L616-628 verbatim
def runRelCondRule : TacticM Bool := do
  let before ← getGoals
  if ← tryEvalTacticSyntax (← `(tactic|
      apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _)) <||>
      tryEvalTacticSyntax (← `(tactic|
        (simp only [game_rule]
         apply OracleComp.ProgramLogic.Relational.relTriple_if <;> intro _))) then
    let after ← getGoals
    let (owned, rest) := ownedSubgoalsAfterMainStep before after
    let remainingOwned ← closeOwnedRelSubgoals owned
    setGoals (remainingOwned ++ rest)
    return true
  return false


-- @@ L630-633 verbatim
def runByUptoRule (bad : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.tvDist_simulateQ_le_probEvent_bad
      (bad := $bad)))


-- @@ L635-637 verbatim
def runRelSymmRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_symm))


-- @@ L639-645 verbatim
def runRelTransRule (mid : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
      (mid := $mid) ?_ ?_)) <||>
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right
      (mid := $mid) ?_ ?_))


-- @@ L647-650 verbatim
def runRelSwapLeftRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_left
      (hleft := OracleComp.ProgramLogic.Relational.relTriple_bind_bind_swap_eqRel) ?_))


-- @@ L652-655 verbatim
def runRelSwapRightRule : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_trans_eqRel_right
      (hright := OracleComp.ProgramLogic.Relational.relTriple_bind_bind_swap_eqRel) ?_))


-- @@ L657-663 verbatim
def runRelSwapLeftRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  if ← runRelSwapLeftRule then
    if ← runRelBindRuleUsing R then
      return true
  saved.restore
  return false


-- @@ L665-671 verbatim
def runRelSwapRightRuleUsing (R : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  if ← runRelSwapRightRule then
    if ← runRelBindRuleUsing R then
      return true
  saved.restore
  return false


-- @@ L673-689 verbatim
def runRelSimRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, _) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        return false
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run' (R_state := Eq))) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run')) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run))
      else
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run))
  | none => return false


-- @@ L691-705 verbatim
def runRelSimRuleUsing (R : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, _) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) then
        return false
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob then
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run' (R_state := $R))) <||>
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run (R_state := $R)))
      else
        tryEvalTacticSyntax (← `(tactic|
          apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run (R_state := $R)))
  | none => return false


-- @@ L707-715 verbatim
def runRelSimDistRule : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match relTripleGoalParts? target with
  | some (oa, ob, post) =>
      if !(hasSimulateQRunLike oa) || !(hasSimulateQRunLike ob) || !isEqRelPost post then
        return false
      tryEvalTacticSyntax (← `(tactic|
        apply OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'_of_impl_evalSPMF_eq))
  | none => return false


-- @@ L717-730 verbatim
private def rawRelWPGoalParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  if let some parts := relWPGoalParts? target then
    return parts
  let target := target.consumeMData
  let rhs ←
    if target.isAppOfArity ``LE.le 4 ||
        target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
      some (target.getArg! 3)
    else
      none
  let app ← findAppWithHead? ``Std.Do'.rwp rhs
  let args ← trailingArgs? app 5
  let #[oa, ob, post, _epost₁, _epost₂] := args | none
  some (oa, ob, post)


-- @@ L732-734 verbatim
private def isRawStdDoRelWPGoal (target : Expr) : Bool :=
  (rawRelWPGoalParts? target).isSome ||
    (findAppWithHead? ``Std.Do'.rwp target).isSome


-- @@ L736-749 verbatim
private def rawRelWPGoalFullParts? (target : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) := do
  let target := target.consumeMData
  let pre ←
    if target.isAppOfArity ``LE.le 4 ||
        target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
      some (target.getArg! 2)
    else
      none
  let rhs := target.getArg! 3
  let app ← findAppWithHead? ``Std.Do'.rwp rhs
  let args ← trailingArgs? app 5
  let #[oa, ob, post, epost₁, epost₂] := args | none
  some (pre, oa, ob, post, epost₁, epost₂)


-- @@ L751-754 verbatim
private def pureValue? (e : Expr) : Option Expr := do
  let e := e.consumeMData
  guard <| e.getAppFn.isConstOf ``Pure.pure
  e.getAppArgs.back?


-- @@ L756-760 verbatim
private def monadFnFromCompType? (type : Expr) : Option Expr := do
  let type := type.consumeMData
  let args := type.getAppArgs
  guard <| 0 < args.size
  some <| mkAppN type.getAppFn (args.extract 0 (args.size - 1))


-- @@ L762-767 verbatim
private def rawOrderBounds? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``LE.le 4 ||
      type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    return some (type.getArg! 2, type.getArg! 3)
  return none


-- @@ L769-774 verbatim
private def runRawRelWPReflRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (lhs, rhs) ← rawOrderBounds? target | return false
  unless (← isDefEq lhs rhs) do
    return false
  tryEvalTacticSyntax (← `(tactic| exact Lean.Order.PartialOrder.rel_refl))


-- @@ L776-811 verbatim
/-- Direct leaf rule for raw `Std.Do'.rwp` pure-pure goals.
This handles the raw counterpart of the folded quantitative `RelTriple` pure
case without first manufacturing a registered-rule consequence wrapper. -/
private def runRawRelWPPureRule : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      let target ← instantiateMVars (← goal.getType)
      let some (_pre, oa, ob, post, epost₁, epost₂) := rawRelWPGoalFullParts? target
        | return false
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      let some a := pureValue? oa | return false
      let some b := pureValue? ob | return false
      try
        let some m₁ := monadFnFromCompType? (← inferType oa) | return false
        let some m₂ := monadFnFromCompType? (← inferType ob) | return false
        let pred ← inferType (mkApp2 post a b)
        let epred₁ ← inferType epost₁
        let epred₂ ← inferType epost₂
        let prf ← mkAppOptM ``Std.Do'.RelWP.rwp_pure
          #[some m₁, some m₂, some pred, some epred₁, some epred₂,
            none, none, none, none, none, none, none, none,
            none, none, some a, some b, some post, some epost₁, some epost₂]
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
        let prf ← instantiateMVars prf
        if prf.hasExprMVar then
          throwError "raw rwp pure proof still has metavariables:{indentExpr prf}"
        let prfTy ← instantiateMVars (← inferType prf)
        unless ← isDefEq target prfTy do
          return false
        goal.assign prf
        setGoals rest
        return true
      catch _ =>
        return false


-- @@ L813-824 verbatim
/-- Direct bind rule for raw `Std.Do'.rwp` goals with binds on both sides. -/
private def runRawRelWPBindRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_le _ _ _ _ _ _ _)))


-- @@ L826-837 verbatim
/-- Explicit left-bind rule for raw `Std.Do'.rwp` goals. -/
private def runRawRelWPBindLeftRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && !isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_left_le _ _ _ _ _ _)))


-- @@ L839-850 verbatim
/-- Explicit right-bind rule for raw `Std.Do'.rwp` goals. -/
private def runRawRelWPBindRightRule : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let some (_pre, oa, ob, _post, _epost₁, _epost₂) := rawRelWPGoalFullParts? target
    | return false
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless !isBindExpr oa && isBindExpr ob do
    return false
  tryEvalTacticSyntax (← `(tactic|
    refine Lean.Order.PartialOrder.rel_trans ?_
      (Std.Do'.RelWP.rwp_bind_right_le _ _ _ _ _ _)))


-- @@ L852-877 verbatim
/-- Try direct-hit registered `@[vcspec]` rules against a raw relational WP goal. -/
private def runRawRelWPTheoremConseq (thm : TSyntax `term)
    (requireClosed : Bool := false) : TacticM Bool := do
  unless isRawStdDoRelWPGoal (← instantiateMVars (← getMainTarget)) do
    return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      let before ← getGoals
      evalTactic (← `(tactic|
        refine Std.Do'.RelWP.rwp_consequence_rel _ _ _ _ _ _
          (by
            intro a b
            by_cases h : a = b <;> simp [h, Lean.Order.PartialOrder.rel])
          $thm))
      let after ← getGoals
      let (owned, rest) := ownedSubgoalsAfterMainStep before after
      let remainingOwned ← closeOwnedRelSubgoals owned
      setGoals (remainingOwned ++ rest)
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false


-- @@ L879-888 verbatim
/-- Registered relational rules that are safe as deterministic structural steps.
They may decompose the current goal, but they do not choose cuts, bijections, or
one-sided bind frontiers. -/
private def structuralRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_map,
  ``OracleComp.ProgramLogic.Relational.relTriple_replicate,
  ``OracleComp.ProgramLogic.Relational.relTriple_replicate_eqRel,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_mapM_eqRel,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_foldlM_same
]


-- @@ L890-898 verbatim
/-- Registered relational rules that close deterministic leaves. -/
private def leafRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_pure_pure,
  ``OracleComp.ProgramLogic.Relational.relTriple_uniformSample_refl,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_pure,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_refl,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl,
  ``Std.Do'.RelWP.rwp_pure
]


-- @@ L900-912 verbatim
/-- Registered relational rules that require an explicit user choice. -/
private def explicitRelVCSpecDecls : List Name := [
  ``OracleComp.ProgramLogic.Relational.relTriple_bind,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_mapM,
  ``OracleComp.ProgramLogic.Relational.relTriple_list_foldlM,
  ``OracleComp.ProgramLogic.Relational.relTriple_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_query_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_bind_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.relTriple_bind_query_bij,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_bind,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_uniformSample_bij,
  ``OracleComp.ProgramLogic.Relational.Loom.relTriple_query_bij
]


-- @@ L914-919 verbatim
private inductive RelVCSpecTier where
  | structural
  | leaf
  | explicit
  | fallback
  deriving BEq


-- @@ L921-924 verbatim
private def relVCSpecEntryDeclIn (entry : VCSpecEntry) (decls : List Name) : Bool :=
  match entry.declName? with
  | some declName => decls.contains declName
  | none => false


-- @@ L926-934 verbatim
private def relVCSpecTier (entry : VCSpecEntry) : RelVCSpecTier :=
  if relVCSpecEntryDeclIn entry structuralRelVCSpecDecls then
    .structural
  else if relVCSpecEntryDeclIn entry leafRelVCSpecDecls then
    .leaf
  else if relVCSpecEntryDeclIn entry explicitRelVCSpecDecls then
    .explicit
  else
    .fallback


-- @@ L936-938 verbatim
private def RelVCSpecTier.canRunInDefaultDirect : RelVCSpecTier → Bool
  | .explicit => false
  | _ => true


-- @@ L940-942 verbatim
private def RelVCSpecTier.canRunInDefaultStructural : RelVCSpecTier → Bool
  | .structural | .leaf => true
  | _ => false


-- @@ L944-946 verbatim
private def RelVCSpecTier.canRunInFallbackSearch : RelVCSpecTier → Bool
  | .fallback => true
  | _ => false


-- @@ L948-985 verbatim
private def runRawRelWPVCSpecBackward : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some (oa, ob, _) := rawRelWPGoalParts? target | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    let entries :=
      (entries.filter fun entry =>
        entry.kind == .relWP && (relVCSpecTier entry).canRunInDefaultDirect) ++
      (entries.filter fun entry =>
        entry.kind == .relTriple && (relVCSpecTier entry).canRunInDefaultDirect)
    for entry in entries.toList.take 8 do
      let saved ← saveState
      if entry.kind == .relWP then
        let ok ←
          match ← observing? do
            let before ← getGoals
            unless ← runVCSpecEntryRawRelConsequence entry do
              throwError "raw relational consequence rule did not apply"
            let after ← getGoals
            let (owned, rest) := ownedSubgoalsAfterMainStep before after
            let remainingOwned ← closeOwnedRelSubgoals owned
            setGoals (remainingOwned ++ rest)
          with
          | some _ => pure true
          | none => pure false
        if ok then
          return true
        saved.restore
      let ok ←
        match ← observing? do
          runVCSpecEntryCachedBackward entry
        with
        | some ok => pure ok
        | none => pure false
      if ok then
        return true
      saved.restore
    return false


-- @@ L987-999 verbatim
private inductive RelGoalKind where
  | relTripleVacuous
  | relTriplePure
  | relTripleRefl
  | relTripleBind
  | relTripleSpec
  | relWP
  | stdDoRelTriple
  | rawRWP
  | couplingPost
  | oneSidedCandidate
  | unknown
  deriving BEq


-- @@ L1001-1003 verbatim
private def RelGoalKind.canTryImmediateClose : RelGoalKind → Bool
  | .relTripleVacuous | .relTriplePure | .relTripleRefl => true
  | _ => false


-- @@ L1005-1035 verbatim
private def classifyRelGoalKind (target : Expr) : TacticM RelGoalKind := do
  if isRawStdDoRelWPGoal target then
    return .rawRWP
  if (relWPGoalParts? target).isSome then
    return .relWP
  if (findAppWithHead? ``OracleComp.ProgramLogic.Relational.CouplingPost target).isSome then
    return .couplingPost
  let some shape := relGoalShape? target | return .unknown
  let post? :=
    match relTripleGoalParts? target with
    | some (_, _, post) => some post
    | none =>
        match stdDoRelTripleGoalParts? target with
        | some (_, _, _, post) => some post
        | none => none
  if let some post := post? then
    if ← relPostIsVacuous post then
      return .relTripleVacuous
  let oa ← whnfReducible (← instantiateMVars shape.oa)
  let ob ← whnfReducible (← instantiateMVars shape.ob)
  if isPureExpr oa && isPureExpr ob then
    return .relTriplePure
  if isBindExpr oa && isBindExpr ob then
    return .relTripleBind
  if isBindExpr oa != isBindExpr ob then
    return .oneSidedCandidate
  if ← relCompsDefEq oa ob then
    return .relTripleRefl
  if shape.isStdDo then
    return .stdDoRelTriple
  return .relTripleSpec


-- @@ L1037-1057 verbatim
private def tryCloseRelGoalAtCoreGateway : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  let goalKind ← classifyRelGoalKind target
  match goalKind with
  | .relTripleVacuous =>
      tryEvalTacticSyntax (← `(tactic|
        first
          | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
          | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
              (fun _ _ => by trivial)))
  | _ =>
      if goalKind.canTryImmediateClose then
        tryCloseRelGoalImmediate
      else
        -- Fallback for vacuous posts whose elaborated form is easier for Lean's
        -- theorem application than for syntactic postcondition inspection.
        tryEvalTacticSyntax (← `(tactic|
          first
            | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
            | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
                (fun _ _ => by trivial)))


-- @@ L1059-1061 verbatim
/-- Controlled one-sided relational bind step on the left. -/
def runRVCGenRawBindLeftStep : TacticM Bool := withMainContext do
  runRawRelWPBindLeftRule <||> runStdDoRelTripleBindLeftRule


-- @@ L1063-1065 verbatim
/-- Controlled one-sided relational bind step on the right. -/
def runRVCGenRawBindRightStep : TacticM Bool := withMainContext do
  runRawRelWPBindRightRule <||> runStdDoRelTripleBindRightRule


-- @@ L1067-1123 verbatim
def runRVCGenCore : TacticM Bool := withVCGenStructuralTiming <| withMainContext do
  tryNormalizeRelBindStructure
  if (← getGoals).isEmpty then
    return true
  if ← runRawRelWPReflRule then
    return true
  if ← runRawRelWPPureRule then
    return true
  if ← runRawRelWPBindRule then
    return true
  if ← runRawRelWPVCSpecBackward then
    return true
  let target ← instantiateMVars (← getMainTarget)
  if ← tryCloseRelGoalAtCoreGateway then
    return true
  if let some (_pre, oa, ob, _) := stdDoRelTripleGoalParts? target then
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if ← runERelPureRule then
      return true
    if ← runERelRndRule then
      return true
    if isBindExpr oa && isBindExpr ob then
      if ← runERelBindRule then
        return true
    return false
  match relTripleGoalParts? target with
  | none => return false
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if isIfExpr oa && isIfExpr ob then
        if ← runRelCondRule then
          return true
      if hasStateTRun'Expr oa && hasStateTRun'Expr ob && hasSimulateQRunLike oa &&
          hasSimulateQRunLike ob && isEqRelPost post then
        if ← runRelSimDistRule then
          return true
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        if ← runRelSimRule then
          return true
      if isMapExpr oa && isMapExpr ob then
        if ← runRelMapRule then
          return true
      if isReplicateExpr oa || isReplicateExpr ob then
        if ← runRelReplicateRule then
          return true
      if isListMapMExpr oa || isListMapMExpr ob then
        if ← runRelMapMRule then
          return true
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        if ← runRelFoldlMRule then
          return true
      if isBindExpr oa && isBindExpr ob then
        if ← runRelBindRule then
          return true
      runRelRndRule


-- @@ L1125-1163 verbatim
def runRVCGenCoreUsing (hint : TSyntax `term) : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if let some (_, oa, ob, _) := stdDoRelTripleGoalParts? target then
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    if isBindExpr oa && isBindExpr ob then
      return (← runERelBindRuleUsing hint)
    return false
  match relTripleGoalParts? target with
  | none => return false
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob &&
          !(hasStateTRun'Expr oa && hasStateTRun'Expr ob && isEqRelPost post) then
        if ← runRelSimRuleUsing hint then
          return true
      if isListMapMExpr oa || isListMapMExpr ob then
        if ← runRelMapMRuleUsing hint then
          return true
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        if ← runRelFoldlMRuleUsing hint then
          return true
      if isBindExpr oa && isBindExpr ob then
        if ← runRelBindRuleUsing hint then
          return true
      if ← runRelRndRuleUsing hint then
        return true
      -- Generic bijection-coupling-bind fallback. Handles `<$>`-shaped goals (and
      -- more generally any goal that normalizes to `bind` on both sides) by
      -- treating the hint as a bijection `f : α → α`, cutting with
      -- `R := fun a b => b = f a`, and discharging the sample subgoal via
      -- `relTriple_uniformSample_bij` / `relTriple_query_bij`.
      if ← runRelBindBijRuleUsing hint then
        return true
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        runRelSimRuleUsing hint
      else
        return false


-- @@ L1165-1180 verbatim
private def potentialRelHintNames : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless relationalGoalParts? target |>.isSome do return #[]
    let mut found : Array Name := #[]
    for localDecl in ← getLCtx do
      unless localDecl.isImplementationDetail do
        let name := localDecl.userName
        if isUsableBinderName name then
          let type ← instantiateMVars localDecl.type
          unless type.isSort do
            unless ← isProp type do
              let whnfType ← whnfReducible type
              if whnfType.isForall then
                found := found.push name
    return found


-- @@ L1182-1191 verbatim
private def localNameOfExpr? (expr : Expr) : TacticM (Option Name) := do
  match expr.consumeMData with
  | .fvar fvarId =>
      match (← getLCtx).find? fvarId with
      | some decl =>
          if isUsableBinderName decl.userName then
            return some decl.userName
          return none
      | none => return none
  | _ => return none


-- @@ L1193-1194 verbatim
private def pushNameIfNew (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name


-- @@ L1196-1201 verbatim
private def relTripleTopParts? (target : Expr) : Option (Expr × Expr × Expr) := do
  let app := target.consumeMData
  guard <| app.getAppFn.isConstOf ``OracleComp.ProgramLogic.Relational.RelTriple
  let args ← trailingArgs? app 3
  let #[oa, ob, post] := args | none
  some (oa, ob, post)


-- @@ L1203-1215 verbatim
private def provenRelPostHintNames : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relationalGoalParts? target |>.isSome do
    return #[]
  let mut found : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if ← isProp type then
        if let some (_, _, post) := relTripleTopParts? type then
          if let some name ← localNameOfExpr? post then
            found := pushNameIfNew found name
  return found


-- @@ L1217-1230 verbatim
private def provenBijectiveHintNames : TacticM (Array Name) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless relationalGoalParts? target |>.isSome do
    return #[]
  let mut found : Array Name := #[]
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let type ← instantiateMVars localDecl.type
      if ← isProp type then
        if let some app := findAppWithHead? ``Function.Bijective type then
          if let some args := trailingArgs? app 1 then
            if let some name ← localNameOfExpr? args[0]! then
              found := pushNameIfNew found name
  return found


-- @@ L1232-1238 verbatim
private def priorityRelHintNames : TacticM (Array Name) := do
  let mut found := #[]
  for name in ← provenRelPostHintNames do
    found := pushNameIfNew found name
  for name in ← provenBijectiveHintNames do
    found := pushNameIfNew found name
  return found


-- @@ L1240-1243 verbatim
private def findUniquePriorityRelHint? : TacticM (Option Name) := do
  let found ← priorityRelHintNames
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none


-- @@ L1245-1259 verbatim
/-- Find the local hypotheses that work as relational `using` hints. -/
def findRelHintCandidates : TacticM (Array Name) :=
  withVCGenLocalHintTiming <| withMainContext do
    let proven ← priorityRelHintNames
    unless proven.isEmpty do
      return proven
    let mut found : Array Name := #[]
    for name in ← potentialRelHintNames do
      let saved ← saveState
      let hint := mkIdent name
      let ok ← runRVCGenCoreUsing hint
      saved.restore
      if ok then
        found := found.push name
    return found


-- @@ L1261-1266 verbatim
/-- Find the unique local hypothesis that works as a relational `using` hint.
Returns `none` if there are 0 or ≥ 2 viable hints (keeping ambiguity explicit). -/
def findUniqueRelHint? : TacticM (Option Name) := do
  let found ← findRelHintCandidates
  return found.toList.head? >>= fun first =>
    if found.size = 1 then some first else none


-- @@ L1268-1281 verbatim
private def runRVCGenExplicitHintStep (hint : TSyntax `term) : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      progress := true
  if ← runRVCGenCoreUsing hint then
    return true
  return progress


-- @@ L1283-1295 verbatim
def runRVCGenStepUsingWithNames (hint : TSyntax `term) (names : Array Name) : TacticM Bool := do
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    if ← introMainGoalNames names then
      progress := true
  if ← runRVCGenCoreUsing hint then
    introAllGoalsNames names
    renameInaccessibleNames names
    return true
  return progress


-- @@ L1297-1301 verbatim
private def closeRelTheoremStepGoals (before : List MVarId) : TacticM Unit := do
  let after ← getGoals
  let (owned, rest) := ownedSubgoalsAfterMainStep before after
  let remainingOwned ← closeOwnedRelSubgoals owned
  setGoals (remainingOwned ++ rest)


-- @@ L1303-1307 verbatim
/-- Try to close a relational goal by applying postcondition monotonicity and
closing both the inner triple and the implication from local hypotheses. -/
def tryCloseRelGoalConseq : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    apply OracleComp.ProgramLogic.Relational.relTriple_post_mono <;> assumption))


-- @@ L1309-1311 verbatim
def runRelUptoRule (R : TSyntax `term) : TacticM Bool := do
  tryEvalTacticSyntax (← `(tactic|
    refine OracleComp.ProgramLogic.Relational.relTriple_post_mono (R := $R) ?_ ?_))


-- @@ L1313-1327 verbatim
private def runRVCGenStepWithTheoremDirect
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let ok ←
    match ← observing? do
      let before ← getGoals
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false


-- @@ L1329-1368 verbatim
private def runRVCGenStepWithTheoremConseq
    (thm : TSyntax `term) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if isRawStdDoRelWPGoal target then
    return (← runRawRelWPTheoremConseq thm requireClosed)
  let wrapper? ←
    if (relTripleGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.relTriple_post_mono ?_ ?_))
    else if (relWPGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine le_trans ?_
          (MAlgRelOrdered.relWP_mono
            (m₁ := OracleComp _) (m₂ := OracleComp _) (l := Prop) _ _ ?_)))
    else if (stdDoRelTripleGoalParts? target).isSome then
      pure <| some (← `(tactic|
        refine OracleComp.ProgramLogic.Relational.Loom.relTriple_conseq le_rfl ?_ ?_))
    else
      pure none
  let some wrapper := wrapper? | return false
  let saved ← saveState
  let ok ←
    match ← observing? do
      evalTactic wrapper
      unless ← focusFirstGoalSatisfying fun target =>
          (relTripleGoalParts? target).isSome ||
          (relWPGoalParts? target).isSome ||
          (stdDoRelTripleGoalParts? target).isSome ||
          isRawStdDoRelWPGoal target do
        throwError "rvcstep with theorem: failed to focus theorem subgoal after consequence rule"
      let before ← getGoals
      evalTactic (← `(tactic| apply $thm))
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false


-- @@ L1370-1404 verbatim
/-- Apply a `@[vcspec]` relational rule to the current goal.
Default `rvcstep` fires cached rules directly. Raw `Std.Do'.rwp` goals also get
a narrow theorem-consequence fallback because their carrier inference can fail
before the cached path sees the concrete target carrier. -/
private def runRelationalVCSpecRule
    (entry : VCSpecEntry) (requireClosed : Bool := false) : TacticM Bool := do
  let target ← instantiateMVars (← getMainTarget)
  if isRawStdDoRelWPGoal target && entry.kind == .relWP then
    let saved ← saveState
    let ok ←
      match ← observing? do
        let before ← getGoals
        unless ← runVCSpecEntryRawRelConsequence entry do
          throwError "raw relational consequence rule did not apply"
        closeRelTheoremStepGoals before
      with
      | some _ => pure true
      | none => pure false
    if ok && (!requireClosed || (← getGoals).isEmpty) then
      return true
    saved.restore
  let saved ← saveState
  let ok ←
    match ← observing? do
      let before ← getGoals
      unless ← runVCSpecEntryCachedBackward entry do
        throwError "rvcstep: registered `@[vcspec]` rule did not apply"
      closeRelTheoremStepGoals before
    with
    | some _ => pure true
    | none => pure false
  if ok && (!requireClosed || (← getGoals).isEmpty) then
    return true
  saved.restore
  return false


-- @@ L1406-1417 verbatim
/-- Try deterministic relational structural rules via cached `@[vcspec]`
before the bespoke structural dispatcher. -/
private def runDeterministicRelVCSpecRule : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some (oa, ob, _) := relationalGoalParts? target | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    for entry in entries do
      if (relVCSpecTier entry).canRunInDefaultStructural then
        if ← runRelationalVCSpecRule entry then
          return true
    return false


-- @@ L1419-1440 verbatim
/-- Try direct discrimination-tree hits for the current pair of computations.
This is a default-safe registered-rule tier because it does not scan unrelated
fallback theorems or choose among broad search candidates. -/
private def runDirectRelVCSpecRule : TacticM Bool := do
  withVCGenRegisteredTiming do
    let target ← instantiateMVars (← getMainTarget)
    let some kind :=
      if (relTripleGoalParts? target).isSome then
        some .relTriple
      else if (relWPGoalParts? target).isSome || isRawStdDoRelWPGoal target then
        some .relWP
      else
        none
      | return false
    let some (oa, ob, _) := relationalGoalParts? target <|> rawRelWPGoalParts? target
      | return false
    let entries ← getRegisteredRelationalVCSpecEntries oa ob
    for entry in entries do
      if entry.kind == kind && (relVCSpecTier entry).canRunInDefaultDirect then
        if ← runRelationalVCSpecRule entry then
          return true
    return false


-- @@ L1442-1447 verbatim
/-- Apply an explicit relational theorem/assumption step and try to close any easy side goals. -/
def runRVCGenStepWithTheorem (thm : TSyntax `term) (requireClosed : Bool := false) :
    TacticM Bool := do
  if ← runRVCGenStepWithTheoremDirect thm requireClosed then
    return true
  runRVCGenStepWithTheoremConseq thm requireClosed


-- @@ L1449-1455 verbatim
private def relationalGoalKind? (target : Expr) : Option VCSpecKind :=
  if (relTripleGoalParts? target).isSome then
    some .relTriple
  else if (relWPGoalParts? target).isSome || isRawStdDoRelWPGoal target then
    some .relWP
  else
    none


-- @@ L1457-1458 verbatim
private def takeCandidatePrefix (entries : Array VCSpecEntry) : Array VCSpecEntry :=
  (entries.toList.take 8).toArray


-- @@ L1460-1486 verbatim
private def registeredRVCGenRuleCandidateTiers
    (includeFallbackSearch : Bool := false) : TacticM (Array (Array VCSpecEntry)) := do
  let target ← instantiateMVars (← getMainTarget)
  let some kind := relationalGoalKind? target | return #[]
  let some (oa, ob, _) := relationalGoalParts? target <|> rawRelWPGoalParts? target | return #[]
  let goalPattern := classifyRelationalCompPattern oa ob
  let direct :=
    (← getRegisteredRelationalVCSpecEntries oa ob).filter fun entry =>
      entry.kind == kind && (relVCSpecTier entry).canRunInDefaultDirect
  let fallbackAll :=
    (← getVCSpecEntriesOfKind kind).filter fun entry =>
      includeFallbackSearch &&
        (relVCSpecTier entry).canRunInFallbackSearch &&
        !(direct.any fun directEntry => directEntry.theoremName! == entry.theoremName!)
  let fallbackPreferred := fallbackAll.filter (·.spec.compPattern == goalPattern)
  let fallbackFallback := fallbackAll.filter (·.spec.compPattern != goalPattern)
  let mut tiers : Array (Array VCSpecEntry) := #[]
  let rawTiers :=
    if includeFallbackSearch then
      #[direct, fallbackPreferred, fallbackFallback]
    else
      #[direct]
  for tier in rawTiers do
    let tier := takeCandidatePrefix tier
    unless tier.isEmpty do
      tiers := tiers.push tier
  return tiers


-- @@ L1488-1495 verbatim
private def runRelationalVCSpecFallbackSearchStep : TacticM Bool := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers (includeFallbackSearch := true) do
      for entry in tier do
        if (relVCSpecTier entry).canRunInFallbackSearch then
          if ← runRelationalVCSpecRule entry then
            return true
    return false


-- @@ L1497-1513 verbatim
/-- Find default-safe registered relational `@[vcspec]` entries whose bounded
application makes progress on the current goal. This uses direct
discrimination-tree hits only; broad fallback/search tiers are reserved for
`rvcfinish` / `rvcgen!`. -/
def findRegisteredRVCGenRuleCandidates : TacticM (Array VCSpecEntry) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers do
      let mut found : Array VCSpecEntry := #[]
      for entry in tier do
        let saved ← saveState
        let ok ← runRelationalVCSpecRule entry
        saved.restore
        if ok then
          found := found.push entry
      unless found.isEmpty do
        return found
    return #[]


-- @@ L1515-1533 verbatim
private def relHintCandidateSteps (hintName : Name) : TacticM (Array PlannedStep) := do
  let genericStep :=
    mkRVCGenPlannedStep
      "rvcgen explicit hint"
      s!"rvcstep using {hintName}"
      (runRVCGenExplicitHintStep (mkIdent hintName))
  let target ← instantiateMVars (← getMainTarget)
  let some (oa, ob, _) := relationalGoalParts? target | return #[genericStep]
  let oa ← whnfReducible (← instantiateMVars oa)
  let ob ← whnfReducible (← instantiateMVars ob)
  unless isBindExpr oa && isBindExpr ob do
    return #[genericStep]
  let names ← getRelBindNames
  let namedHintStep :=
    mkRVCGenPlannedStep
      "rvcgen explicit hint with names"
      s!"rvcstep using {hintName}{renderAsClause names}"
      (runRVCGenStepUsingWithNames (mkIdent hintName) names)
  return #[namedHintStep, genericStep]


-- @@ L1535-1561 verbatim
private def chooseBestRelHintStep? : TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenLocalHintTiming do
    let hintNames ← findRelHintCandidates
    let traceSteps := vcvio.vcgen.traceSteps.get (← getOptions)
    let mut best? : Option (PlannedStep × PreviewResult) := none
    let mut accepted : Array String := #[]
    for hintName in hintNames do
      for step in ← relHintCandidateSteps hintName do
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
          break
    match best? with
    | none => return none
    | some (step, preview) =>
        if traceSteps then
          let alternatives := accepted.filter (· != renderPlannedStepPreview step preview)
          return some (attachPlannerChoiceNotes step preview alternatives, preview)
        return some (step, preview)



-- @@ L1564-1575 verbatim
private def chooseBestRegisteredRVCGenTheoremStep? :
    TacticM (Option (PlannedStep × PreviewResult)) := do
  withVCGenRegisteredTiming do
    for tier in ← registeredRVCGenRuleCandidateTiers do
      let steps := tier.map fun entry =>
        mkRVCGenPlannedStep
          "rvcgen @[vcspec] theorem rule"
          s!"rvcstep with {entry.theoremName!}"
          (runRelationalVCSpecRule entry)
      if let some chosen ← chooseBestPlannedStepCandidate? steps then
        return some chosen
    return none


-- @@ L1577-1590 verbatim
/-- Structural/default relational VCGen step, excluding explicit `using`-hint fallbacks. -/
def runRVCGenStructuralCore : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  if ← runDeterministicRelVCSpecRule then
    return true
  if ← runRVCGenCore then
    return true
  if (← getGoals).isEmpty then
    return true
  return progress


-- @@ L1592-1638 verbatim
/-- Choose one relational VCGen step and remember how to replay it explicitly. -/
def planRVCGenStep? : TacticM (Option PlannedStep) := do
  if (← getGoals).isEmpty then
    return none
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    let introStep :=
      mkRVCGenPlannedStep
        "rvcgen intro"
        s!"rvcstep{renderAsClause names}"
        (introMainGoalNames names)
    if ← previewPlannedStep introStep then
      return some introStep
  let structuralStep :=
    mkRVCGenPlannedStep
      "rvcgen structural step"
      "rvcstep"
      runRVCGenStructuralCore
  let structuralPreview ← previewPlannedStepWithGoals structuralStep
  if structuralPreview.ok && structuralPreview.goalCount == 0 then
    return some structuralStep
  let closeStep :=
    mkRVCGenPlannedStep
      "rvcgen consequence close"
      "rvcfinish"
      (withVCGenCloseTiming tryCloseRelGoalConseq)
  let closePreview ← previewPlannedStepWithGoals closeStep
  if closePreview.ok && closePreview.goalCount == 0 then
    return some closeStep
  let hintCandidate? ← chooseBestRelHintStep?
  let theoremCandidate? ← chooseBestRegisteredRVCGenTheoremStep?
  if structuralPreview.ok then
    if closePreview.ok && closePreview.goalCount < structuralPreview.goalCount then
      return some closeStep
    if let some (hintStep, hintPreview) := hintCandidate? then
      if hintPreview.goalCount < structuralPreview.goalCount then
        return some hintStep
    if let some (theoremStep, theoremPreview) := theoremCandidate? then
      if theoremPreview.goalCount < structuralPreview.goalCount then
        return some theoremStep
    return some structuralStep
  if let some (hintStep, _) := hintCandidate? then
    return some hintStep
  if let some (theoremStep, _) := theoremCandidate? then
    return some theoremStep
  return none


-- @@ L1640-1646 verbatim
/-- Execute one planned relational VCGen step, returning the chosen step for replay/trace. -/
def runRVCGenPlannedStep? : TacticM (Option PlannedStep) := do
  let some step ← planRVCGenStep?
    | return none
  if ← executePlannedStep step then
    return some step
  return none


-- @@ L1648-1676 verbatim
/-- One step of relational VCGen. -/
def runRVCGenStep : TacticM Bool := do
  if (← getGoals).isEmpty then
    return false
  let mut progress := false
  if ← tryLowerRelGoal then
    progress := true
  let target ← instantiateMVars (← getMainTarget)
  if target.isForall then
    let names ← getSuggestedIntroNames 1
    if ← introMainGoalNames names then
      progress := true
  if ← tryCloseRelGoalImmediate then
    return true
  if let some hintName ← findUniquePriorityRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if ← runDeterministicRelVCSpecRule then
    return true
  if ← runRVCGenCore then
    return true
  if ← runDirectRelVCSpecRule then
    return true
  if let some hintName ← findUniqueRelHint? then
    if ← runRVCGenCoreUsing (mkIdent hintName) then
      return true
  if (← getGoals).isEmpty then
    return true
  return progress


-- @@ L1678-1679 verbatim
def runRVCGenStepUsing (hint : TSyntax `term) : TacticM Bool := do
  runRVCGenExplicitHintStep hint


-- @@ L1681-1687 verbatim
def runRVCGenStrictStepUsing (hint : TSyntax `term) : TacticM Bool := do
  let saved ← saveState
  discard <| tryLowerRelGoal
  if ← runRVCGenCoreUsing hint then
    return true
  saved.restore
  return false


-- @@ L1689-1704 verbatim
def runRVCGenPassPlanned : TacticM (Array PlannedStep) := do
  let goals ← getGoals
  if goals.isEmpty then
    return #[]
  let mut newGoals : Array MVarId := #[]
  let mut steps := #[]
  for goal in goals do
    setGoals [goal]
    if let some step ← runRVCGenPlannedStep? then
      steps := steps.push step
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return steps


-- @@ L1706-1721 verbatim
def runRVCGenPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    if ← runRVCGenStep then
      progress := true
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return progress


-- @@ L1723-1809 verbatim
def throwRVCGenStepError : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if isGameEquivGoal target then
    throwError "rvcstep: failed to lower the `GameEquiv` goal into relational proof mode."
  if isEvalDistEqGoal target then
    throwError "rvcstep: failed to lower the `evalSPMF` equality into a `RelTriple` goal."
  match relationalGoalParts? target with
  | none =>
      throwError m!
        "rvcstep: expected a `GameEquiv`, `evalSPMF` equality, `RelTriple`, `RelWP`,\n\
        or quantitative `Std.Do'.RelTriple` goal; got:{indentExpr target}"
  | some (oa, ob, post) =>
      let oa ← whnfReducible (← instantiateMVars oa)
      let ob ← whnfReducible (← instantiateMVars ob)
      let hintCandidates ← potentialRelHintNames
      let theoremCandidateTiers ← registeredRVCGenRuleCandidateTiers
      let theoremCandidates := theoremCandidateTiers.foldl (init := #[]) fun acc tier =>
        acc ++ tier.map (·.theoremName!)
      let goalLabel :=
        if isStdDoRelTripleGoal target then
          "quantitative `Std.Do'.RelTriple`"
        else if (relWPGoalParts? target).isSome then
          "`RelWP`"
        else
          "`RelTriple`"
      let hintMsg :=
        if hintCandidates.isEmpty then
          ""
        else
          s!"\nPotential local `using` hints: {formatCandidateNames hintCandidates}"
      let theoremMsg :=
        if theoremCandidates.isEmpty then
          ""
        else
          s!"\nRegistered `@[vcspec]` candidates: {formatCandidateNames theoremCandidates}\n\
          Try `rvcstep?` or `rvcstep with <theorem>` for an explicit replay."
      if hasSimulateQRunLike oa && hasSimulateQRunLike ob then
        throwError m!
          "rvcstep: found a `simulateQ` relational goal but no simulation rule applied.\n\
          If the proof needs a state invariant, try `rvcstep using R_state`.\n\
          If the goal is an output-only `run'` equality coupling, `rvcstep` also tries the \
          exact-distribution specialization automatically.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListMapMExpr oa || isListMapMExpr ob then
        throwError m!
          "rvcstep: found a `List.mapM` relational goal but no traversal rule applied.\n\
          Use `rvcstep using Rin` when the two input lists are related by a\n\
          non-equality relation.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isListFoldlMExpr oa || isListFoldlMExpr ob then
        throwError m!
          "rvcstep: found a `List.foldlM` relational goal but no fold rule applied.\n\
          Use `rvcstep using Rin` when the two input lists are related by a\n\
          non-equality relation.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isReplicateExpr oa || isReplicateExpr ob then
        throwError m!
          "rvcstep: found a `replicate` relational goal but no iteration rule applied.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      if isBindExpr oa && isBindExpr ob then
        throwError m!
          "rvcstep: found a bind-on-both-sides relational goal but could not choose\n\
          an intermediate cut.\n\
          Try `rvcstep using R` when the default cut is not the right one.\n\
          {hintMsg}{theoremMsg}\n\
          Left side:{indentExpr oa}\n\
          Right side:{indentExpr ob}\n\
          Postcondition:{indentExpr post}"
      throwError m!
        "rvcstep: found a {goalLabel} goal, but no relational VCGen rule matched.\n\
        {hintMsg}{theoremMsg}\n\
        Left side:{indentExpr oa}\n\
        Right side:{indentExpr ob}\n\
        Postcondition:{indentExpr post}\n\
        Consider `rel_conseq`, `rel_inline`, or `rel_dist` for a non-structural step."


-- @@ L1811-1828 verbatim
def throwRVCGenStepUsingError (hint : TSyntax `term) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let hintCandidates ← findRelHintCandidates
  let hintMsg :=
    if hintCandidates.isEmpty then
      ""
    else
      s!"\nViable local `using` hints here: {formatCandidateNames hintCandidates}"
  throwError m!
    "rvcstep using {hint}: the explicit hint did not match the current relational goal shape.\n\
    `using` is interpreted by goal shape as one of:\n\
    - bind cut relation (`α → β → Prop`)\n\
    - bind bijection coupling (`α → α`, on synchronized uniform/query binds)\n\
    - random/query bijection (`α → α`)\n\
    - `List.mapM` / `List.foldlM` input relation\n\
    - `simulateQ` state relation\n\
    {hintMsg}\n\
    Goal:{indentExpr target}"


-- @@ L1830-1844 verbatim
def runRVCGenCloseConseqPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : List MVarId := []
  for goal in goals do
    setGoals [goal]
    if ← withVCGenCloseTiming tryCloseRelGoalConseq then
      progress := true
      newGoals := newGoals ++ (← getGoals)
    else
      newGoals := newGoals ++ [goal]
  setGoals newGoals
  return progress


-- @@ L1846-1861 verbatim
def runRVCGenFallbackVCSpecPass : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then
    return false
  let mut progress := false
  let mut newGoals : Array MVarId := #[]
  for goal in goals do
    setGoals [goal]
    if ← runRelationalVCSpecFallbackSearchStep then
      progress := true
      for newGoal in ← getGoals do
        newGoals := newGoals.push newGoal
    else
      newGoals := newGoals.push goal
  setGoals newGoals.toList
  return progress


-- @@ L1863-1865 verbatim
def runRVCGenLeafFinish : TacticM Unit := do
  let remaining ← closeOwnedRelSubgoals (← getGoals)
  setGoals remaining


-- @@ L1867-1896 verbatim
def runRVCGenSearchFinish : TacticM Unit := do
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals try simp only [game_rule]))
  unless (← getGoals).isEmpty do
    let _ ← tryEvalTacticSyntax
      (← `(tactic| all_goals first
        | assumption
        | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
        | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
            (fun _ _ => by trivial)
        | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
        | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
        | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
        | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)
        | exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _
        | (try subst_vars
           first
             | exact OracleComp.ProgramLogic.Relational.relTriple_true _ _
             | exact OracleComp.ProgramLogic.Relational.relTriple_refl _
             | exact OracleComp.ProgramLogic.Relational.relTriple_eqRel_of_eq rfl
             | exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure rfl
             | exact OracleComp.ProgramLogic.Relational.Loom.relTriple_pure _ _ _
             | (apply OracleComp.ProgramLogic.Relational.relTriple_pure_pure; assumption)
             | exact OracleComp.ProgramLogic.Relational.relTriple_post_const
                (fun _ _ => by trivial))))
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen fallback search" runRVCGenFallbackVCSpecPass
  unless (← getGoals).isEmpty do
    discard <| runBoundedPasses "rvcgen finish" runRVCGenCloseConseqPass


-- @@ L1898-1899 verbatim
def runRVCGenFinish : TacticM Unit :=
  runRVCGenLeafFinish


-- @@ L1901-1901 verbatim
end Relational

-- @@ L1902-1902 verbatim
end TacticInternals

-- @@ L1903-1903 verbatim
end OracleComp.ProgramLogic


-- @@ L1905-1905 verbatim
set_option linter.style.longFile 2100
