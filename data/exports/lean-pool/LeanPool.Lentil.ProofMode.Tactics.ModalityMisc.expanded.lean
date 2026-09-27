/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.ProofMode.Tactics.Monotone
meta import LeanPool.Lentil.ProofMode.Basic
import LeanPool.Lentil.Rules.Basic


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace TLA.ProofMode


-- @@ L16-16 verbatim
open Lean Meta Elab Tactic


-- @@ L18-18 verbatim
section


-- @@ L20-20 verbatim
variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}


-- @@ L22-27 verbatim
theorem Entails_toggle_goal_under_always :
    Entails (mapHypPreds TLA.always hyps) goal =
      Entails (mapHypPreds TLA.always hyps) (TLA.always goal) := by
  unfold Entails
  rw [mapHypPreds_preds, repeatedAnd_map_always]
  apply TLA.always_pred_implies


-- @@ L29-32 verbatim
end

-- FIXME: The following logic is very similar in `Lentil.ProofMode.Tactics.Monotone`,
-- consider unifying them

-- @@ L33-37 verbatim
private meta def peelAlwaysOpt (p : Expr) : Option Expr :=
  if p.getAppFn'.isConstOf ``TLA.always then
    if h : p.isApp = true then some (p.appArg h) else none
  else
    none


-- @@ L39-57 verbatim
private meta def proofModeToggleGoalUnderAlways : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let target ← cleanupAnnotAndMore (← g.getType)
  let_expr Entails _ hypsExpr goal := target
    | throwError "tla_toggle_goal_under_always: expected a proof-mode Entails goal"
  let some (hypTy, hyps) ← recognizeHypsList hypsExpr
    | throwError "tla_toggle_goal_under_always: failed to read the hypotheses from the goal"
  let some peeledHyps := hyps.mapM fun (name, pred) =>
      (peelAlwaysOpt pred).map fun pred => (name, pred)
    | throwError "tla_toggle_goal_under_always: expected every temporal hypothesis to have an always prefix"
  let peeledHypsExpr ← toHypsList hypTy peeledHyps
  let (leftToRight?, toggledGoal) :=
    match peelAlwaysOpt goal with
    | some goal => (true, goal)
    | none => (false, goal)
  let thm ← mkAppOptM ``Entails_toggle_goal_under_always #[none, some peeledHypsExpr, some toggledGoal]
  let thm ← mkAppM (if leftToRight? then ``Eq.mp else ``Eq.mpr) #[thm]
  replaceMainGoal (← g.apply thm)
  postDSimpAfterApplyingReflectionTheorem #[``mapHypPreds, ``List.map]


-- @@ L59-76 verbatim
/--
`tla_toggle_goal_under_always` toggles one leading `□` on the current
proof-mode goal when every temporal hypothesis has a leading `□`.

For example, with `hp : □ p`, it changes a proof-mode goal `□ q` to `q`:
```lean
tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
tla_toggle_goal_under_always
tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩] q
```
If the current goal has no leading `□`, the same tactic changes `q` to `□ q`:
```lean
tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩] q
tla_toggle_goal_under_always
tla_check_goal Entails [⟨"hp", [tlafml| □ p]⟩] [tlafml| □ q]
```
-/
syntax (name := tlaToggleGoalUnderAlwaysTac) "tla_toggle_goal_under_always" : tactic


-- @@ L78-79 verbatim
elab_rules : tactic
  | `(tactic| tla_toggle_goal_under_always) => proofModeToggleGoalUnderAlways


-- @@ L81-81 verbatim
end TLA.ProofMode
