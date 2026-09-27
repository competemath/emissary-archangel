/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public meta import LeanPool.Lentil.Expr

public import LeanPool.Lentil.ProofMode.Tactics.Have
import LeanPool.Lentil.Rules.Basic


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace TLA.ProofMode


-- @@ L17-17 verbatim
open Lean Meta Elab Tactic LentilLib


-- @@ L19-32 expanded
theorem Entails_trans {σ : Type u} {hyps : List (NamedPred σ)} {mid goal : pred σ} :
    TLA.predImplies mid goal → Entails hyps mid → Entails hyps goal := by intro h1 h2; revert h1;
  revert h2; apply pred_implies_trans


-- @@ L34-34 verbatim
section


-- @@ L36-38 verbatim
variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

-- Well, this "last" thing might be too specific?


-- @@ L40-48 verbatim
theorem Entails_apply_hyp (hs : List (pred σ)) (h : hyps.getLast?.map NamedPred.pred = some (repeatedImplies hs goal)) :
  Entails hyps.dropLast (repeatedAnd hs) → Entails hyps goal := by
  unfold Entails
  simp [List.getLast?_eq_some_iff] at h; rcases h with ⟨a, ⟨hyps, rfl⟩, heq⟩
  simp [heq, repeatedAnd_append, repeatedAnd_singleton, ← impl_intro_add_r]
  intro h; apply pred_implies_trans h; simp [impl_intro_add_r]
  apply repeatedImplies_apply

-- FIXME: Generalize this to allow `tla_assumption`

-- @@ L49-50 verbatim
theorem Entails_apply_hyp_closing_goal (h : hyps.getLast?.map NamedPred.pred = some goal) :
  Entails hyps goal := Entails_apply_hyp [] h (by intro _ _; exact True.intro)


-- @@ L52-52 verbatim
end


-- @@ L54-55 verbatim
private meta def applyTacDSimps := #[``repeatedAnd, ``LentilLib.List.foldrD, ``List.dropLast,
  ``List.foldr]


-- @@ L57-65 verbatim
private meta def goalDirectedPremisesCut (remainingPremises : List Expr) (goal conclusion : Expr) : MetaM (List Expr) := do
  if ← isDefEq goal conclusion then
    return remainingPremises
  else
    match remainingPremises with
    | [] => throwError "tla_apply: failed to find a way to unify the goal and the hypothesis conclusion"
    | prem :: rest =>
      let newConclusion ← mkAppM ``tlaImplies #[prem, conclusion]
      goalDirectedPremisesCut rest goal newConclusion


-- @@ L67-84 verbatim
/--
`tla_apply t` proves the current proof-mode goal using a TLA theorem or a
temporal hypothesis. If the theorem concludes the current goal but still has
unsupplied temporal premises, those premises become new proof-mode goals.

For example, if the context contains `hp : p` and the goal is `q`, then
`tla_apply h hp` closes the goal when `h` proves `p |-tla- q`:
```lean
tla_apply lemma hp
```

If the goal is `r` and `lemma hp` has type `q |-tla- r`, then
```lean
tla_apply lemma hp
```
changes the goal to `q`.
-/
syntax (name := tlaApplyBackwardTac) "tla_apply " term : tactic


-- @@ L86-123 verbatim
elab_rules : tactic
  | `(tactic| tla_apply $tm:term) => withMainContext do
    (do
      let g ← getMainGoal
      let gs ← evalTacticAt (← `(tactic| refine @$(mkIdent ``Entails_trans) _ _ ?_ _ ?_ ?_)) g
      -- NOTE: This is kind of ad-hoc, relying on the exact shape of `Entails_trans`
      let [midGoal, theoremGoal, entailsGoal] := gs
        | throwError "tla_apply: failed to generate the expected number of subgoals"
      replaceMainGoal [theoremGoal, entailsGoal, midGoal]
      -- NOTE: `mid` is an auxiliary predicate to be inferred by applying the theorem;
      -- make it assignable by unification instead of leaving it synthetic opaque.
      midGoal.setKind .natural
      Tactic.focusAndDone <| evalTactic <| ← `(tactic| apply $tm)
      pruneSolvedGoals)
    <|>
    (do
      let idx ← tlaHaveTerm default /- the name does not matter here -/ tm
      withMainContext do
      let g ← getMainTarget
      let g := g.headBeta.cleanupAnnotations    -- Since `getMainTarget` does `instantiateMVars`
      let_expr TLA.ProofMode.Entails _ hyps goal := g
        | throwError "tla_apply: goal is not an Entails sequent, but {g}"
      let some (_, hyps) ← recognizeHypsList hyps
        | throwError "tla_apply: failed to read the hypotheses from the goal"
      let some (_, pred) := hyps[idx]?
        | throwError "tla_apply: failed to find the introduced theorem hypothesis"
      -- NOTE: For convenience, do not cut inner `∧`s
      let (premises, conclusion) ← TLA.Expr.splitImplicationsIntoParts pred (cutAnd? := false)
      -- The goal might be an implication, so need to find where to cut `premises`
      let premisesToProve ← goalDirectedPremisesCut premises goal conclusion
      if premisesToProve.isEmpty then
        evalTactic <| ← `(tactic| apply $(mkIdent ``Entails_apply_hyp_closing_goal) (by rfl))
      else
        let holesListStx ← do
          let holes := Array.replicate premisesToProve.length (← `(_))
          `([$holes,*])
        evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_apply_hyp) $holesListStx (by rfl) ?_)
        postDSimpAfterApplyingReflectionTheorem applyTacDSimps)


-- @@ L125-125 verbatim
end TLA.ProofMode
