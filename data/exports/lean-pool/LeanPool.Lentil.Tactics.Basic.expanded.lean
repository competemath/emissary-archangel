/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Basic
public import Aesop.BuiltinRules
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Replace
public import Std.Do.Triple.SpecLemmas
import LeanPool.Lentil.Util


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Lean Meta Elab Tactic


-- @@ L19-19 verbatim
namespace TLA


-- @@ L21-22 verbatim
/-- Try to unfold the given identifiers everywhere. -/
syntax "try_unfold_at_all" ident+ : tactic

-- @@ L23-25 verbatim
macro_rules
  | `(tactic| try_unfold_at_all $idt:ident ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt:ident $idts:ident* ) => `(tactic| (try unfold $idt at *); try_unfold_at_all $idts* )


-- @@ L27-30 verbatim
attribute [tlasimp_def] leadsTo weakFairness tlaAnd tlaOr tlaNot tlaImplies tlaForall tlaExists tlaTrue tlaFalse alwaysImplies
  always eventually later tlaUntil statePred purePred actionPred
  valid predImplies exec.satisfies exec.drop_drop
  tlaBigwedge tlaBigvee Foldable.fold


-- @@ L32-32 verbatim
attribute [execsimp] exec.drop Nat.add_zero Nat.zero_add


-- @@ L34-35 verbatim
/-- Unfold TLA definitions in all hypotheses and the goal. -/
macro "tlaUnfold" : tactic => `(tactic| (try dsimp only [tlasimp_def] at *))


-- @@ L37-38 expanded
/-- Unfold TLA and execution definitions everywhere. -/
macro "tlaUnfold'" : tactic =>
  `(tactic| ((try dsimp only [tlasimp_def] at *); (try dsimp only [execsimp] at *)))


-- @@ L40-41 verbatim
/-- Unfold TLA definitions and simplify everywhere. -/
macro "tlaUnfoldSimp" : tactic => `(tactic| (simp [tlasimp_def] at *))


-- @@ L43-44 expanded
/-- Unfold TLA and execution definitions and simplify everywhere. -/
macro "tlaUnfoldSimp'" : tactic =>
  `(tactic| ((simp [tlasimp_def] at *); (try simp only [execsimp] at *)))


-- @@ L46-49 verbatim
attribute [tla_nontemporal_def] tlaAnd tlaOr tlaNot tlaImplies tlaForall tlaExists tlaTrue tlaFalse
  statePred purePred actionPred
  valid predImplies exec.satisfies
  tlaBigwedge tlaBigvee Foldable.fold


-- @@ L51-52 verbatim
/-- Simplify with the non-temporal TLA lemmas everywhere. -/
macro "tlaNontemporalSimp" : tactic => `(tactic| (simp [tla_nontemporal_def] at *))


-- @@ L54-64 verbatim
/-- Normalize a sequent goal into a validity goal, by definitional equality. -/
def changePredImpliesToValid : TacticM Unit := withMainContext do
  let target ← getMainTarget
  match_expr target.headBeta.cleanupAnnotations with
  | TLA.predImplies _ p q =>
    let imp ← mkAppM ``TLA.tlaImplies #[p, q]
    let target' ← mkAppM ``TLA.valid #[imp]
    let goal ← getMainGoal
    replaceMainGoal [← goal.change target']
  | _ =>
    pure ()


-- @@ L66-66 verbatim
end TLA
