/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public meta import LeanPool.Lentil.ProofMode.Basic

public import LeanPool.Lentil.ProofMode.Basic
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.String


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace TLA.ProofMode


-- @@ L17-17 verbatim
open Lean Meta Elab Tactic


-- @@ L19-24 verbatim
theorem Entails_drop_hyps {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (subHyps : List (NamedPred σ)) (hinc : subHyps.map NamedPred.pred ⊆ hyps.map NamedPred.pred) :
  Entails subHyps goal → Entails hyps goal := by
  intro h
  refine pred_implies_trans ?_ (by apply h); clear h
  apply repeatedAnd_subset_implies; exact hinc


-- @@ L26-29 verbatim
theorem Entails_clear {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toClear : List String) :
  letI hyps' := hyps.filter fun h => !toClear.contains h.name
  Entails hyps' goal → Entails hyps goal := Entails_drop_hyps _ (by grind)


-- @@ L31-34 verbatim
theorem Entails_clear_except {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
  (toKeep : List String) :
  letI hyps' := hyps.filter fun h => toKeep.contains h.name
  Entails hyps' goal → Entails hyps goal := Entails_drop_hyps _ (by grind)


-- @@ L36-36 verbatim
syntax (name := tlaClearExceptTac) "tla_clear" "*" " -" (ppSpace colGt ident)* : tactic

-- @@ L37-48 verbatim
/--
`tla_clear h₁ h₂ ...` removes temporal hypotheses from the proof-mode context.
The target predicate is unchanged, but the remaining proof must not use the
cleared hypotheses.

For example, from a context containing `hp : p`, `hq : q`, and goal `q`,
```lean
tla_clear hp
```
leaves only `hq : q` in the proof-mode context.
-/
syntax (name := tlaClearTac) "tla_clear" (ppSpace colGt ident)+ : tactic


-- @@ L50-59 verbatim
/--
`tla_clear * - h₁ h₂ ...` removes every temporal hypothesis except the named
ones. The kept hypotheses stay in their original order. For example, from
`hp : p`, `hq : q`, `hr : r`,
```lean
tla_clear * - hq
```
leaves only `hq : q`.
-/
tactic_extension tlaClearTac


-- @@ L61-61 verbatim
attribute [tactic_alt tlaClearTac] tlaClearExceptTac


-- @@ L63-65 verbatim
/-- Reduction rules used after clearing a proof-mode hypothesis. -/
meta def clearTacDSimps := #[``List.filter, ``List.contains, ``List.elem, ``or, ``and, ``not,
  ``String.reduceBEq, ``String.reduceBNe, ``Bool.false_or, ``Bool.or_false]


-- @@ L67-70 verbatim
/-- Clear the proof-mode hypotheses with the given names. -/
meta def tlaClearByName (name : List String) : TacticM Unit := do
  evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_clear) ($(quote name)) ?_)
  postDSimpAfterApplyingReflectionTheorem clearTacDSimps


-- @@ L72-79 verbatim
elab_rules : tactic
  | `(tactic| tla_clear * - $[$names:ident]*) => withMainContext do
    let toKeep := names.toList.map fun name => toString name.getId
    evalTactic <| ← `(tactic| refine $(mkIdent ``Entails_clear_except) ($(quote toKeep)) ?_)
    postDSimpAfterApplyingReflectionTheorem clearTacDSimps
  | `(tactic| tla_clear $[$names:ident]*) => withMainContext do
    let toClear := names.toList.map fun name => toString name.getId
    tlaClearByName toClear


-- @@ L81-81 verbatim
end TLA.ProofMode
