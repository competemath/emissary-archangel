/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public meta import LeanPool.Lentil.ProofMode.Basic

public import LeanPool.Lentil.ProofMode.Basic
public import LeanPool.Lentil.ProofMode.Location
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.String
meta import LeanPool.Lentil.ProofMode.Location
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Util


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace TLA.ProofMode


-- @@ L22-42 verbatim
open Lean Meta Elab Tactic LentilLib

/-
Design note: `tla_specialize` should be the shared specialization engine for
proof-mode automation.

The tactic repeatedly looks at the current predicate of one temporal hypothesis
and consumes one user argument according to that predicate shape:

* `forall`: the argument is elaborated as the Lean witness.
* pure implication: the argument is elaborated as a Lean proof of the pure
  proposition.
* temporal implication: the argument names one or more existing proof-mode
  hypotheses, written either as a single identifier or as a flat tuple.

This file supports both name-based and index-based positions through
`TemporalHypLoc`. The index form is important for callers such as `tla_have := ...`,
which can append an anonymous/internal temporal hypothesis and immediately
specialize exactly that newly-added hypothesis without relying on a user-visible
name.
-/


-- @@ L44-56 expanded
/-- The general thing used in `apply`, `have` and `suffices`. -/
theorem Entails_add_new {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}
    (subHyps : List (pred σ)) (hinc : subHyps ⊆ hyps.map NamedPred.pred) (newHypName : String)
    (newHyp : pred σ) :
    TLA.predImplies (repeatedAnd subHyps) newHyp →
      Entails (hyps ++ [⟨newHypName, newHyp⟩]) goal → Entails hyps goal :=
  by
  intro h1 h2
  refine pred_implies_trans ?_ (by apply h2); clear h2
  simp [repeatedAnd_append, and_pred_implies_split]; constructor
  · rfl
  · refine pred_implies_trans ?_ (by apply h1); clear h1
    apply repeatedAnd_subset_implies; grind


-- @@ L58-58 verbatim
local macro "replaceFun" : term => `((fun h => { h with pred := $(mkIdent `newHyp) }))


-- @@ L60-60 verbatim
section


-- @@ L62-63 verbatim
variable {σ : Type u} {hyps hyps' : List (NamedPred σ)} {goal : pred σ} {newHyp : pred σ}
  (idx : Nat) (h : ModifyHypSpecWithIndex hyps hyps' replaceFun idx)


-- @@ L65-79 expanded
include h in
private theorem Entails_specializeHyp_aux (subHyps : List (pred σ))
    (hinc : subHyps ⊆ hyps.map NamedPred.pred) :
    TLA.predImplies (repeatedAnd subHyps) newHyp → Entails hyps' goal → Entails hyps goal :=
  by
  intro h1 h2
  rcases h with rfl | ⟨hidx, rfl⟩
  · exact h2
  apply Entails_add_new (newHypName := (hyps[idx]'hidx).name)
  · exact hinc
  · exact h1
  unfold Entails
  have htmp2 := repeatedAnd_modifyHyp_reorder hyps _ hidx fun ⟨name, _⟩ => NamedPred.mk name newHyp
  dsimp only at htmp2
  simp only [List.map_append, repeatedAnd_append, List.map_singleton, repeatedAnd_singleton, htmp2]
  apply impl_drop_hyp_one_r; exact h2


-- @@ L81-81 verbatim
variable (hidx : idx < hyps.length) (hhyps' : hyps' = hyps.modify idx replaceFun)

-- @@ L82-82 verbatim
include hidx hhyps'


-- @@ L84-89 expanded
private theorem Entails_specialize_forall_aux {α : Sort v} {p : α → pred σ} (witness : α)
    (heq : newHyp = p witness) (hpred : (hyps[idx]'hidx).pred = tlaForall p) :
    Entails hyps' goal → Entails hyps goal :=
  by
  apply
    Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps :=
      [TLA.tlaForall p])
  · grind
  · simp [repeatedAnd_singleton]; (simp [tlasimp_def] at *); subst newHyp; grind


-- @@ L91-96 expanded
private theorem Entails_specialize_pure_aux {rhs : pred σ} {q : Prop} (hq : q) (heq : newHyp = rhs)
    (hpred : (hyps[idx]'hidx).pred = TLA.tlaImplies (TLA.purePred q) rhs) :
    Entails hyps' goal → Entails hyps goal :=
  by
  apply
    Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps :=
      [TLA.tlaImplies (TLA.purePred q) rhs])
  · grind
  · simp [repeatedAnd_singleton]; (simp [tlasimp_def] at *); grind


-- @@ L98-103 expanded
private theorem Entails_specialize_valid_aux {lhs rhs : pred σ} (hlhs : TLA.valid lhs)
    (heq : newHyp = rhs) (hpred : (hyps[idx]'hidx).pred = TLA.tlaImplies lhs rhs) :
    Entails hyps' goal → Entails hyps goal :=
  by
  apply
    Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps :=
      [TLA.tlaImplies lhs rhs])
  · grind
  · subst newHyp; simp [repeatedAnd_singleton]; revert hlhs; (simp [tlasimp_def] at *); grind


-- @@ L105-111 expanded
private theorem Entails_specialize_temporal_aux {rhs : pred σ} (lhss : List (pred σ))
    (hin : lhss ⊆ hyps.map NamedPred.pred) (heq : newHyp = rhs)
    (hpred : (hyps[idx]'hidx).pred = TLA.tlaImplies (repeatedAnd lhss) rhs) :
    Entails hyps' goal → Entails hyps goal :=
  by
  apply
    Entails_specializeHyp_aux idx (by right; constructor <;> assumption) (subHyps :=
      TLA.tlaImplies (repeatedAnd lhss) rhs :: lhss)
  · grind
  · rw [repeatedAnd_cons]; (simp [tlasimp_def] at *); grind


-- @@ L113-113 verbatim
end


-- @@ L115-117 verbatim
/-- Replace the chosen hypothesis predicate with a new one. -/
def replaceChosenPred {σ : Type u} (hyps : List (NamedPred σ)) (chosen : String) (newHyp : pred σ) :=
  modifyHypByName hyps chosen replaceFun


-- @@ L119-119 verbatim
section


-- @@ L121-121 verbatim
variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}


-- @@ L123-123 verbatim
section


-- @@ L125-125 verbatim
variable {α : Sort v} {p : α → pred σ} (witness : α)


-- @@ L127-132 verbatim
theorem Entails_specialize_forall_by_name (chosen : String)
  (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, TLA.tlaForall p⟩) :
  Entails (replaceChosenPred hyps chosen (p witness)) goal → Entails hyps goal := by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_forall_aux _ hidx rfl _ rfl (by grind)


-- @@ L134-139 verbatim
theorem Entails_specialize_forall_by_idx (idx : Nat)
  (hpred : hyps[idx]?.map NamedPred.pred = some (TLA.tlaForall p)) :
  Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, p witness⟩)) goal → Entails hyps goal := by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_forall_aux _ hidx rfl _ rfl (by grind)


-- @@ L141-141 verbatim
end


-- @@ L143-143 verbatim
section


-- @@ L145-145 verbatim
variable {rhs : pred σ} {q : Prop} (hq : q)

-- @@ L146-146 verbatim
include hq


-- @@ L148-153 expanded
theorem Entails_specialize_pure_by_name (chosen : String)
    (hpred :
      hyps.find? (fun h => h.name == chosen) = some ⟨chosen, TLA.tlaImplies (TLA.purePred q) rhs⟩) :
    Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal :=
  by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_pure_aux _ hidx rfl hq rfl (by grind)


-- @@ L155-160 expanded
theorem Entails_specialize_pure_by_idx (idx : Nat)
    (hpred : hyps[idx]?.map NamedPred.pred = some (TLA.tlaImplies (TLA.purePred q) rhs)) :
    Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal :=
  by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_pure_aux _ hidx rfl hq rfl (by grind)


-- @@ L162-162 verbatim
end


-- @@ L164-164 verbatim
section


-- @@ L166-166 verbatim
variable {lhs rhs : pred σ} (hlhs : TLA.valid lhs)

-- @@ L167-167 verbatim
include hlhs


-- @@ L169-174 expanded
theorem Entails_specialize_valid_by_name (chosen : String)
    (hpred : hyps.find? (fun h => h.name == chosen) = some ⟨chosen, TLA.tlaImplies lhs rhs⟩) :
    Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal :=
  by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_valid_aux _ hidx rfl hlhs rfl (by grind)


-- @@ L176-181 expanded
theorem Entails_specialize_valid_by_idx (idx : Nat)
    (hpred : hyps[idx]?.map NamedPred.pred = some (TLA.tlaImplies lhs rhs)) :
    Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal :=
  by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_valid_aux _ hidx rfl hlhs rfl (by grind)


-- @@ L183-183 verbatim
end


-- @@ L185-185 verbatim
section


-- @@ L187-189 verbatim
variable {rhs : pred σ} {lhss : List (pred σ)} (premises : List String)
  -- (hprem : hyps.find? (fun h => h.name == premise) = some ⟨premise, lhs⟩)
  (hprem : premises.filterMap (fun premise => hyps.find? (fun h => h.name == premise) |>.map NamedPred.pred) = lhss)

-- @@ L190-190 verbatim
include hprem


-- @@ L192-198 expanded
theorem Entails_specialize_temporal_by_name (chosen : String)
    (hpred :
      hyps.find? (fun h => h.name == chosen) =
        some ⟨chosen, TLA.tlaImplies (repeatedAnd lhss) rhs⟩) :
    Entails (replaceChosenPred hyps chosen rhs) goal → Entails hyps goal :=
  by
  obtain ⟨ht, ⟨idx, hidx, heq1, heq2⟩⟩ := List.findFindIdx hpred
  unfold replaceChosenPred modifyHypByName; rw [heq2]; dsimp
  apply Entails_specialize_temporal_aux _ hidx rfl lhss ?_ rfl (by grind)
  subst lhss; rw [← List.map_filterMap]; clear hpred ht heq1 heq2; grind


-- @@ L200-206 expanded
theorem Entails_specialize_temporal_by_idx (idx : Nat)
    (hpred : hyps[idx]?.map NamedPred.pred = some (TLA.tlaImplies (repeatedAnd lhss) rhs)) :
    Entails (hyps.modify idx (fun ⟨name, _⟩ => ⟨name, rhs⟩)) goal → Entails hyps goal :=
  by
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hpred
  rcases hpred with ⟨_, ⟨hidx, rfl⟩, heq⟩
  apply Entails_specialize_temporal_aux _ hidx rfl lhss ?_ rfl (by grind)
  subst lhss; rw [← List.map_filterMap]; clear heq; grind


-- @@ L208-208 verbatim
end


-- @@ L210-210 verbatim
end


-- @@ L212-215 verbatim
private meta def specializeTacDSimps := #[``replaceChosenPred, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go,
  ``String.reduceBEq, ``String.reduceBNe, ``dreduceIte, ``Option.elim,
  ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx, ``List.modifyTailIdx.go,
  ``List.modifyHead]


-- @@ L217-259 verbatim
/-- Specialize one temporal hypothesis once, then simplify the reflected
hypothesis list back to the literal proof-mode context. Callers build repeated
specialization by invoking this after each argument, so each step sees the
predicate produced by the previous step. -/
meta def tlaSpecializeStep (pos : TemporalHypLoc) (arg : TSyntax `term) : TacticM Unit := withMainContext do
  -- FIXME: Repetitively running `recognizeEntailsHypsFromGoal` and `find?` on it
  -- might be slow in some extreme cases?
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | throwError "tla_specialize: failed to read the hypotheses from the goal"
  let (_, pred) ← findByTemporalHypLoc hyps pos "tla_specialize" "the goal's Entails list"
  match_expr pred with
  | TLA.tlaForall _ _ _ =>
    let thm := if pos matches .byName .. then ``Entails_specialize_forall_by_name else ``Entails_specialize_forall_by_idx
    evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_)
  | TLA.tlaImplies _ lhs _ =>
    if lhs.isAppOfArity' ``TLA.purePred 2 then
      -- Treat `arg` as a Lean term
      let thm := if pos matches .byName .. then ``Entails_specialize_pure_by_name else ``Entails_specialize_pure_by_idx
      evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_)
    else
      (do
        let thm := if pos matches .byName .. then ``Entails_specialize_valid_by_name else ``Entails_specialize_valid_by_idx
        evalTactic <| ← `(tactic| refine $(mkIdent thm) $arg ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_))
      <|>
      (do
        let premises ← match arg with
          | `(term| ⟨ $args:term,* ⟩) => pure args.getElems.toList
          | _ => pure [arg]
        let premises ← premises.mapM fun arg => do
          match (← termIdentOpt arg) with
          | some id => pure <| toString id.getId
          | _ => throwError "tla_specialize: implication arguments must be a tuple or a single identifier; got {arg}"
        for premise in premises do
          unless hyps.any (fun ⟨name, _⟩ => name == premise) do
            throwError "tla_specialize: temporal hypothesis '{premise}' not found in the goal's Entails list"
        let thm := if pos matches .byName .. then ``Entails_specialize_temporal_by_name else ``Entails_specialize_temporal_by_idx
        evalTactic <| ← `(tactic| refine $(mkIdent thm) ($(quote premises)) (by rfl) ($(quoteTemporalHypLocToTerm pos)) (by rfl) ?_))
  | _ => throwError (specializeTargetBadShapeMsg pred pos)
  postDSimpAfterApplyingReflectionTheorem specializeTacDSimps
where
  /-- Error message for a specialize target of an unsupported shape. -/
  specializeTargetBadShapeMsg (pred : Expr) : TemporalHypLoc → MessageData
    | .byName name => m!"tla_specialize: hypothesis '{name}' is not a ∀ or implication; got {pred}"
    | .byIdx idx => m!"tla_specialize: hypothesis index {idx} is not a ∀ or implication; got {pred}"


-- @@ L261-277 verbatim
/--
`tla_specialize h arg₁ arg₂ ...` specializes a proof-mode temporal hypothesis
in place.

If `h : ∀ n, P n`, then
```lean
tla_specialize h 0
```
changes `h` to `P 0`. If `h : p → q` and `hp : p` is a temporal hypothesis,
then
```lean
tla_specialize h hp
```
changes `h` to `q` and keeps `hp` in the context. Numeric hypothesis indices
may be used in place of names.
-/
syntax (name := tlaSpecializeTac) "tla_specialize" (ppSpace colGt temporalHypLoc) (ppSpace colGt term:arg)+ : tactic


-- @@ L279-283 verbatim
elab_rules : tactic
  | `(tactic| tla_specialize $h:temporalHypLoc $[$args:term]*) => do
    let pos ← parseTemporalHypLoc h "tla_specialize: invalid syntax for specialization position"
    for arg in args do
      tlaSpecializeStep pos arg


-- @@ L285-285 verbatim
end TLA.ProofMode
