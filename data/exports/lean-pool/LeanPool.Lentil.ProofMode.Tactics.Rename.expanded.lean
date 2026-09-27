/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public meta import LeanPool.Lentil.ProofMode.Basic

public import LeanPool.Lentil.ProofMode.Location
public import LeanPool.Lentil.ProofMode.Basic
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.String


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace TLA.ProofMode


-- @@ L19-19 verbatim
open Lean Meta Elab Tactic


-- @@ L21-23 verbatim
/-- Change the displayed name of a hypothesis while retaining its predicate. -/
def renameFun {σ : Type u} (newName : String) (h : NamedPred σ) : NamedPred σ :=
  ⟨newName, h.pred⟩


-- @@ L25-25 verbatim
section


-- @@ L27-28 verbatim
variable {σ : Type u} {hyps hyps' : List (NamedPred σ)} {goal : pred σ} (newName : String)
  (idx : Nat) (h : ModifyHypSpecWithIndex hyps hyps' (renameFun newName) idx)

-- @@ L29-29 verbatim
include h


-- @@ L31-36 verbatim
private theorem renameHyp_pred_same : hyps'.map NamedPred.pred = hyps.map NamedPred.pred := by
  rcases h with rfl | ⟨hidx, rfl⟩
  · rfl
  rw [List.modify_eq_take_cons_drop hidx]
  conv => enter [2, 2]; rw [← LentilLib.List.take_getElem_drop hidx]
  simp only [List.map_append, List.map_take, List.map_cons, List.map_drop, renameFun]


-- @@ L38-39 verbatim
private theorem Entails_rename_aux : Entails hyps' goal = Entails hyps goal := by
  unfold Entails; congr 1; rw [renameHyp_pred_same newName idx h]


-- @@ L41-41 verbatim
end


-- @@ L43-45 verbatim
/-- Rename a hypothesis in a hypothesis list. -/
def renameHyp {σ : Type u} (hyps : List (NamedPred σ)) (oldName newName : String) :=
  modifyHypByName hyps oldName (renameFun newName)


-- @@ L47-47 verbatim
section


-- @@ L49-49 verbatim
variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ} (newName : String)


-- @@ L51-54 verbatim
theorem Entails_rename_by_name (oldName : String) :
  Entails (renameHyp hyps oldName newName) goal = Entails hyps goal := by
  obtain ⟨idx, hspec⟩ := ModifyHypSpec_implies_ModifyHypSpecWithIndex <| modifyHypByName_spec hyps oldName (renameFun newName)
  exact Entails_rename_aux newName idx hspec


-- @@ L56-57 verbatim
theorem Entails_rename_by_idx (idx : Nat) :
  Entails (hyps.modify idx (renameFun newName)) goal = Entails hyps goal := Entails_rename_aux newName idx (ModifyHypSpecWithIndex_modify _ _ _)


-- @@ L59-59 verbatim
end


-- @@ L61-64 verbatim
/-- Reduction rules used after renaming a proof-mode hypothesis. -/
meta def renameTacDSimps := #[``renameHyp, ``modifyHypByName, ``List.findIdx?, ``List.findIdx?.go, ``String.reduceBEq, ``String.reduceBNe,
    ``dreduceIte, ``Option.elim, ``Bool.false_eq_true, ``List.modify, ``List.modifyTailIdx,
    ``List.modifyTailIdx.go, ``List.modifyHead]


-- @@ L66-71 verbatim
/-- Rename the hypothesis at the given location. -/
meta def tlaRename (old : TemporalHypLoc) (newStr : String) : TacticM Unit := do
  let thm := if old matches .byName .. then ``Entails_rename_by_name else ``Entails_rename_by_idx
  evalTactic <| ← `(tactic|
    refine ($(mkIdent thm) ($(quote newStr)) ($(quoteTemporalHypLocToTerm old))).$(mkIdent `mp) ?_)
  postDSimpAfterApplyingReflectionTheorem renameTacDSimps


-- @@ L73-87 verbatim
/--
`tla_rename h => h'` renames a proof-mode temporal hypothesis. The predicate
and the hypothesis position are unchanged.

For example, if the context contains `hp : p`, then
```lean
tla_rename hp => hp'
```
changes the context entry to `hp' : p`. A numeric index can be used instead of
a name:
```lean
tla_rename 0 => hHead
```
-/
syntax (name := tlaRenameTac) "tla_rename" (ppSpace colGt temporalHypLoc) " => " ident : tactic


-- @@ L89-93 verbatim
elab_rules : tactic
  | `(tactic| tla_rename $old:temporalHypLoc => $new:ident) => do
    let old ← parseTemporalHypLoc old "tla_rename: invalid syntax for renaming position"
    let newStr := toString new.getId
    tlaRename old newStr


-- @@ L95-95 verbatim
end TLA.ProofMode
