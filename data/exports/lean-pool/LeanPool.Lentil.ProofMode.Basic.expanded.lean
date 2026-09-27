/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
public import LeanPool.Lentil.Utils.MiscLemmas
import Aesop.Frontend.Tactic
import Aesop.Main
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Rules.BigOp
import LeanPool.Lentil.Util
import Std.Tactic.BVDecide.Normalize.Prop


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace TLA.ProofMode


-- @@ L21-21 verbatim
open TLA LentilLib


-- @@ L23-30 verbatim
/-- A named proof-mode hypothesis. -/
structure NamedPred (σ : Type u) where
  /-- The hypothesis name. -/
  name : String
  /-- The hypothesis predicate. -/
  pred : pred σ

-- FIXME: How to unify this with `tlaBigwedge`?

-- @@ L31-32 verbatim
/-- Right-fold a list of predicates into a single conjunction. -/
def repeatedAnd (ps : List (pred σ)) : pred σ := (List.foldrD tlaAnd tlaTrue ps)


-- @@ L34-37 verbatim
/-- Right-fold a list of predicates into a chain of implications to `q`. -/
def repeatedImplies (ps : List (pred σ)) (q : pred σ) : pred σ := ps.foldr tlaImplies q

-- FIXME: This is not satisfactory ...

-- @@ L38-43 expanded
theorem repeatedAnd_eq_bigwedge (ps : List (pred σ)) :
    (repeatedAnd ps) = TLA.tlaBigwedge (fun x => x) ps :=
  by
  dsimp [tlaBigwedge, Foldable.fold]
  rw [← List.foldrD_eq_foldr]
  · rfl
  · apply and_true


-- @@ L45-47 expanded
theorem repeatedAnd_eq_in_iff (ps1 ps2 : List (pred σ)) (h : ∀ p, p ∈ ps1 ↔ p ∈ ps2) :
    (repeatedAnd ps1) = (repeatedAnd ps2) := by
  simp [repeatedAnd_eq_bigwedge, bigwedge_forall_list, h]


-- @@ L49-49 verbatim
theorem repeatedAnd_singleton (p : pred σ) : repeatedAnd [p] = p := rfl


-- @@ L51-53 expanded
theorem repeatedAnd_append (ps1 ps2 : List (pred σ)) :
    (repeatedAnd (ps1 ++ ps2)) = TLA.tlaAnd (repeatedAnd ps1) (repeatedAnd ps2) := by
  simp [repeatedAnd_eq_bigwedge, bigwedge_list_append]


-- @@ L55-57 expanded
theorem repeatedAnd_cons (p : pred σ) (ps : List (pred σ)) :
    (repeatedAnd (p :: ps)) = TLA.tlaAnd p (repeatedAnd ps) := by
  rw [← List.singleton_append, repeatedAnd_append]; rfl


-- @@ L59-62 expanded
theorem repeatedAnd_add_duplicate {ps : List (pred σ)} {p : pred σ} (h : p ∈ ps) :
    (repeatedAnd ps) = TLA.tlaAnd (repeatedAnd ps) p :=
  by
  simp [repeatedAnd_eq_bigwedge, bigwedge_forall_list]
  funext e; (simp [tlasimp_def] at *); grind


-- @@ L64-68 expanded
theorem repeatedAnd_subset_implies (ps1 ps2 : List (pred σ)) :
    ps1 ⊆ ps2 → TLA.predImplies (repeatedAnd ps2) (repeatedAnd ps1) :=
  by
  intro h; rw [List.subset_def] at h
  simp only [repeatedAnd_eq_bigwedge, bigwedge_forall_list]
  (simp [tla_nontemporal_def] at *); aesop


-- @@ L70-74 expanded
theorem repeatedImplies_apply {σ : Type u} {hs : List (pred σ)} {goal : pred σ} :
    TLA.predImplies (TLA.tlaAnd (repeatedAnd hs) (repeatedImplies hs goal)) goal := by
  induction hs with
  | nil => intro e ⟨h1, h2⟩; exact h2
  | cons p ps ih => rw [repeatedAnd_cons, repeatedImplies, List.foldr_cons];
    (simp [tlasimp_def] at *); aesop


-- @@ L76-78 verbatim
/-- The proof-mode entailment: the conjunction of hypotheses entails the goal. -/
def Entails (hyps : List (NamedPred σ)) (goal : pred σ) : Prop :=
  TLA.predImplies (repeatedAnd (hyps.map NamedPred.pred)) goal


-- @@ L80-88 expanded
theorem repeatedAnd_modifyHyp_reorder {σ : Type u} (hyps : List (NamedPred σ)) (idx : Nat)
    (h : idx < hyps.length) (f : NamedPred σ → NamedPred σ) :
    TLA.tlaAnd (repeatedAnd <| hyps.map NamedPred.pred) (f (hyps[idx]'h) |>.pred) =
      TLA.tlaAnd (repeatedAnd <| (hyps.modify idx f).map NamedPred.pred) (hyps[idx]'h |>.pred) :=
  by
  rw [← repeatedAnd_singleton hyps[idx].pred, ← repeatedAnd_singleton (f (hyps[idx]'h)).pred, ←
    repeatedAnd_append, ← repeatedAnd_append]
  apply repeatedAnd_eq_in_iff
  have htmp := List.Perm.map NamedPred.pred <| LentilLib.List.modify_perm h f
  simp at htmp; intro p; apply List.Perm.mem_iff; exact htmp


-- @@ L90-97 verbatim
theorem repeatedAnd_map_comm {σ : Type u} (hyps : List (pred σ)) (f : pred σ → pred σ)
  (htrue : tlaTrue = f tlaTrue)
  (h : ∀ (p q : pred σ), tlaAnd (f p) (f q) = f (tlaAnd p q)) :
  ((repeatedAnd (hyps.map f))) = (f (repeatedAnd hyps)) := by
  simp [repeatedAnd_eq_bigwedge]
  induction hyps with
  | nil => simp [bigwedge_list_nil]; exact htrue
  | cons p hyps ih => simp [bigwedge_list_cons, ih]; rw [h]


-- @@ L99-101 verbatim
/-- Specification relating a hypothesis list to its modification at a given index. -/
def ModifyHypSpecWithIndex (hyps hyps' : List (NamedPred σ)) (f : NamedPred σ → NamedPred σ) (idx : Nat) :=
  hyps = hyps' ∨ (idx < hyps.length ∧ hyps' = hyps.modify idx f)


-- @@ L103-108 verbatim
theorem ModifyHypSpecWithIndex_modify {σ : Type u} (hyps : List (NamedPred σ)) (f : NamedPred σ → NamedPred σ) (idx : Nat) :
  ModifyHypSpecWithIndex hyps (hyps.modify idx f) f idx := by
  unfold ModifyHypSpecWithIndex
  by_cases h : idx < hyps.length
  · grind
  · left; rw [List.modify_eq_self]; omega


-- @@ L110-112 verbatim
/-- Specification relating a hypothesis list to its modification at some index. -/
def ModifyHypSpec (hyps hyps' : List (NamedPred σ)) (f : NamedPred σ → NamedPred σ) :=
  hyps = hyps' ∨ ∃ (idx : Nat) (_ : idx < hyps.length), hyps' = hyps.modify idx f


-- @@ L114-119 verbatim
theorem ModifyHypSpecWithIndex_implies_ModifyHypSpec {hyps hyps' : List (NamedPred σ)}
    {f : NamedPred σ → NamedPred σ} {idx : Nat} :
  ModifyHypSpecWithIndex hyps hyps' f idx → ModifyHypSpec hyps hyps' f := by
  unfold ModifyHypSpecWithIndex ModifyHypSpec; grind

-- This is possible since `Nat` is inhabited

-- @@ L120-122 verbatim
theorem ModifyHypSpec_implies_ModifyHypSpecWithIndex {hyps hyps' : List (NamedPred σ)} {f : NamedPred σ → NamedPred σ} :
  ModifyHypSpec hyps hyps' f → ∃ idx, ModifyHypSpecWithIndex hyps hyps' f idx := by
  unfold ModifyHypSpecWithIndex ModifyHypSpec; aesop


-- @@ L124-128 verbatim
/-- Modify the hypothesis with the given name by applying `f`. -/
def modifyHypByName {σ : Type u} (hyps : List (NamedPred σ)) (name : String)
  (f : NamedPred σ → NamedPred σ) : List (NamedPred σ) :=
  letI idx? := hyps.findIdx? fun h => h.name == name
  idx?.elim hyps fun idx => hyps.modify idx f


-- @@ L130-138 verbatim
theorem modifyHypByName_spec {σ : Type u} (hyps : List (NamedPred σ)) (name : String)
  (f : NamedPred σ → NamedPred σ) :
  ModifyHypSpec hyps (modifyHypByName hyps name f) f := by
  unfold ModifyHypSpec modifyHypByName
  cases hidx : hyps.findIdx? (fun h => h.name == name) with
  | none => left; rfl
  | some idx =>
    dsimp only [Option.elim]
    rw [List.findIdx?_eq_some_iff_findIdx_eq] at hidx; grind


-- @@ L140-140 verbatim
open Lean Meta Elab Tactic


-- @@ L142-145 verbatim
/-- Like `Expr.isStringLit`, but returns the string. -/
def parseStringLitOpt : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none


-- @@ L147-149 verbatim
/-- Obtain a cleaned-up version of `e`. -/
def cleanupAnnotAndMore (e : Expr) : MetaM Expr := do
  pure (← instantiateMVars e).headBeta.cleanupAnnotations


-- @@ L151-162 verbatim
/-- Run `dsimp` with the reflection lemmas after applying a proof-mode theorem. -/
def postDSimpAfterApplyingReflectionTheorem (l : Array Name) : TacticM Unit := do
  let gs ← getGoals
  let gs' ← gs.mapM fun g => do
    let ty ← cleanupAnnotAndMore (← g.getType)
    if ty.isAppOfArity' ``Entails 3 then
      let simps := l.map Lean.mkIdent
      let [g'] ← evalTacticAt (← `(tactic| dsimp -$(mkIdent `failIfUnchanged) only [$[$simps:ident],*])) g
        | throwError "Unexpected number of goals after dsimp"
      pure g'
    else pure g
  setGoals gs'


-- @@ L164-176 verbatim
/-- Recognize a literal list of named hypotheses from an `Expr`. -/
def recognizeHypsList (hyps : Expr) : MetaM (Option (Expr × List (String × Expr))) := do
  let some (ty, hyps) := hyps.listLit? | return none
  let hyps ← hyps.foldrM (init := some []) fun hyp acc => do
    match acc with
    | none => pure none
    | some l =>
      let_expr TLA.ProofMode.NamedPred.mk _ nm pred := hyp
        | return none
      let some nameStr := parseStringLitOpt nm | return none
      pure <| some ((nameStr, pred) :: l)
  let some hyps := hyps | return none
  return some (ty, hyps)


-- @@ L178-181 verbatim
/-- Recognize the hypothesis list of an `Entails` goal `Expr`. -/
def recognizeEntailsHyps (e : Expr) : MetaM (Option (Expr × List (String × Expr))) := do
  let_expr TLA.ProofMode.Entails _ hyps _ := e | return none
  recognizeHypsList hyps


-- @@ L183-187 verbatim
/-- Recognize the hypothesis list of the current `Entails` goal. -/
def recognizeEntailsHypsFromGoal : TacticM (Option (Expr × List (String × Expr))) := do
  let g ← getMainTarget
  let g := g.headBeta.cleanupAnnotations    -- Since `getMainTarget` does `instantiateMVars`
  recognizeEntailsHyps g


-- @@ L189-192 verbatim
/-- Build the `Expr` of a literal list of named hypotheses. -/
def toHypsList (hypTy : Expr) (hyps : List (String × Expr)) : MetaM Expr := do
  let elems ← hyps.mapM fun (name, pred) => mkAppM ``TLA.ProofMode.NamedPred.mk #[toExpr name, pred]
  mkListLit hypTy elems


-- @@ L194-197 verbatim
/-- The number of hypotheses in the current proof-mode goal. -/
def goalHypsLength : TacticM (Option Nat) := do
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | return none
  return some hyps.length


-- @@ L199-199 verbatim
end TLA.ProofMode
