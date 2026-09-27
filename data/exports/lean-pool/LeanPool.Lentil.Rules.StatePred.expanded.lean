/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Tactics.FiniteWindow
import LeanPool.Lentil.Util


-- @@ L15-18 verbatim
/-! Theorems specialized for state predicates.
    Their premises are typically pure Lean propositions involving
    states before/after an action, instead of being in the form of
    `|-tla-`. -/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open Classical


-- @@ L24-24 verbatim
namespace TLA


-- @@ L26-26 verbatim
section state_pred_specialized


-- @@ L28-28 verbatim
variable {σ : Type u}


-- @@ L30-31 expanded
theorem state_preds_and (p q : σ → Prop) :
    TLA.tlaAnd (TLA.statePred p) (TLA.statePred q) = TLA.statePred λ s => p s ∧ q s := by funext e;
  (simp [tla_nontemporal_def] at *)


-- @@ L33-45 expanded
theorem init_invariant {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hinit : ∀ s, init s → inv s) (hnext : ∀ s s', next s s' → inv s → inv s') :
    TLA.predImplies (TLA.tlaAnd (TLA.statePred init) (TLA.always (TLA.actionPred next)))
      (TLA.always (TLA.statePred inv)) :=
  by
  have hstep :
    TLA.predImplies (TLA.tlaAnd (TLA.statePred inv) (TLA.actionPred next))
      (TLA.later (TLA.statePred inv)) :=
    by
    tlaFiniteWindow
    aesop
  rw (occs := .pos [2]) [always_induction]
  rw [and_pred_implies_split]; apply And.intro
  · intro e ⟨hinit', _⟩
    exact hinit _ hinit'
  · intro e ⟨_, hnext'⟩ k hinv
    exact hstep (e.drop k) ⟨hinv, hnext' k⟩


-- @@ L47-47 verbatim
end state_pred_specialized


-- @@ L49-49 verbatim
end TLA
