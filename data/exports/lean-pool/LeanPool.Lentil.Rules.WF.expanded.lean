/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
import Batteries.Tactic.Init
import LeanPool.Lentil.Gadgets.TheoremDeriving
import LeanPool.Lentil.ProofMode.Tactics.Apply
import LeanPool.Lentil.ProofMode.Tactics.RCases
import LeanPool.Lentil.ProofMode.Tactics.SplitAnds
import LeanPool.Lentil.ProofMode.Tactics.Start
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Util
import Std.Tactic.BVDecide.Normalize.Prop


-- @@ L21-21 verbatim
/-! Theorems about weak-fairness. -/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open Classical


-- @@ L27-27 verbatim
namespace TLA


-- @@ L29-29 verbatim
section wf


-- @@ L31-31 verbatim
variable {σ : Type u}


-- @@ L33-33 verbatim
section wf_def


-- @@ L35-35 verbatim
variable {a : action σ}


-- @@ L37-37 expanded
theorem wf_as_leads_to :
    TLA.weakFairness a = TLA.leadsTo (TLA.always (TLA.tlaEnabled a)) (TLA.actionPred a) :=
  rfl


-- @@ L39-41 expanded
theorem wf_alt1 :
    TLA.weakFairness a =
      TLA.always
        (TLA.eventually
          (TLA.tlaOr (TLA.tlaNot (TLA.tlaEnabled a))
            (TLA.always (TLA.eventually (TLA.actionPred a))))) :=
  by
  funext e; unfold weakFairness; rw [implies_to_or]; simp [tlasimp]
  rw [← eventually_or]; (repeat rw [always_eventually_or_distrib]); simp [tlasimp]


-- @@ L43-44 expanded
theorem wf_alt1' :
    TLA.weakFairness a =
      TLA.always (TLA.eventually (TLA.tlaOr (TLA.tlaNot (TLA.tlaEnabled a)) (TLA.actionPred a))) :=
  by rw [wf_alt1]; (repeat rw [always_eventually_or_distrib]); simp [tlasimp]


-- @@ L46-46 verbatim
end wf_def


-- @@ L48-82 expanded
/-- A useful rule for proving `↝`. Compared with its original presentation in
the paper "The Temporal Logic of Actions", the following version contains
some changes to make it hopefully more practical.
-/
@[tla_derive]
theorem wf1 (p q : pred σ) (next a : action σ) :
    TLA.predImplies
      (TLA.tlaAnd
        (TLA.alwaysImplies (TLA.tlaAnd p (TLA.actionPred next))
          (TLA.tlaOr (TLA.later p) (TLA.later q)))
        (TLA.tlaAnd
          (TLA.alwaysImplies (TLA.tlaAnd p (TLA.tlaAnd (TLA.actionPred next) (TLA.actionPred a)))
            (TLA.later q))
          (TLA.tlaAnd (TLA.alwaysImplies p (TLA.tlaOr (TLA.tlaEnabled a) q))
            (TLA.tlaAnd (TLA.always (TLA.actionPred next)) (TLA.weakFairness a)))))
      (TLA.leadsTo p q) :=
  by
  rw [wf_alt1']
  intro e ⟨hpuntilq, haq, henable, hnext, hwf_alt⟩ k hp
  specialize hwf_alt k;
  rcases hwf_alt with
    ⟨k1, hwf_alt⟩
      -- know that: either `q` holds between `k` and `k + k1`, or `p` holds at `k1`
        -- use `henable` to know that if it is the latter case, then `q` must hold in the next step
      
  have htmp : (∃ k' ≤ k1, q <| e.drop (k + k')) ∨ (p <| e.drop (k + k1)) :=
    by
    clear hwf_alt
    induction k1 with
    | zero => right; assumption
    | succ n ih => {
      rw [← Nat.add_assoc]
      rcases ih with ⟨k', hle, ih⟩ | ih
      · left; exists k'; constructor; omega; apply ih
      · specialize hpuntilq _ ⟨ih, (hnext _)⟩
        rcases hpuntilq with hq | hq <;>
          ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))
        · right; apply hq
        · left; exists (n + 1); aesop
    }
  rcases htmp with ⟨k', _, hq⟩ | hq <;> ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))
  · aesop
  · rcases hwf_alt with hq2 | hq2
    · specialize henable _ hq; aesop
    · exists (k1 + 1)
      specialize haq (k + k1) hq; rw [← Nat.add_assoc]; apply haq <;> aesop


-- @@ L84-98 expanded
/-- A (relatively) original presentation of the `wf1` rule. -/
theorem wf1_original (p q : pred σ) (next a : action σ) :
    TLA.predImplies
      (TLA.tlaAnd
        (TLA.alwaysImplies (TLA.tlaAnd p (TLA.actionPred next)) (TLA.later (TLA.tlaOr p q)))
        (TLA.tlaAnd
          (TLA.alwaysImplies (TLA.tlaAnd p (TLA.tlaAnd (TLA.actionPred next) (TLA.actionPred a)))
            (TLA.later q))
          (TLA.alwaysImplies p (TLA.tlaEnabled a))))
      (TLA.tlaImplies (TLA.tlaAnd (TLA.always (TLA.actionPred next)) (TLA.weakFairness a))
        (TLA.leadsTo p q)) :=
  by
  tla_start hpuntilq haq henable
  tla_rintro ⟨hnext, hfair⟩
  tla_apply wf1 (next := next) (a := a)
  (simp only [TLA.ProofMode.Entails_and_split]; split_ands)
  · rw [later_or]; tla_apply hpuntilq
  · tla_apply haq
  · intro e ⟨_, _, henable, _⟩ k hp
    exact Or.inl (henable k hp)
  · tla_apply hnext
  · tla_apply hfair


-- @@ L100-100 verbatim
end wf


-- @@ L102-102 verbatim
end TLA
