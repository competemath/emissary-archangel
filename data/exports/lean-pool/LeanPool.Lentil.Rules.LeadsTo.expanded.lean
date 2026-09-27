/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
import LeanPool.Lentil.Gadgets.TheoremDeriving
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Util


-- @@ L15-15 verbatim
/-! Theorems about the leads-to operator. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Classical


-- @@ L21-21 verbatim
namespace TLA


-- @@ L23-23 verbatim
section leadsTo


-- @@ L25-27 verbatim
variable {σ : Type u}

-- FIXME: any chance to make the following two lemmas more general

-- @@ L28-30 expanded
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
    (∀ (x : α), TLA.predImplies Γ (TLA.leadsTo (p x) q)) ↔
      TLA.predImplies Γ (TLA.leadsTo (tlaExists p) q) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L32-34 expanded
theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
    (φ → TLA.predImplies Γ (TLA.leadsTo p q)) ↔
      TLA.predImplies Γ (TLA.leadsTo (TLA.tlaAnd (TLA.purePred φ) p) q) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L36-40 expanded
@[tla_derive]
theorem leads_to_conseq (p p' q q' : pred σ) :
    TLA.valid
      (TLA.tlaImplies (TLA.alwaysImplies p' p)
        (TLA.tlaImplies (TLA.alwaysImplies q q')
          (TLA.alwaysImplies (TLA.leadsTo p q) (TLA.leadsTo p' q')))) :=
  by
  (simp [tlasimp_def] at *); intro e h1 h2 k h k' hh'
  specialize h _ (h1 _ hh'); rcases h with ⟨k1, h⟩; aesop


-- @@ L42-48 expanded
@[tla_derive]
theorem leads_to_trans (p q r : pred σ) :
    TLA.valid
      (TLA.tlaImplies (TLA.leadsTo p q) (TLA.tlaImplies (TLA.leadsTo q r) (TLA.leadsTo p r))) :=
  by
  (simp [tlasimp_def] at *); intro e h1 h2 k hh
  specialize h1 _ hh; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ h1; rcases h2 with ⟨k2, h2⟩
  exists (k1 + k2); rw [← Nat.add_assoc]; assumption


-- @@ L50-63 expanded
theorem leads_to_combine (Γ Γ' p1 q1 p2 q2 : pred σ)
    (h1 : TLA.predImplies (TLA.tlaAnd (TLA.always Γ) Γ') (TLA.leadsTo p1 q1))
    (h2 : TLA.predImplies (TLA.tlaAnd (TLA.always Γ) Γ') (TLA.leadsTo p2 q2))
    (h1' : TLA.predImplies (TLA.tlaAnd q1 (TLA.always Γ)) (TLA.always q1))
    (h2' : TLA.predImplies (TLA.tlaAnd q2 (TLA.always Γ)) (TLA.always q2)) :
    TLA.predImplies (TLA.tlaAnd (TLA.always Γ) Γ')
      (TLA.leadsTo (TLA.tlaAnd p1 p2) (TLA.tlaAnd q1 q2)) :=
  by
  -- a semantic proof
  
  (simp [tlasimp_def] at *); intro e hΓ hΓ' k hp1 hp2
  specialize h1 _ hΓ hΓ' k hp1; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ hΓ hΓ' k hp2; rcases h2 with ⟨k2, h2⟩
  exists k1 + k2
  specialize h1' _ h1 (by intro q; rw [exec.drop_drop]; apply hΓ) k2
  specialize h2' _ h2 (by intro q; rw [exec.drop_drop]; apply hΓ) k1
  simp [exec.drop_drop] at h1' h2'
  constructor; rw [← Nat.add_assoc]; assumption; rw [Nat.add_comm k1 k2, ← Nat.add_assoc];
  assumption


-- @@ L65-68 expanded
@[tla_derive]
theorem leads_to_strengthen_lhs (p q inv : pred σ) :
    TLA.valid
      (TLA.tlaImplies (TLA.always inv)
        (TLA.tlaImplies (TLA.leadsTo (TLA.tlaAnd p inv) q) (TLA.leadsTo p q))) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L70-70 verbatim
end leadsTo


-- @@ L72-72 verbatim
end TLA
