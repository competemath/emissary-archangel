/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L11-11 verbatim
/-! # Disjunctive -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Entailment


-- @@ L19-19 verbatim
variable {F : Type*} [LogicalConnective F]

-- @@ L20-20 verbatim
variable {S : Type*} [Entailment F S]


-- @@ L22-24 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {φ ψ}, Provable 𝓢 (Vee.vee φ ψ) → Provable 𝓢 φ ∨ Provable 𝓢 ψ


-- @@ L26-26 verbatim
alias disjunctive := Disjunctive.disjunctive


-- @@ L28-29 expanded
lemma iff_disjunctive {𝓢 : S} :
    (Disjunctive 𝓢) ↔ ∀ {φ ψ}, Provable 𝓢 (Vee.vee φ ψ) → Provable 𝓢 φ ∨ Provable 𝓢 ψ :=
  ⟨fun h ↦ h.disjunctive, fun d ↦ ⟨d⟩⟩


-- @@ L31-43 expanded
lemma iff_complete_disjunctive {𝓢 : S} [Entailment.Classical 𝓢] :
    (Entailment.Complete 𝓢) ↔ (Disjunctive 𝓢) := by
  classical
  constructor;
  · intro hComp; apply iff_disjunctive.mpr; intro φ ψ hpq; rcases (hComp φ) with (hp | hnp);
    · left; assumption;
    · right; exact or₃'''! (efq_of_neg! hnp) imp_id! hpq;
  · intro hDisj φ;
    replace hDisj : ∀ {φ ψ}, Provable 𝓢 (Vee.vee φ ψ) → Provable 𝓢 φ ∨ Provable 𝓢 ψ :=
      iff_disjunctive.mp hDisj;
    exact @hDisj φ (Tilde.tilde φ) lem!;


-- @@ L45-45 verbatim
end Entailment

-- @@ L46-46 verbatim
end LO
