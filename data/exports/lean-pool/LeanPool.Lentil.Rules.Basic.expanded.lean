/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
import LeanPool.Lentil.Gadgets.TheoremLifting
import LeanPool.Lentil.Util
import LeanPool.Lentil.Utils.MiscLemmas
import Std.Tactic.BVDecide.Normalize.Prop


-- @@ L16-16 verbatim
/-! Basic theorems about TLA. -/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-24 verbatim
open Classical LentilLib

-- lift a bunch of proplemmas first

-- `And`

-- @@ L25-25 verbatim
#tla_lift and_self_iff and_not_self_iff not_and_self_iff and_comm and_assoc

-- @@ L26-26 verbatim
#tla_lift And.left => TLA.and_left

-- @@ L27-27 verbatim
#tla_lift And.right => TLA.and_right

-- @@ L28-28 verbatim
#tla_lift And.imp_left => TLA.and_imp_left

-- @@ L29-29 verbatim
#tla_lift And.imp_right => TLA.and_imp_right

-- @@ L30-30 verbatim
#tla_lift And.imp => TLA.and_imp_both

-- @@ L31-35 verbatim
#tla_lift not_and_of_not_left not_and_of_not_right and_left_comm and_right_comm
  and_rotate and_and_and_comm and_and_left and_and_right
  and_imp

-- `Or`

-- @@ L36-37 verbatim
#tla_lift or_self_iff or_left_comm or_right_comm or_or_or_comm or_or_distrib_left
  or_or_distrib_right or_rotate or_comm or_assoc

-- @@ L38-38 verbatim
#tla_lift Or.inl => TLA.or_inl

-- @@ L39-39 verbatim
#tla_lift Or.inr => TLA.or_inr

-- @@ L40-42 verbatim
#tla_lift Or.elim => TLA.or_elim

-- distributive laws

-- @@ L43-45 verbatim
#tla_lift and_or_left or_and_right or_and_left and_or_right

-- `Not`

-- @@ L46-46 verbatim
#tla_lift not_and' not_or imp_false not_true

-- @@ L47-47 verbatim
#tla_lift not_and => TLA.not_and_to_imp

-- @@ L48-50 verbatim
#tla_lift not_false_iff => TLA.not_false

-- `∀`, `∃`

-- @@ L51-52 verbatim
#tla_lift not_exists forall_and exists_or exists_and_left exists_and_right
  forall_comm exists_comm

-- @@ L53-53 verbatim
#tla_lift Bool.forall_bool Bool.exists_bool'

-- @@ L54-56 verbatim
#tla_lift LentilLib.forall_unit LentilLib.exists_unit

-- `Decidable`, but we are in the classical setting

-- @@ L57-60 verbatim
#tla_lift Decidable.not_not Decidable.by_contra Decidable.not_imp_comm
  Decidable.not_imp_self Decidable.or_iff_not_imp_left
  Decidable.imp_iff_or_not Decidable.not_and_not_right
  Decidable.or_iff_not_not_and_not Decidable.and_iff_not_not_or_not

-- @@ L61-61 verbatim
#tla_lift Decidable.em => TLA.excluded_middle

-- @@ L62-62 verbatim
#tla_lift Decidable.not_and_iff_not_or_not => TLA.not_and

-- @@ L63-63 verbatim
#tla_lift Decidable.imp_iff_not_or => TLA.implies_to_or

-- @@ L64-64 verbatim
#tla_lift Decidable.not_imp_iff_and_not => TLA.not_implies_to_and

-- @@ L65-65 verbatim
#tla_lift Decidable.not_imp_not => TLA.contraposition_for_tla_implies


-- @@ L67-70 verbatim
#tla_lift LentilLib.Nat.find_min => TLA.find_min by {
  intro σ p n e
  apply LentilLib.Nat.find_min (p := fun n => p n e)
}


-- @@ L72-72 verbatim
namespace TLA


-- @@ L74-74 verbatim
section playground


-- @@ L76-76 verbatim
variable {σ : Type u}


-- @@ L78-79 expanded
theorem dual_lemma (p q : pred σ) : TLA.tlaNot p = TLA.tlaNot q → p = q := by unfold tlaNot;
  intro h; funext e; have := congrFun h e; aesop


-- @@ L81-82 expanded
theorem pred_eq_iff_iff (p q : pred σ) : p = q ↔ TLA.predImplies p q ∧ TLA.predImplies q p := by
  (simp [tlasimp_def] at *); exact ⟨by aesop, by intro h; funext e; aesop⟩


-- @@ L84-84 verbatim
section structural


-- @@ L86-86 expanded
theorem impl_intro (p q : pred σ) : TLA.valid (TLA.tlaImplies p q) = TLA.predImplies p q :=
  rfl


-- @@ L88-89 expanded
theorem impl_decouple (p q : pred σ) : TLA.valid (TLA.tlaImplies p q) → TLA.valid p → TLA.valid q :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L91-92 expanded
theorem and_pred_implies_split (Γ p q : pred σ) :
    TLA.predImplies Γ (TLA.tlaAnd p q) = (TLA.predImplies Γ p ∧ TLA.predImplies Γ q) := by
  (simp [tlasimp_def] at *); aesop


-- @@ L94-95 expanded
theorem valid_eq_true_implies (p : pred σ) : TLA.valid p = (TLA.predImplies TLA.tlaTrue p) := by
  (simp [tlasimp_def] at *)


-- @@ L97-98 expanded
theorem and_valid_split (p q : pred σ) : TLA.valid (TLA.tlaAnd p q) = (TLA.valid p ∧ TLA.valid q) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L100-101 expanded
theorem impl_intro_add_r (p q r : pred σ) :
    TLA.predImplies r (TLA.tlaImplies p q) = TLA.predImplies (TLA.tlaAnd r p) q := by
  (simp [tlasimp_def] at *)


-- @@ L103-104 expanded
theorem impl_drop_hyp (p q : pred σ) : TLA.valid q → TLA.predImplies p q := by
  (simp [tlasimp_def] at *); aesop


-- @@ L106-107 expanded
theorem impl_drop_hyp_one_r (p q r : pred σ) :
    TLA.predImplies p q → TLA.predImplies (TLA.tlaAnd p r) q := by (simp [tlasimp_def] at *); aesop


-- @@ L109-109 verbatim
end structural


-- @@ L111-111 verbatim
section one


-- @@ L113-115 verbatim
variable (p : pred σ)

-- FIXME: These should be automatically generated

-- @@ L116-116 expanded
theorem and_true (p : pred σ) : TLA.tlaAnd p TLA.tlaTrue = p := by funext e;
  ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L118-118 expanded
theorem true_and (p : pred σ) : TLA.tlaAnd TLA.tlaTrue p = p := by funext e;
  ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L120-120 expanded
theorem or_false (p : pred σ) : TLA.tlaOr p TLA.tlaFalse = p := by funext e;
  ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L122-122 expanded
theorem false_or (p : pred σ) : TLA.tlaOr TLA.tlaFalse p = p := by funext e;
  ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L124-124 expanded
theorem imp_true (p : pred σ) : TLA.tlaImplies p TLA.tlaTrue = TLA.tlaTrue := by funext e;
  ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L126-128 expanded
theorem always_true :
    letI lhs : pred σ := TLA.always TLA.tlaTrue
    lhs = TLA.tlaTrue :=
  by funext e; ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L130-132 expanded
theorem eventually_true :
    letI lhs : pred σ := TLA.eventually TLA.tlaTrue
    lhs = TLA.tlaTrue :=
  by funext e; ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L134-136 expanded
theorem later_true :
    letI lhs : pred σ := TLA.later TLA.tlaTrue
    lhs = TLA.tlaTrue :=
  by funext e; ((simp [tlasimp_def] at *); (try simp only [execsimp] at *))


-- @@ L138-139 expanded
theorem always_intro : (TLA.valid p) = (TLA.valid (TLA.always p)) := by (simp [tlasimp_def] at *);
  exact ⟨by aesop, fun h e => h e 0⟩


-- @@ L141-143 expanded
theorem later_always_comm : TLA.later (TLA.always p) = TLA.always (TLA.later p) :=
  by
  funext e; (simp [tlasimp_def] at *)
  constructor <;> intro h k <;> rw [Nat.add_comm] <;> apply h


-- @@ L145-152 expanded
theorem always_unroll : TLA.always p = TLA.tlaAnd p (TLA.later (TLA.always p)) :=
  by
  rw [later_always_comm]
  funext e; (simp [tlasimp_def] at *)
  constructor
  · intro h; apply And.intro (h 0) (by aesop)
  · intro ⟨h0, hs⟩ k;
    cases k with
    | zero => exact h0
    | succ k => apply hs


-- @@ L154-158 expanded
theorem always_induction :
    TLA.always p = TLA.tlaAnd p (TLA.always (TLA.tlaImplies p (TLA.later p))) :=
  by
  funext e; (simp [tlasimp_def] at *)
  constructor
  · intro h; apply And.intro (h 0) (by aesop)
  · intro ⟨h0, hs⟩ k; induction k <;> aesop


-- @@ L160-161 expanded
theorem always_weaken : TLA.predImplies (TLA.always p) p := by (simp [tlasimp_def] at *); intro e h;
  apply h 0


-- @@ L163-164 expanded
theorem always_weaken_to_eventually : TLA.predImplies (TLA.always p) (TLA.eventually p) := by
  (simp [tlasimp_def] at *); intro e h; exists 0; apply h


-- @@ L166-167 expanded
theorem later_weaken_to_eventually : TLA.predImplies (TLA.later p) (TLA.eventually p) := by
  (simp [tlasimp_def] at *); intro e h; exists 1


-- @@ L169-170 expanded
theorem now_weaken_to_eventually : TLA.predImplies p (TLA.eventually p) := by
  (simp [tlasimp_def] at *); intro e h; exists 0


-- @@ L172-173 expanded
theorem not_always : TLA.tlaNot (TLA.always p) = TLA.eventually (TLA.tlaNot p) := by funext e;
  (simp [tlasimp_def] at *)


-- @@ L175-177 expanded
@[tladual]
theorem not_eventually : TLA.tlaNot (TLA.eventually p) = TLA.always (TLA.tlaNot p) := by funext e;
  (simp [tlasimp_def] at *)


-- @@ L179-180 expanded
theorem eventually_to_always : TLA.eventually p = TLA.tlaNot (TLA.always (TLA.tlaNot p)) := by
  funext e; (simp [tlasimp_def] at *)


-- @@ L182-184 expanded
@[tladual]
theorem always_to_eventually : TLA.always p = TLA.tlaNot (TLA.eventually (TLA.tlaNot p)) := by
  funext e; (simp [tlasimp_def] at *)


-- @@ L186-190 expanded
theorem always_idem : TLA.always (TLA.always p) = TLA.always p :=
  by
  funext e; (simp [tlasimp_def] at *)
  constructor <;> intro h
  · intro k; apply h _ 0
  · intros; apply h


-- @@ L192-194 expanded
@[tladual]
theorem eventually_idem : TLA.eventually (TLA.eventually p) = TLA.eventually p := by
  apply dual_lemma; simp [not_eventually, always_idem]


-- @@ L196-201 expanded
theorem always_eventually_always :
    TLA.always (TLA.eventually (TLA.always p)) = TLA.eventually (TLA.always p) :=
  by
  funext e; ext; constructor
  · apply always_weaken
  (simp [tlasimp_def] at *); intro kk h k; exists kk; intros k2
  have hq : k + kk + k2 = kk + (k + k2) := by omega
  rw [hq]; apply h


-- @@ L203-205 expanded
@[tladual]
theorem eventually_always_eventually :
    TLA.eventually (TLA.always (TLA.eventually p)) = TLA.always (TLA.eventually p) := by
  apply dual_lemma; simp [not_eventually, not_always, always_eventually_always]


-- @@ L207-208 expanded
theorem always_eventually_idem :
    TLA.always (TLA.eventually (TLA.always (TLA.eventually p))) = TLA.always (TLA.eventually p) :=
  by simp [eventually_always_eventually, always_idem]


-- @@ L210-212 expanded
@[tladual]
theorem eventually_always_idem :
    TLA.eventually (TLA.always (TLA.eventually (TLA.always p))) = TLA.eventually (TLA.always p) :=
  by simp [always_eventually_always, eventually_idem]


-- @@ L214-214 verbatim
end one


-- @@ L216-218 verbatim
attribute [tlasimp] not_not not_always not_eventually always_idem eventually_idem
  always_eventually_always eventually_always_eventually
  always_eventually_idem eventually_always_idem


-- @@ L220-220 verbatim
section two


-- @@ L222-222 verbatim
variable (p q : pred σ)


-- @@ L224-225 expanded
theorem contraposition_for_pred_implies :
    TLA.predImplies p q = (TLA.predImplies (TLA.tlaNot q) (TLA.tlaNot p)) := by
  repeat rw [← impl_intro, ← contraposition_for_tla_implies]


-- @@ L227-228 expanded
theorem proof_by_contra :
    TLA.predImplies p q = TLA.predImplies (TLA.tlaAnd (TLA.tlaNot q) p) TLA.tlaFalse := by
  rw [contraposition_for_pred_implies]; (simp [tlasimp_def] at *)


-- @@ L230-231 expanded
theorem modus_ponens : TLA.predImplies (TLA.tlaAnd p (TLA.tlaImplies p q)) q := by
  (simp [tlasimp_def] at *); aesop


-- @@ L233-236 expanded
theorem modus_ponens_with_premise :
    TLA.predImplies (TLA.tlaAnd p (TLA.tlaImplies p q)) (TLA.tlaAnd p q) := by
  (simp [tlasimp_def] at *);
  aesop
    -- the following: about modal operators


-- @@ L238-241 expanded
theorem always_pred_implies :
    (TLA.predImplies (TLA.always p) q) = (TLA.predImplies (TLA.always p) (TLA.always q)) :=
  by
  (simp [tlasimp_def] at *); constructor
  · intro h e hp k; apply h; (simp [tlasimp_def] at *); grind
  · intro h e hp; exact h _ hp 0


-- @@ L243-244 expanded
theorem always_and_eventually :
    TLA.predImplies (TLA.tlaAnd (TLA.eventually p) (TLA.always q))
      (TLA.eventually (TLA.tlaAnd p q)) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L246-247 expanded
theorem always_and_eventually' :
    TLA.predImplies (TLA.tlaAnd (TLA.eventually p) (TLA.always q))
      (TLA.eventually (TLA.tlaAnd p (TLA.always q))) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L249-250 expanded
theorem later_monotone : TLA.predImplies p q → TLA.predImplies (TLA.later p) (TLA.later q) := by
  (simp [tlasimp_def] at *); aesop


-- @@ L252-253 expanded
theorem always_monotone : TLA.predImplies p q → TLA.predImplies (TLA.always p) (TLA.always q) := by
  (simp [tlasimp_def] at *); aesop


-- @@ L255-256 expanded
theorem eventually_monotone :
    TLA.predImplies p q → TLA.predImplies (TLA.eventually p) (TLA.eventually q) := by
  (simp [tlasimp_def] at *); aesop


-- @@ L258-259 expanded
theorem always_eventually_monotone :
    TLA.predImplies p q →
      TLA.predImplies (TLA.always (TLA.eventually p)) (TLA.always (TLA.eventually q)) :=
  by intro h; apply always_monotone; apply eventually_monotone; assumption


-- @@ L261-262 expanded
theorem eventually_always_monotone :
    TLA.predImplies p q →
      TLA.predImplies (TLA.eventually (TLA.always p)) (TLA.eventually (TLA.always q)) :=
  by intro h; apply eventually_monotone; apply always_monotone; assumption


-- @@ L264-279 expanded
theorem until_induction :
    TLA.predImplies
      (TLA.tlaAnd p (TLA.always (TLA.tlaImplies (TLA.tlaAnd p (TLA.tlaNot q)) (TLA.later p))))
      (TLA.tlaOr (TLA.always (TLA.tlaAnd p (TLA.tlaNot q))) (TLA.tlaUntil p (TLA.tlaAnd p q))) :=
  by
  (simp [tlasimp_def] at *); intro e hp h
  by_cases h' : (∃ n, q <| e.drop n)
  · rcases h' with ⟨n', h'⟩
    have ⟨n', _, hq, hmin⟩ := Nat.find_min (p := fun n_ => q (exec.drop n_ e)) _ h'
    right; exists n'
    suffices hthis : q (exec.drop n' e) ∧ ∀ (j : Nat), j ≤ n' → p (exec.drop j e)
      by
      rcases hthis with ⟨h1, h2⟩
      apply And.intro (And.intro (by apply h2 n' (by simp)) h1) (fun j hlt => h2 _ (by omega))
    apply And.intro hq; intro j hlt
    induction j with
    | zero => exact hp
    | succ j ih => apply h; apply ih; omega; apply hmin; omega
  · simp at h'
    left; intro j; apply And.intro _ (h' _)
    induction j <;> solve_by_elim


-- @@ L281-281 verbatim
end two


-- @@ L283-283 verbatim
section two_with_quantifiers


-- @@ L285-285 verbatim
variable {α : Sort v} (p : α → pred σ)


-- @@ L287-288 expanded
theorem later_forall :
    TLA.later (TLA.tlaForall fun x => (p x)) = TLA.tlaForall fun x => TLA.later (p x) := by
  funext e; (simp [tlasimp_def] at *)


-- @@ L290-291 expanded
theorem later_exists :
    TLA.later (TLA.tlaExists fun x => (p x)) = TLA.tlaExists fun x => TLA.later (p x) := by
  funext e; (simp [tlasimp_def] at *)


-- @@ L293-294 expanded
theorem always_forall :
    TLA.always (TLA.tlaForall fun x => (p x)) = TLA.tlaForall fun x => TLA.always (p x) := by
  funext e; (simp [tlasimp_def] at *); aesop


-- @@ L296-297 expanded
theorem eventually_exists :
    TLA.eventually (TLA.tlaExists fun x => (p x)) = TLA.tlaExists fun x => TLA.eventually (p x) :=
  by funext e; (simp [tlasimp_def] at *); aesop


-- @@ L299-301 expanded
/-- uni-direction, moving `∃` into `□` -/
theorem exists_into_always :
    TLA.predImplies (TLA.tlaExists fun x => TLA.always (p x))
      (TLA.always (TLA.tlaExists fun x => (p x))) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L303-306 expanded
/-- uni-direction, moving `◇` into `∀` -/
@[tladual]
theorem eventually_into_forall :
    TLA.predImplies (TLA.eventually (TLA.tlaForall fun x => (p x)))
      (TLA.tlaForall fun x => TLA.eventually (p x)) :=
  by (simp [tlasimp_def] at *); aesop


-- @@ L308-308 verbatim
end two_with_quantifiers


-- @@ L310-310 verbatim
section two'


-- @@ L312-315 verbatim
variable (p q : pred σ)

/- NOTE: in principle we can derive the following via metaprogramming,
   but these proofs are so short, so why bother ... -/

-- @@ L316-317 expanded
theorem later_and : TLA.later (TLA.tlaAnd p q) = TLA.tlaAnd (TLA.later p) (TLA.later q) := by
  funext e; (simp [tlasimp_def] at *)


-- @@ L319-320 expanded
theorem later_or : TLA.later (TLA.tlaOr p q) = TLA.tlaOr (TLA.later p) (TLA.later q) := by funext e;
  (simp [tlasimp_def] at *)


-- @@ L322-323 expanded
theorem always_and : TLA.always (TLA.tlaAnd p q) = TLA.tlaAnd (TLA.always p) (TLA.always q) := by
  funext e; (simp [tlasimp_def] at *); aesop


-- @@ L325-327 expanded
@[tladual]
theorem eventually_or :
    TLA.eventually (TLA.tlaOr p q) = TLA.tlaOr (TLA.eventually p) (TLA.eventually q) := by funext e;
  (simp [tlasimp_def] at *); aesop


-- @@ L329-331 expanded
/-- uni-direction, merging the `∨` outside `◇` in -/
theorem always_or_merge :
    TLA.predImplies (TLA.tlaOr (TLA.always p) (TLA.always q)) (TLA.always (TLA.tlaOr p q)) := by
  (simp [tlasimp_def] at *); aesop


-- @@ L333-338 expanded
/-- uni-direction, splitting the `∧` inside `◇` -/
@[tladual]
theorem eventually_and_split :
    TLA.predImplies (TLA.eventually (TLA.tlaAnd p q))
      (TLA.tlaAnd (TLA.eventually p) (TLA.eventually q)) :=
  by (simp [tlasimp_def] at *);
  aesop
    -- NOTE: this __DOES NOT__ apply if we change `∧` into `∀`, unless, e.g. `α` is finite!


-- @@ L339-347 expanded
theorem eventually_always_and_distrib :
    TLA.eventually (TLA.always (TLA.tlaAnd p q)) =
      TLA.tlaAnd (TLA.eventually (TLA.always p)) (TLA.eventually (TLA.always q)) :=
  by
  rw [pred_eq_iff_iff]; constructor
  · rw [always_and]; apply eventually_and_split
  (simp [tlasimp_def] at *); intro e n1 h1 n2 h2; exists (n1 + n2)
  intro k
  specialize h1 (n2 + k); specialize h2 (n1 + k)
  have hq1 : n1 + (n2 + k) = n1 + n2 + k := by omega
  have hq2 : n2 + (n1 + k) = n1 + n2 + k := by omega
  rw [hq1] at h1; rw [hq2] at h2; aesop


-- @@ L349-351 expanded
@[tladual]
theorem always_eventually_or_distrib :
    TLA.always (TLA.eventually (TLA.tlaOr p q)) =
      TLA.tlaOr (TLA.always (TLA.eventually p)) (TLA.always (TLA.eventually q)) :=
  by apply dual_lemma; simp [tlasimp, not_or, eventually_always_and_distrib]


-- @@ L353-353 verbatim
end two'


-- @@ L355-357 verbatim
end playground

-- FIXME: Better name

-- @@ L358-358 verbatim
section more


-- @@ L360-361 expanded
theorem forall_elim {α : Type u} {β : Sort v} {p : β → pred α} {Γ : pred α} :
    (∀ x, TLA.predImplies Γ (p x)) = (TLA.predImplies Γ (TLA.tlaForall fun x => (p x))) := by
  (simp [tlasimp_def] at *); grind


-- @@ L363-364 expanded
theorem exists_elim {α : Type u} {β : Sort v} {p : β → pred α} {Γ : pred α} (x : β) :
    (TLA.predImplies Γ (p x)) → (TLA.predImplies Γ (TLA.tlaExists fun x => (p x))) := by
  (simp [tlasimp_def] at *); grind


-- @@ L366-366 verbatim
end more


-- @@ L368-368 verbatim
section pure


-- @@ L370-370 expanded
theorem valid_pure {p : Prop} : p → @valid α (purePred p) := by (simp [tlasimp_def] at *); grind


-- @@ L372-372 expanded
theorem pred_implies_pure {p : Prop} : p → @predImplies α q (purePred p) := by
  (simp [tlasimp_def] at *); grind


-- @@ L374-375 expanded
theorem pure_fact_intro {α : Type u} {Γ p : pred α} {q : Prop} :
    (q → (TLA.predImplies Γ p)) = (TLA.predImplies Γ (TLA.tlaImplies (TLA.purePred q) p)) := by
  (simp [tlasimp_def] at *); grind


-- @@ L377-377 expanded
theorem pure_implies_to_forall {p : Prop} :
    TLA.tlaImplies (TLA.purePred p) q = TLA.tlaForall fun _x : p => q := by funext e;
  (simp [tlasimp_def] at *)


-- @@ L379-379 expanded
theorem pure_and_to_exists {p : Prop} :
    TLA.tlaAnd (TLA.purePred p) q = TLA.tlaExists fun _x : p => q := by funext e;
  (simp [tlasimp_def] at *)


-- @@ L381-381 verbatim
end pure


-- @@ L383-383 verbatim
end TLA
