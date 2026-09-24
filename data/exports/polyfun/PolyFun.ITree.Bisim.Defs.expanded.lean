/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.ITree.Construct


-- @@ L10-64 verbatim
/-! # Bisimulation for Interaction Trees

This module defines the two equivalences on `ITree F α` used throughout the
algebraic theory:

* `ITree.Bisim t s` — *strong* (a.k.a. structural) bisimulation. Two ITrees
  are strongly bisimilar iff their one-step shapes match and the
  continuations are pointwise bisimilar. By the universal property of
  `PFunctor.M`, strong bisimulation coincides with Lean equality;
  for that reason we set `Bisim = (· = ·)`.

* `ITree.WeakBisimRel RR t s` — relational weak bisimulation (Coq `euttR`).
  The trees share an event signature, but their return types and universes are
  independent; pure leaves are compared by `RR`.

* `ITree.WeakBisim t s` — the equality-specialized weak bisimulation (Coq
  `eutt`). Two ITrees are
  weakly bisimilar iff, after stripping any *finitely many* leading `step`
  nodes from each side, their observable heads agree (pure leaves, visible
  queries, or paired silent steps) and continuations are pointwise weakly
  bisimilar. This is the intended notion of ITree equivalence for
  reasoning about programs.

## Design

The naive coinductive definition with `tauL` / `tauR` constructors
directly appearing in a coinductive predicate is **unsound**: it admits
`WeakBisim (pure r) diverge` via repeated `tauR` applications, because
the greatest fixed point closes under the (unbounded) coinductive
stripping. The fix follows Xia et al. (POPL 2020): wrap τ-stripping in
an *inductive* relation `TauSteps` (so each stripping chain is finite),
and let each coinductive "step" of `WeakBisim` consist of stripping
finitely many τ's from each side and then matching observable heads via
the `Match` functor.

We define `WeakBisimRel` as the Tarski greatest fixed point of the
one-step functor packaged by `TauSteps` + `MatchRel`, i.e. as the largest
relation `R` that is closed under the functor. This `∃ R, …` form is
used because Lean's `coinductive` keyword requires syntactic
monotonicity, which does not see through the separately-declared
`MatchRel` inductive.

## Implementation notes

Lean supports `coinductive` *predicates*, but the monotonicity
checker is syntactic. We therefore use the explicit Tarski formulation
`∃ R, R t s ∧ closure`. The coinduction principle is then the
constructor itself (`WeakBisimRel.coinduct`), and the standard algebraic
laws for the equality specialization are recovered by exhibiting an
appropriate witness relation `R` in each case.

All event-position, event-direction, and result universes are independent.
The two trees in `WeakBisimRel` deliberately share one event signature;
relating different signatures is the separate relational-simulation layer.
-/


-- @@ L66-66 verbatim
@[expose] public section


-- @@ L68-68 verbatim
universe uFA uFB uα uβ


-- @@ L70-70 verbatim
namespace ITree


-- @@ L72-72 verbatim
variable {F : PFunctor.{uFA, uFB}} {α : Type uα} {β : Type uβ}


-- @@ L74-74 verbatim
/-! ### Strong bisimulation -/


-- @@ L76-81 verbatim
/-- Strong bisimulation on interaction trees. Two ITrees are strongly
bisimilar iff they are equal as wrapped elements of
`PFunctor.M (ITree.Poly F α)`. By `ITree.bisim`, this is the same as having
matching `ViewPoly` one-step shapes with pointwise-bisimilar continuations. -/
@[reducible]
def Bisim (t s : ITree F α) : Prop := t = s


-- @@ L83-83 verbatim
@[inherit_doc] scoped infix:50 " ≅ " => ITree.Bisim


-- @@ L85-85 verbatim
namespace Bisim


-- @@ L87-87 verbatim
variable {t s u : ITree F α}


-- @@ L89-89 verbatim
@[refl] theorem refl' (t : ITree F α) : t ≅ t := rfl


-- @@ L91-91 verbatim
@[symm] theorem symm' (h : t ≅ s) : s ≅ t := Eq.symm h


-- @@ L93-93 verbatim
@[trans] theorem trans' (h₁ : t ≅ s) (h₂ : s ≅ u) : t ≅ u := Eq.trans h₁ h₂


-- @@ L95-98 verbatim
/-- One-step characterisation: two ITrees are strongly bisimilar iff their
`shape'` agrees. Provable by `ITree.bisim`. -/
theorem dest (h : t ≅ s) : shape' t = shape' s := by
  cases h; rfl


-- @@ L100-100 verbatim
end Bisim


-- @@ L102-106 verbatim
/-! ### Finite τ-stripping

`TauSteps t t'` captures the (deterministic, partial) operation of
stripping finitely many leading silent-step nodes from `t` to reach `t'`.
Being an inductive family, every derivation has a finite length. -/


-- @@ L108-116 verbatim
/-- `TauSteps t t'` iff `t'` is obtained from `t` by stripping finitely
many leading `step` nodes. -/
inductive TauSteps : ITree F α → ITree F α → Prop where
  /-- Strip zero steps: `t` is reachable from itself. -/
  | refl (t : ITree F α) : TauSteps t t
  /-- Strip one step from a step-headed tree and continue stripping. -/
  | step {t t' : ITree F α} (c : PUnit.{uFB + 1} → ITree F α)
      (ht : shape' t = ⟨.step, c⟩) (hr : TauSteps (c PUnit.unit) t') :
      TauSteps t t'


-- @@ L118-118 verbatim
namespace TauSteps


-- @@ L120-125 verbatim
/-- Transitivity of τ-stripping. -/
theorem trans {t s u : ITree F α} (h₁ : TauSteps t s) (h₂ : TauSteps s u) :
    TauSteps t u := by
  induction h₁ with
  | refl _ => exact h₂
  | step c ht _ ih => exact .step c ht (ih h₂)


-- @@ L127-130 verbatim
/-- Stripping one step is available when the head is a step. -/
theorem one {t : ITree F α} (c : PUnit.{uFB + 1} → ITree F α)
    (ht : shape' t = ⟨.step, c⟩) : TauSteps t (c PUnit.unit) :=
  TauSteps.step (t' := c PUnit.unit) c ht (TauSteps.refl _)


-- @@ L132-135 verbatim
/-- The `.step` relation is deterministic on step-headed trees. -/
theorem cont_eq {t : ITree F α} {c c' : PUnit.{uFB + 1} → ITree F α}
    (h : shape' t = ⟨.step, c⟩) (h' : shape' t = ⟨.step, c'⟩) : c = c' :=
  eq_of_heq (Sigma.mk.inj (h.symm.trans h')).2


-- @@ L137-150 verbatim
/-- `TauSteps` is linear: any two strippings from the same tree are
comparable. Uses determinism of `shape'`. -/
theorem linear {t a b : ITree F α}
    (ha : TauSteps t a) (hb : TauSteps t b) :
    TauSteps a b ∨ TauSteps b a := by
  induction ha generalizing b with
  | refl _ => exact Or.inl hb
  | @step t t' c ht hr ih =>
      cases hb with
      | refl _ => exact Or.inr (TauSteps.step (t' := t') c ht hr)
      | @step _ _ c' ht' hr' =>
          have hcc : c = c' := cont_eq ht ht'
          subst hcc
          exact ih hr'


-- @@ L152-152 verbatim
end TauSteps


-- @@ L154-160 verbatim
/-! ### Relational head matching

`MatchRel RR R t s` pins two trees whose observable heads agree. Pure
leaves are compared by `RR`; visible queries share an event and compare
their continuations pointwise by `R`; paired silent steps also continue
through `R`. There is no τ-stripping here: stripping happens separately
via `TauSteps` before invoking `MatchRel`. -/


-- @@ L162-171 verbatim
/-- One-step observable head match for trees with potentially different
return types. -/
inductive MatchRel (RR : α → β → Prop)
    (R : ITree F α → ITree F β → Prop) :
    ITree F α → ITree F β → Prop where
  /-- Both heads are pure leaves carrying `RR`-related values. -/
  | pure {t : ITree F α} {s : ITree F β} (r : α) (r' : β) (hrr : RR r r')
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r', PEmpty.elim⟩) :
      MatchRel RR R t s
  
-- @@ L172-177 verbatim
/-- Both heads are visible queries on the same event. -/
  | query {t : ITree F α} {s : ITree F β} (a : F.A)
      (c : F.B a → ITree F α) (c' : F.B a → ITree F β)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, R (c b) (c' b)) :
      MatchRel RR R t s
  
-- @@ L178-184 verbatim
/-- Both heads are silent steps, with continuations related by `R`. -/
  | tau {t : ITree F α} {s : ITree F β}
      (ct : PUnit.{uFB + 1} → ITree F α)
      (cs : PUnit.{uFB + 1} → ITree F β)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : R (ct PUnit.unit) (cs PUnit.unit)) :
      MatchRel RR R t s


-- @@ L186-186 verbatim
namespace MatchRel


-- @@ L188-196 verbatim
/-- Monotonicity in the continuation relation. -/
theorem mono {RR : α → β → Prop}
    {R R' : ITree F α → ITree F β → Prop}
    (h : ∀ a b, R a b → R' a b) {t : ITree F α} {s : ITree F β}
    (hM : MatchRel RR R t s) : MatchRel RR R' t s := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r r' hrr ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs (fun b => h _ _ (hcc b))
  | tau ct cs ht hs hr => exact .tau ct cs ht hs (h _ _ hr)


-- @@ L198-206 verbatim
/-- Monotonicity in the return-value relation. -/
theorem mono_result {RR RR' : α → β → Prop}
    (h : ∀ a b, RR a b → RR' a b)
    {R : ITree F α → ITree F β → Prop} {t : ITree F α} {s : ITree F β}
    (hM : MatchRel RR R t s) : MatchRel RR' R t s := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r r' (h _ _ hrr) ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr


-- @@ L208-215 verbatim
/-- Swap the two trees and both component relations. -/
theorem swap {RR : α → β → Prop} {R : ITree F α → ITree F β → Prop}
    {t : ITree F α} {s : ITree F β} (hM : MatchRel RR R t s) :
    MatchRel (fun b a => RR a b) (fun y x => R x y) s t := by
  cases hM with
  | pure r r' hrr ht hs => exact .pure r' r hrr hs ht
  | query a c c' ht hs hcc => exact .query a c' c hs ht (fun b => hcc b)
  | tau ct cs ht hs hr => exact .tau cs ct hs ht hr


-- @@ L217-217 verbatim
end MatchRel


-- @@ L219-223 verbatim
/-! ### Equality-specialized head match compatibility view

`Match R t s` pins two trees whose observable heads agree. There is no
τ-stripping here: stripping happens separately via `TauSteps` before
invoking `Match`. -/


-- @@ L225-235 verbatim
/-- One-step observable head match. Two trees have matching heads iff
both are pure leaves carrying the same value, both are queries with the
same event name and pointwise `R`-related continuations, or both are
step-headed with `R`-related step continuations. -/
inductive Match (R : ITree F α → ITree F α → Prop) :
    ITree F α → ITree F α → Prop where
  /-- Both heads are pure leaves with the same value. -/
  | pure {t s : ITree F α} (r : α)
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r, PEmpty.elim⟩) :
      Match R t s
  
-- @@ L236-240 verbatim
/-- Both heads are visible queries on the same event. -/
  | query {t s : ITree F α} (a : F.A) (c c' : F.B a → ITree F α)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, R (c b) (c' b)) :
      Match R t s
  
-- @@ L241-245 verbatim
/-- Both heads are silent steps, with continuations related by `R`. -/
  | tau {t s : ITree F α} (ct cs : PUnit.{uFB + 1} → ITree F α)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : R (ct PUnit.unit) (cs PUnit.unit)) :
      Match R t s


-- @@ L247-247 verbatim
namespace Match


-- @@ L249-256 verbatim
/-- Monotonicity: `Match` is monotone in its relation parameter. -/
theorem mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hM : Match R t s) : Match R' t s := by
  cases hM with
  | pure r ht hs => exact .pure r ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs (fun b => h _ _ (hcc b))
  | tau ct cs ht hs hr => exact .tau ct cs ht hs (h _ _ hr)


-- @@ L258-264 verbatim
/-- `Match` is symmetric in the two sides when `R` is swapped. -/
theorem swap {R : ITree F α → ITree F α → Prop} {t s : ITree F α}
    (hM : Match R t s) : Match (fun x y => R y x) s t := by
  cases hM with
  | pure r ht hs => exact .pure r hs ht
  | query a c c' ht hs hcc => exact .query a c' c hs ht (fun b => hcc b)
  | tau ct cs ht hs hr => exact .tau cs ct hs ht hr


-- @@ L266-266 verbatim
end Match


-- @@ L268-274 verbatim
/-- Embed the equality-specialized compatibility view into `MatchRel`. -/
theorem Match.toMatchRel {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hM : Match R t s) : MatchRel Eq R t s := by
  cases hM with
  | pure r ht hs => exact .pure r r rfl ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr


-- @@ L276-285 verbatim
/-- Recover the compatibility `Match` view from an equality-specialized
relational head match. -/
theorem MatchRel.toMatch {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hM : MatchRel Eq R t s) : Match R t s := by
  cases hM with
  | pure r r' hrr ht hs =>
      subst r'
      exact .pure r ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs hcc
  | tau ct cs ht hs hr => exact .tau ct cs ht hs hr


-- @@ L287-287 verbatim
/-! ### Relational weak bisimulation -/


-- @@ L289-294 verbatim
/-- One-step unfolding functor for relational weak bisimulation. -/
def WeakBisimRelF (RR : α → β → Prop)
    (R : ITree F α → ITree F β → Prop)
    (t : ITree F α) (s : ITree F β) : Prop :=
  ∃ t' : ITree F α, ∃ s' : ITree F β,
    TauSteps t t' ∧ TauSteps s s' ∧ MatchRel RR R t' s'


-- @@ L296-296 verbatim
namespace WeakBisimRelF


-- @@ L298-304 verbatim
/-- Monotonicity in the continuation relation. -/
theorem mono {RR : α → β → Prop}
    {R R' : ITree F α → ITree F β → Prop}
    (h : ∀ a b, R a b → R' a b) {t : ITree F α} {s : ITree F β}
    (hF : WeakBisimRelF RR R t s) : WeakBisimRelF RR R' t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono h⟩


-- @@ L306-312 verbatim
/-- Monotonicity in the return-value relation. -/
theorem mono_result {RR RR' : α → β → Prop}
    (h : ∀ a b, RR a b → RR' a b)
    {R : ITree F α → ITree F β → Prop} {t : ITree F α} {s : ITree F β}
    (hF : WeakBisimRelF RR R t s) : WeakBisimRelF RR' R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono_result h⟩


-- @@ L314-314 verbatim
end WeakBisimRelF


-- @@ L316-320 verbatim
/-- Relational weak bisimulation (`euttR`). The trees share an event
signature but may have return types in different universes. -/
def WeakBisimRel (RR : α → β → Prop) (t : ITree F α) (s : ITree F β) : Prop :=
  ∃ R : ITree F α → ITree F β → Prop,
    (∀ a b, R a b → WeakBisimRelF RR R a b) ∧ R t s


-- @@ L322-322 verbatim
@[inherit_doc] scoped notation:50 t " ≈[" RR "] " s => ITree.WeakBisimRel RR t s


-- @@ L324-324 verbatim
namespace WeakBisimRel


-- @@ L326-330 verbatim
/-- Coinduction principle for relational weak bisimulation. -/
theorem coinduct (RR : α → β → Prop) (R : ITree F α → ITree F β → Prop)
    (h : ∀ a b, R a b → WeakBisimRelF RR R a b)
    {a : ITree F α} {b : ITree F β} (hab : R a b) : WeakBisimRel RR a b :=
  ⟨R, h, hab⟩


-- @@ L332-337 verbatim
/-- Relational weak bisimulation is closed under its one-step functor. -/
theorem unfold {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) : WeakBisimRelF RR (WeakBisimRel RR) t s := by
  obtain ⟨R, hcl, hR⟩ := h
  obtain ⟨t', s', ht, hs, hm⟩ := hcl _ _ hR
  exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => ⟨R, hcl, hxy⟩)⟩


-- @@ L339-344 verbatim
/-- Extract the stripped-heads relational match witness. -/
theorem dest {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) :
    ∃ t' : ITree F α, ∃ s' : ITree F β,
      TauSteps t t' ∧ TauSteps s s' ∧ MatchRel RR (WeakBisimRel RR) t' s' :=
  unfold h


-- @@ L346-354 verbatim
/-- Folding rule for relational weak bisimulation. -/
theorem fold {RR : α → β → Prop} {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRelF RR (WeakBisimRel RR) t s) : WeakBisimRel RR t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct RR (fun a b => WeakBisimRel RR a b ∨ (a = t ∧ b = s))
    ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro a b (hab | ⟨rfl, rfl⟩)
  · exact (unfold hab).mono (fun x y hxy => Or.inl hxy)
  · exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => Or.inl hxy)⟩


-- @@ L356-361 verbatim
/-- Monotonicity in the relation used to compare pure leaves. -/
theorem mono_result {RR RR' : α → β → Prop}
    (hRR : ∀ a b, RR a b → RR' a b) {t : ITree F α} {s : ITree F β}
    (h : WeakBisimRel RR t s) : WeakBisimRel RR' t s := by
  obtain ⟨R, hcl, hR⟩ := h
  exact ⟨R, fun a b hab => (hcl a b hab).mono_result hRR, hR⟩


-- @@ L363-363 verbatim
end WeakBisimRel


-- @@ L365-365 verbatim
/-! ### Equality-specialized weak bisimulation -/


-- @@ L367-371 verbatim
/-- One-step unfolding functor for weak bisimulation: strip finitely many
τ's from each side (via `TauSteps`) and then match observable heads (via
`Match`). `WeakBisim` is the Tarski greatest fixed point of this functor. -/
def WeakBisimF (R : ITree F α → ITree F α → Prop) (t s : ITree F α) : Prop :=
  ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match R t' s'


-- @@ L373-378 verbatim
/-- `WeakBisimF` is monotone in its relation parameter. -/
theorem WeakBisimF.mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hF : WeakBisimF R t s) : WeakBisimF R' t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono h⟩


-- @@ L380-384 verbatim
/-- Convert the compatibility one-step view to the relational functor. -/
theorem WeakBisimF.toWeakBisimRelF {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hF : WeakBisimF R t s) : WeakBisimRelF Eq R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.toMatchRel⟩


-- @@ L386-391 verbatim
/-- Convert the equality-specialized relational functor to its compatibility
view. -/
theorem WeakBisimRelF.toWeakBisimF {R : ITree F α → ITree F α → Prop}
    {t s : ITree F α} (hF : WeakBisimRelF Eq R t s) : WeakBisimF R t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.toMatch⟩


-- @@ L393-398 verbatim
/-- Weak bisimulation (Coq `eutt`). Two trees are weakly bisimilar iff
there exists a relation `R` containing the pair that is closed under
one-step unfolding into `WeakBisimF`. Equivalently, `WeakBisim` is the
largest such relation (Tarski greatest fixed point). -/
abbrev WeakBisim (t s : ITree F α) : Prop :=
  WeakBisimRel Eq t s


-- @@ L400-400 verbatim
@[inherit_doc] scoped infix:50 " ≈ " => ITree.WeakBisim


-- @@ L402-402 verbatim
namespace WeakBisim


-- @@ L404-410 verbatim
/-- Coinduction principle: any relation closed under `WeakBisimF` is
contained in `WeakBisim`. This is the Tarski greatest fixed point
characterization. -/
theorem coinduct (R : ITree F α → ITree F α → Prop)
    (h : ∀ a b, R a b → WeakBisimF R a b)
    {a b : ITree F α} (hab : R a b) : a ≈ b :=
  WeakBisimRel.coinduct Eq R (fun a b hR => (h a b hR).toWeakBisimRelF) hab


-- @@ L412-414 verbatim
/-- `WeakBisim` is closed under `WeakBisimF`. -/
theorem unfold {t s : ITree F α} (h : t ≈ s) : WeakBisimF WeakBisim t s :=
  (WeakBisimRel.unfold h).toWeakBisimF


-- @@ L416-419 verbatim
/-- Extract the stripped-heads match witness. -/
theorem dest {t s : ITree F α} (h : t ≈ s) :
    ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match WeakBisim t' s' :=
  unfold h


-- @@ L421-429 verbatim
/-- Folding rule: supplying a `WeakBisimF WeakBisim`-match recovers
`WeakBisim`. -/
theorem fold {t s : ITree F α} (h : WeakBisimF WeakBisim t s) : t ≈ s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct (fun a b => a ≈ b ∨
      (a = t ∧ b = s)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro a b (hab | ⟨rfl, rfl⟩)
  · exact (unfold hab).mono (fun x y hxy => Or.inl hxy)
  · exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => Or.inl hxy)⟩


-- @@ L431-431 verbatim
end WeakBisim


-- @@ L433-433 verbatim
end ITree
