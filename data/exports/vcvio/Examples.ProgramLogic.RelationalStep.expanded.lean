/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.Relational
public import VCVio.OracleComp.Constructions.Replicate


-- @@ L12-16 verbatim
/-!
# Relational VCGen Step Examples

This file validates one-step relational tactic behavior.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open ENNReal OracleSpec OracleComp

-- @@ L21-21 verbatim
open OracleComp.ProgramLogic

-- @@ L22-22 verbatim
open OracleComp.ProgramLogic.Relational

-- @@ L23-23 verbatim
open Lean.Order

-- @@ L24-24 verbatim
open scoped OracleComp.ProgramLogic


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
variable {ι : Type u} {spec : OracleSpec ι}

-- @@ L29-29 verbatim
variable [IsUniformSpec spec]

-- @@ L30-30 verbatim
variable {α β γ δ : Type}


-- @@ L32-32 verbatim
/-! ## Basic relational stepping -/


-- @@ L34-36 expanded
example (oa : OracleComp spec α) : Relational.RelTriple oa oa (EqRel α) := by rvcstep


-- @@ L38-43 expanded
example {oa₁ oa₂ : OracleComp spec α} {f₁ f₂ : α → OracleComp spec β}
    (hoa : Relational.RelTriple oa₁ oa₂ (EqRel α))
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → Relational.RelTriple (f₁ a₁) (f₂ a₂) (EqRel β)) :
    Relational.RelTriple (oa₁ >>= f₁) (oa₂ >>= f₂) (EqRel β) := by rvcstep


-- @@ L45-51 expanded
example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ} (hoa : Relational.RelTriple oa₁ oa₂ S)
    (hf : ∀ a₁ a₂, S a₁ a₂ → Relational.RelTriple (f₁ a₁) (f₂ a₂) R) :
    Relational.RelTriple (oa₁ >>= f₁) (oa₂ >>= f₂) R := by rvcstep using S


-- @@ L53-56 expanded
example (f : α → OracleComp spec β) : ∀ x, Relational.RelTriple (f x) (f x) (EqRel β) :=
  by
  rvcstep as⟨x⟩
  rvcstep


-- @@ L58-62 expanded
example (t : spec.Domain) :
    Relational.RelTriple (query t : OracleComp spec (spec.Range t))
      (query t : OracleComp spec (spec.Range t)) (EqRel (spec.Range t)) :=
  by rvcstep


-- @@ L64-68 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} {R : RelPost α β}
    (h : Relational.RelTriple oa ob R) : Relational.RelTriple ob oa fun b a => R a b :=
  by
  rvcstep sym
  exact h


-- @@ L70-76 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} {R : RelPost α β}
    (h : Relational.RelTriple oa ob R) : Relational.RelTriple oa ob fun a b => R a b ∧ True :=
  by
  rvcstep upto R
  · exact h
  · intro a b hab
    exact ⟨hab, trivial⟩


-- @@ L78-85 expanded
example {oa mid : OracleComp spec α} {ob : OracleComp spec β} {R : RelPost α β}
    (hleft : Relational.RelTriple oa mid (EqRel α)) (hright : Relational.RelTriple mid ob R) :
    Relational.RelTriple oa ob R := by
  fail_if_success rvcstep
  rvcstep trans mid
  · exact hleft
  · exact hright


-- @@ L87-94 expanded
example {oa : OracleComp spec α} {mid ob : OracleComp spec β} {R : RelPost α β}
    (hleft : Relational.RelTriple oa mid R) (hright : Relational.RelTriple mid ob (EqRel β)) :
    Relational.RelTriple oa ob R := by
  fail_if_success rvcstep
  rvcstep trans mid
  · exact hleft
  · exact hright


-- @@ L96-109 expanded
theorem rvcstep_trans_postprocess_right [SampleableType α] (f : α → β) (g : β → γ) :
    Relational.RelTriple
      (do
        let x ← (uniformSample α : ProbComp α)
        pure (f x))
      (do
        let x ← (uniformSample α : ProbComp α)
        pure (g (f x)))
      fun y z => z = g y :=
  by
  rvcstep
    trans(do
      let x ← (uniformSample α : ProbComp α)
      pure (f x))
  · rvcstep
  · rvcstep using EqRel α


-- @@ L111-124 expanded
theorem rvcstep_trans_postprocess_left [SampleableType α] (f : β → γ) (g : α → β) :
    Relational.RelTriple
      (do
        let x ← (uniformSample α : ProbComp α)
        pure (f (g x)))
      (do
        let x ← (uniformSample α : ProbComp α)
        pure (g x))
      fun y z => y = f z :=
  by
  rvcstep
    trans(do
      let x ← (uniformSample α : ProbComp α)
      pure (g x))
  · rvcstep using EqRel α
  · rvcstep


-- @@ L126-135 expanded
/-- info: [vcspec cache] miss `OracleComp.ProgramLogic.Relational.relTriple_map` (folded, relTriple)
-/
#guard_msgs in
  set_option vcvio.vcgen.traceCachedRules true in
  example {oa : OracleComp spec α} {ob : OracleComp spec β} {R : RelPost γ δ} {f : α → γ}
      {g : β → δ} (h : Relational.RelTriple oa ob fun a b => R (f a) (g b)) :
      Relational.RelTriple (f <$> oa) (g <$> ob) R := by rvcstep


-- @@ L137-137 verbatim
/-! ## Bijective random sampling -/


-- @@ L139-145 expanded
example [SampleableType α] {f : α → α} (hf : Function.Bijective f) :
    Relational.RelTriple (uniformSample α : ProbComp α) (uniformSample α : ProbComp α) fun x y =>
      y = f x :=
  by
  rvcstep using f
  · exact hf
  · intro x
    rfl


-- @@ L147-153 expanded
example [SampleableType α] {f : α → α} (hf : Function.Bijective f) :
    Relational.RelTriple (uniformSample α : ProbComp α) (uniformSample α : ProbComp α) fun x y =>
      y = f x :=
  by
  rvcstep
  · exact hf
  · intro x
    rfl


-- @@ L155-161 expanded
example [SampleableType α] {f : α → α} (hf : Function.Bijective f) :
    Relational.RelTriple ((uniformSample α : ProbComp α) >>= fun x => pure x)
      ((uniformSample α : ProbComp α) >>= fun x => pure x) fun x y => y = f x :=
  by
  rvcstep using f
  exact hf


-- @@ L163-163 verbatim
/-! ## Bind swap -/


-- @@ L165-171 expanded
example {mx : OracleComp spec α} {my : OracleComp spec β} {f : α → β → OracleComp spec γ} :
    Relational.RelTriple (mx >>= fun a => my >>= fun b => f a b)
      (my >>= fun b => mx >>= fun a => f a b) (EqRel γ) :=
  by
  rvcstep swap left
  rvcfinish


-- @@ L173-179 expanded
example {mx : OracleComp spec α} {my : OracleComp spec β} {f : α → β → OracleComp spec γ} :
    Relational.RelTriple (my >>= fun b => mx >>= fun a => f a b)
      (mx >>= fun a => my >>= fun b => f a b) (EqRel γ) :=
  by
  rvcstep swap right
  rvcfinish


-- @@ L181-190 expanded
example {mx : OracleComp spec α} {my : OracleComp spec β} {f : α → β → OracleComp spec γ}
    {g : β → α → OracleComp spec δ} {R : RelPost γ δ}
    (hfg : ∀ b a, Relational.RelTriple (f a b) (g b a) R) :
    Relational.RelTriple (mx >>= fun a => my >>= fun b => f a b)
      (my >>= fun b => mx >>= fun a => g b a) R :=
  by
  rvcstep swap left
  rvcgen using[EqRel β, EqRel α]
  exact hfg _ _


-- @@ L192-201 expanded
example {mx : OracleComp spec α} {my : OracleComp spec β} {f : α → β → OracleComp spec γ}
    {g : β → α → OracleComp spec δ} {R : RelPost δ γ}
    (hgf : ∀ b a, Relational.RelTriple (g b a) (f a b) R) :
    Relational.RelTriple (my >>= fun b => mx >>= fun a => g b a)
      (mx >>= fun a => my >>= fun b => f a b) R :=
  by
  rvcstep swap right
  rvcgen using[EqRel β, EqRel α]
  exact hgf _ _


-- @@ L203-209 expanded
example {mx : OracleComp spec α} {my : OracleComp spec β} {k : α → β → δ} :
    Relational.RelTriple (mx >>= fun a => my >>= fun b => pure (k a b))
      (my >>= fun b => mx >>= fun a => pure (k a b)) (EqRel δ) :=
  by
  rvcstep swap left
  rvcfinish


-- @@ L211-227 expanded
example [SampleableType α] {my : ProbComp β} {f : α → α} (hf : Function.Bijective f) :
    Relational.RelTriple
      (do
        let x ← (uniformSample α : ProbComp α)
        let y ← my
        pure (x, y))
      (do
        let y ← my
        let x ← (uniformSample α : ProbComp α)
        pure (x, y))
      fun p q => q.1 = f p.1 ∧ q.2 = p.2 :=
  by
  rvcstep swap left using EqRel β
  intro y₁ y₂ hy
  subst hy
  rvcstep using f
  · exact relTriple_pure_pure ⟨rfl, rfl⟩
  · exact hf


-- @@ L229-245 expanded
example [SampleableType α] {my : ProbComp β} {f : α → α} (hf : Function.Bijective f) :
    Relational.RelTriple
      (do
        let y ← my
        let x ← (uniformSample α : ProbComp α)
        pure (x, y))
      (do
        let x ← (uniformSample α : ProbComp α)
        let y ← my
        pure (x, y))
      fun p q => q.1 = f p.1 ∧ q.2 = p.2 :=
  by
  rvcstep swap right using EqRel β
  intro y₁ y₂ hy
  subst hy
  rvcstep using f
  · exact relTriple_pure_pure ⟨rfl, rfl⟩
  · exact hf


-- @@ L247-251 expanded
example [SampleableType α] (post : α → α → ℝ≥0∞) :
    Std.Do'.RelTriple (∑' a : α, probOutput (uniformSample α : ProbComp α) a * post a a)
      (uniformSample α : ProbComp α) (uniformSample α : ProbComp α) post Lean.Order.bot
      Lean.Order.bot :=
  by rvcstep


-- @@ L253-259 expanded
example (t : spec.Domain) (post : spec.Range t → spec.Range t → ℝ≥0∞) :
    Std.Do'.RelTriple
      (∑' a : spec.Range t, probOutput (query t : OracleComp spec (spec.Range t)) a * post a a)
      (query t : OracleComp spec (spec.Range t)) (query t : OracleComp spec (spec.Range t)) post
      Lean.Order.bot Lean.Order.bot :=
  by exact OracleComp.ProgramLogic.Relational.Loom.relTriple_query_refl t post


-- @@ L261-261 verbatim
/-! ## Iteration rules -/


-- @@ L263-266 expanded
example {oa₁ oa₂ : OracleComp spec α} (n : ℕ) (h : Relational.RelTriple oa₁ oa₂ (EqRel α)) :
    Relational.RelTriple (oa₁.replicate n) (oa₂.replicate n) (EqRel (List α)) := by rvcstep


-- @@ L268-272 expanded
example {oa : OracleComp spec α} {ob : OracleComp spec β} (n : ℕ) {R : RelPost α β}
    (h : Relational.RelTriple oa ob R) :
    Relational.RelTriple (oa.replicate n) (ob.replicate n) (List.Forall₂ R) := by rvcstep


-- @@ L274-277 expanded
example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, Relational.RelTriple (f a) (g a) (EqRel β)) :
    Relational.RelTriple (xs.mapM f) (xs.mapM g) (EqRel (List β)) := by rvcstep


-- @@ L279-286 expanded
example {xs : List α} {ys : List β} {S : α → β → Prop} {f : α → OracleComp spec γ}
    {g : β → OracleComp spec γ} {R : RelPost γ γ} (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → Relational.RelTriple (f a) (g b) R) :
    Relational.RelTriple (xs.mapM f) (ys.mapM g) (List.Forall₂ R) := by rvcstep using S


-- @@ L288-297 expanded
example {σ₁ σ₂ : Type} {xs : List α} {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → α → OracleComp spec σ₂} {S : σ₁ → σ₂ → Prop} {s₁ : σ₁} {s₂ : σ₂} (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → Relational.RelTriple (f t₁ a) (g t₂ a) S) :
    Relational.RelTriple (xs.foldlM f s₁) (xs.foldlM g s₂) S := by rvcstep


-- @@ L299-310 expanded
example {σ₁ σ₂ : Type} {xs : List α} {ys : List β} {Rin : α → β → Prop}
    {f : σ₁ → α → OracleComp spec σ₁} {g : σ₂ → β → OracleComp spec σ₂} {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂} (hs : S s₁ s₂) (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → Relational.RelTriple (f t₁ a) (g t₂ b) S) :
    Relational.RelTriple (xs.foldlM f s₁) (ys.foldlM g s₂) S := by rvcstep using Rin


-- @@ L312-312 verbatim
/-! ## Pure / ite rules -/


-- @@ L314-316 expanded
example (a : α) :
    Relational.RelTriple (pure a : OracleComp spec α) (pure a : OracleComp spec α) (EqRel α) := by
  rvcstep


-- @@ L318-323 expanded
example {c : Prop} [Decidable c] {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : Relational.RelTriple oa₁ ob₁ (EqRel α)) (h2 : Relational.RelTriple oa₂ ob₂ (EqRel α)) :
    Relational.RelTriple (if c then oa₁ else oa₂) (if c then ob₁ else ob₂) (EqRel α) := by rvcstep


-- @@ L325-325 verbatim
/-! ## Auto relational hint consumption -/


-- @@ L327-333 expanded
example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ} (hoa : Relational.RelTriple oa₁ oa₂ S)
    (hf : ∀ a₁ a₂, S a₁ a₂ → Relational.RelTriple (f₁ a₁) (f₂ a₂) R) :
    Relational.RelTriple (oa₁ >>= f₁) (oa₂ >>= f₂) R := by rvcstep


-- @@ L335-341 expanded
example {oa₁ oa₂ : OracleComp spec α} {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ} (hoa : Relational.RelTriple oa₁ oa₂ S)
    (hf : ∀ a₁ a₂, S a₁ a₂ → Relational.RelTriple (f₁ a₁) (f₂ a₂) R) :
    Relational.RelTriple (oa₁ >>= f₁) (oa₂ >>= f₂) R := by rvcgen


-- @@ L343-347 verbatim
/-! ## Leaf closure via equality hypotheses

These exercise the augmented leaf closer that calls `subst_vars` and tries the
canonical pure/refl rules afterward, so syntactically-distinct pure values that
become equal under local equalities close automatically. -/


-- @@ L349-351 expanded
example {a b : α} (h : a = b) :
    Relational.RelTriple (pure a : OracleComp spec α) (pure b : OracleComp spec α) (EqRel α) := by
  rvcstep


-- @@ L353-355 expanded
example {a b : α} (h : b = a) :
    Relational.RelTriple (pure a : OracleComp spec α) (pure b : OracleComp spec α) (EqRel α) := by
  rvcstep


-- @@ L357-361 verbatim
/-! ## Bind normalization

These exercise the monadic-normalization pre-pass: nested `>>=` and `pure`-binds
get flattened so the relational planner sees aligned bind shapes (or bypasses
the bind rule entirely when both sides reduce to a leaf). -/


-- @@ L363-365 expanded
example {a : α} {f : α → OracleComp spec β} :
    Relational.RelTriple
      (do
        let x ← pure a;
        f x)
      (f a) (EqRel β) :=
  by simpa only [monad_norm] using (relTriple_refl (oa := f a))


-- @@ L367-370 expanded
example {oa : OracleComp spec α} {f : α → OracleComp spec β} {g : β → OracleComp spec γ} :
    Relational.RelTriple ((oa >>= f) >>= g)
      (do
        let x ← oa;
        let y ← f x;
        g y)
      (EqRel γ) :=
  by simpa only [monad_norm] using (relTriple_refl (oa := oa >>= fun x => f x >>= g))


-- @@ L372-381 verbatim
/-! ## Regression: multi-goal isolation

Not an idiomatic-usage example. The deliberately unfocused `rvcstep` below
exercises the corner case where `rvcstep` is invoked with sibling goals visible
in the goal list (the pattern `linter.style.multiGoal` discourages on style
grounds, but which must still behave *correctly* when used). Previously, when
the sample subgoal of `relTriple_bind` auto-closed, an unconditional
swap-and-close pass could pull a trailing sibling ahead of the bind continuation
and silently discharge it. The fix in `closeSampleAndReorderBindGoals` keeps
`rest` untouched at the tail. -/


-- @@ L383-392 expanded
example {oa : OracleComp spec α} {f g : α → OracleComp spec β} (ob : OracleComp spec α)
    (hf : ∀ a, Relational.RelTriple (f a) (g a) (EqRel β)) :
    (Relational.RelTriple (oa >>= f) (oa >>= g) (EqRel β)) ∧
      (Relational.RelTriple ob ob (EqRel α)) :=
  by
  constructor
  · refine relTriple_bind (R := EqRel α) (relTriple_refl (oa := oa)) ?_
    intro a₁ a₂ h
    subst h
    exact hf a₁
  · exact relTriple_refl (oa := ob)


-- @@ L394-394 verbatim
/-! ## Quantitative `Std.Do'.RelTriple` path -/


-- @@ L396-400 expanded
example (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    Std.Do'.RelTriple (post a b) (pure a : OracleComp spec α) (pure b : OracleComp spec β) post
      Lean.Order.bot Lean.Order.bot :=
  by rvcstep


-- @@ L402-406 expanded
example (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    post a b ⊑
      Std.Do'.rwp (pure a : OracleComp spec α) (pure b : OracleComp spec β) post
        Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by rvcstep


-- @@ L408-421 expanded
example (a : α) (b : β) (f : α → OracleComp spec γ) (g : β → OracleComp spec δ)
    (post : γ → δ → ℝ≥0∞) :
    Std.Do'.rwp (f a) (g b) post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk ⊑
      Std.Do'.rwp
        (do
          let x ← (pure a : OracleComp spec α)
          f x)
        (do
          let y ← (pure b : OracleComp spec β)
          g y)
        post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by rvcgen


-- @@ L423-436 expanded
example [DecidableEq γ] [DecidableEq δ] (a : α) (b : β) (f : α → γ) (g : β → δ)
    (post : γ → δ → ℝ≥0∞) :
    post (f a) (g b) ⊑
      Std.Do'.rwp
        (do
          let x ← (pure a : OracleComp spec α)
          pure (f x))
        (do
          let y ← (pure b : OracleComp spec β)
          pure (g y))
        post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by rvcgen


-- @@ L438-450 expanded
example (a : α) (b : β) (f : α → OracleComp spec γ) (post : γ → β → ℝ≥0∞) :
    Std.Do'.rwp (f a) (pure b : OracleComp spec β) post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk ⊑
      Std.Do'.rwp
        (do
          let x ← (pure a : OracleComp spec α)
          f x)
        (pure b : OracleComp spec β) post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  rvcstep left
  rvcgen


-- @@ L452-464 expanded
example (a : α) (b : β) (g : β → OracleComp spec δ) (post : α → δ → ℝ≥0∞) :
    Std.Do'.rwp (pure a : OracleComp spec α) (g b) post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk ⊑
      Std.Do'.rwp (pure a : OracleComp spec α)
        (do
          let y ← (pure b : OracleComp spec β)
          g y)
        post Std.Do'.EPost.nil.mk Std.Do'.EPost.nil.mk :=
  by
  rvcstep right
  rvcgen


-- @@ L466-475 expanded
example (a : α) (b : β) (f : α → OracleComp spec γ) (post : γ → β → ℝ≥0∞) :
    Std.Do'.RelTriple
      (Std.Do'.rwp (f a) (pure b : OracleComp spec β) post Std.Do'.EPost.nil.mk
        Std.Do'.EPost.nil.mk)
      (do
        let x ← (pure a : OracleComp spec α)
        f x)
      (pure b : OracleComp spec β) post Lean.Order.bot Lean.Order.bot :=
  by
  rvcstep left
  rvcgen


-- @@ L477-487 expanded
example (a : α) (b : β) (g : β → OracleComp spec δ) (post : α → δ → ℝ≥0∞) :
    Std.Do'.RelTriple
      (Std.Do'.rwp (pure a : OracleComp spec α) (g b) post Std.Do'.EPost.nil.mk
        Std.Do'.EPost.nil.mk)
      (pure a : OracleComp spec α)
      (do
        let y ← (pure b : OracleComp spec β)
        g y)
      post Lean.Order.bot Lean.Order.bot :=
  by
  rvcstep right
  rvcgen

