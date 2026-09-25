/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.Unary
public import VCVio.ProgramLogic.Unary.SimulateQ
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.OracleComp.Coercions.SubSpec


-- @@ L14-19 verbatim
/-!
# Unary VCGen Step Examples

This file validates one-step unary tactic behavior for raw `wp` goals,
registered `@[vcspec]` hints, and `liftComp`.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open ENNReal OracleSpec OracleComp

-- @@ L24-24 verbatim
open Lean.Order

-- @@ L25-25 verbatim
open OracleComp.ProgramLogic

-- @@ L26-26 verbatim
open scoped OracleComp.ProgramLogic


-- @@ L28-28 verbatim
universe u


-- @@ L30-30 verbatim
variable {ι : Type u} {spec : OracleSpec ι}

-- @@ L31-31 verbatim
variable [IsUniformSpec spec]

-- @@ L32-32 verbatim
variable {α β : Type}


-- @@ L34-34 verbatim
/-! ## Notation examples -/


-- @@ L36-38 expanded
example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp (oa >>= f) post = wp oa (fun u => wp (f u) post) := by vcstep


-- @@ L40-40 verbatim
/-! ## `vcstep` on raw `wp` goals -/


-- @@ L42-44 expanded
example (x : α) (post : α → ℝ≥0∞) : wp (pure x : OracleComp spec α) post = post x := by vcstep


-- @@ L46-48 expanded
example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (if c then a else b) post = if c then wp a post else wp b post := by vcstep


-- @@ L50-53 expanded
example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp (oa.replicate (n + 1)) post =
      wp oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs))) :=
  by vcstep


-- @@ L55-58 expanded
example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp ((x :: xs).mapM f) post = wp (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys))) := by
  vcstep


-- @@ L60-64 expanded
example (x : α) (xs : List α) (f : β → α → OracleComp spec β) (init : β) (post : β → ℝ≥0∞) :
    wp ((x :: xs).foldlM f init) post = wp (f init x) (fun s => wp (xs.foldlM f s) post) := by
  vcstep


-- @@ L66-69 expanded
example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (query t : OracleComp spec (spec.Range t)) post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u :=
  by vcstep


-- @@ L71-74 expanded
example (c : Prop) [Decidable c] (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α)
    (post : α → ℝ≥0∞) : wp (dite c a b) post = if h : c then wp (a h) post else wp (b h) post := by
  vcstep


-- @@ L76-79 expanded
example [SampleableType α] (post : α → ℝ≥0∞) :
    wp (uniformSample α : ProbComp α) post =
      ∑' u : α, probOutput (uniformSample α : ProbComp α) u * post u :=
  by vcstep


-- @@ L81-83 expanded
example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp (f <$> oa) post = wp oa (post ∘ f) := by vcstep


-- @@ L85-85 verbatim
/-! ## `StateT (OracleComp spec)` transformer steps -/


-- @@ L87-91 verbatim
example (post : Nat → Nat → ℝ≥0∞) :
    ⦃fun s => post s s⦄
      (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
    ⦃post⦄ := by
  vcstep


-- @@ L93-97 verbatim
example (s' : Nat) (post : PUnit → Nat → ℝ≥0∞) :
    ⦃fun _ => post ⟨⟩ s'⦄
      (MonadStateOf.set s' : StateT Nat (OracleComp spec) PUnit)
    ⦃post⦄ := by
  vcstep


-- @@ L99-103 verbatim
example (f : Nat → α × Nat) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => post (f s).1 (f s).2⦄
      (MonadStateOf.modifyGet f : StateT Nat (OracleComp spec) α)
    ⦃post⦄ := by
  vcstep


-- @@ L105-109 expanded
example (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃ fun s => wp oa (fun a => post a s) ⦄
      (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α) ⦃ post ⦄ :=
  by vcstep


-- @@ L111-119 expanded
example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) :
    ⦃ fun s => wp oa (fun a => post (s, a) (s + 1)) ⦄
      (do
        let s ← (MonadStateOf.get : StateT Nat (OracleComp spec) Nat)
        MonadStateOf.set (s + 1)
        let a ← (MonadLift.monadLift oa : StateT Nat (OracleComp spec) α)
        pure (s, a)) ⦃
      post ⦄ :=
  by vcgen


-- @@ L121-127 expanded
example (s' : Nat) (oa : OracleComp spec α) (post : α → Nat → ℝ≥0∞) :
    ⦃ fun _ => wp oa (fun a => post a s') ⦄
      (do
        MonadStateOf.set s'
        MonadLift.monadLift oa : StateT Nat (OracleComp spec) α) ⦃
      post ⦄ :=
  by vcgen


-- @@ L129-135 verbatim
example (f : Nat → α × Nat) (post : α → Nat → ℝ≥0∞) :
    ⦃fun s => post (f s).1 (f s).2⦄
      (do
        let a ← (MonadStateOf.modifyGet f : StateT Nat (OracleComp spec) α)
        pure a)
    ⦃post⦄ := by
  vcgen


-- @@ L137-137 verbatim
/-! ## `OptionT (OracleComp spec)` transformer steps -/


-- @@ L139-143 expanded
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (nonePost : ℝ≥0∞) :
    Std.Do'.Triple (wp oa post) (MonadLift.monadLift oa : OptionT (OracleComp spec) α) post
      (Std.Do'.EPost.cons.mk nonePost Std.Do'.EPost.nil.mk) :=
  by vcgen


-- @@ L145-151 expanded
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (nonePost : ℝ≥0∞) :
    Std.Do'.Triple (wp oa post)
      (do
        let a ← (MonadLift.monadLift oa : OptionT (OracleComp spec) α)
        pure a)
      post (Std.Do'.EPost.cons.mk nonePost Std.Do'.EPost.nil.mk) :=
  by vcgen


-- @@ L153-157 verbatim
example (post : α → ℝ≥0∞) (nonePost : ℝ≥0∞) :
    Std.Do'.Triple nonePost
      (failure : OptionT (OracleComp spec) α)
      post (Std.Do'.EPost.cons.mk nonePost Std.Do'.EPost.nil.mk) := by
  vcgen


-- @@ L159-159 verbatim
/-! ## `ExceptT (OracleComp spec)` transformer steps -/


-- @@ L161-165 expanded
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    Std.Do'.Triple (wp oa post) (MonadLift.monadLift oa : ExceptT String (OracleComp spec) α) post
      (Std.Do'.EPost.cons.mk errPost Std.Do'.EPost.nil.mk) :=
  by vcgen


-- @@ L167-173 expanded
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    Std.Do'.Triple (wp oa post)
      (do
        let a ← (MonadLift.monadLift oa : ExceptT String (OracleComp spec) α)
        pure a)
      post (Std.Do'.EPost.cons.mk errPost Std.Do'.EPost.nil.mk) :=
  by vcgen


-- @@ L175-179 verbatim
example (err : String) (post : α → ℝ≥0∞) (errPost : String → ℝ≥0∞) :
    Std.Do'.Triple (errPost err)
      (throw err : ExceptT String (OracleComp spec) α)
      post (Std.Do'.EPost.cons.mk errPost Std.Do'.EPost.nil.mk) := by
  vcgen


-- @@ L181-181 verbatim
/-! ## `ReaderT (OracleComp spec)` transformer steps -/


-- @@ L183-187 expanded
example (oa : OracleComp spec α) (post : α → String → ℝ≥0∞) :
    ⦃ fun r => wp oa (fun a => post a r) ⦄
      (MonadLift.monadLift oa : ReaderT String (OracleComp spec) α) ⦃ post ⦄ :=
  by vcgen


-- @@ L189-196 expanded
example (oa : OracleComp spec α) (post : String × α → String → ℝ≥0∞) :
    ⦃ fun r => wp oa (fun a => post (r, a) r) ⦄
      (do
        let r ← (MonadReaderOf.read : ReaderT String (OracleComp spec) String)
        let a ← (MonadLift.monadLift oa : ReaderT String (OracleComp spec) α)
        pure (r, a)) ⦃
      post ⦄ :=
  by vcgen


-- @@ L198-198 verbatim
/-! ## Mixed transformer stack steps -/


-- @@ L200-209 expanded
example (oa : OracleComp spec α) (post : Nat × α → Nat → ℝ≥0∞) (nonePost : ℝ≥0∞) :
    Std.Do'.Triple (fun s => wp oa (fun a => post (s, a) (s + 1)))
      (do
        let s ← (MonadStateOf.get : StateT Nat (OptionT (OracleComp spec)) Nat)
        (MonadStateOf.set (s + 1) : StateT Nat (OptionT (OracleComp spec)) PUnit)
        let a ← (MonadLift.monadLift (OptionT.lift oa) : StateT Nat (OptionT (OracleComp spec)) α)
        pure (s, a))
      post (Std.Do'.EPost.cons.mk nonePost Std.Do'.EPost.nil.mk) :=
  by vcgen


-- @@ L211-211 verbatim
/-! ## `WriterT (OracleComp spec)` transformer steps -/


-- @@ L213-217 expanded
example (oa : OracleComp spec α) (post : α → Multiplicative Nat → ℝ≥0∞) :
    ⦃ fun w => wp oa (fun a => post a w) ⦄
      (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) ⦃ post ⦄ :=
  by vcgen


-- @@ L219-223 verbatim
example (out : Multiplicative Nat) (post : PUnit → Multiplicative Nat → ℝ≥0∞) :
    ⦃fun w => post ⟨⟩ (w * out)⦄
      (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit)
    ⦃post⦄ := by
  vcgen


-- @@ L225-233 expanded
example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : PUnit × α → Multiplicative Nat → ℝ≥0∞) :
    ⦃ fun w => wp oa (fun a => post (PUnit.unit, a) (w * out)) ⦄
      (do
        MonadWriter.tell out
        let a ← (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α)
        pure (PUnit.unit, a)) ⦃
      post ⦄ :=
  by vcgen


-- @@ L235-253 expanded
example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : Nat × α → Nat → Multiplicative Nat → ℝ≥0∞) :
    Std.Do'.Triple (fun s w => wp oa (fun a => post (s, a) (s + 1) (w * out)))
      ((do
          let s ←
            (MonadStateOf.get : StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) Nat)
          (MonadStateOf.set (s + 1) :
              StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
          (MonadLift.monadLift
                (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit) :
              StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
          let a ←
            (MonadLift.monadLift
                  (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) :
                StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) α)
          (pure (s, a) : StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) (Nat × α))) :
        StateT Nat (WriterT (Multiplicative Nat) (OracleComp spec)) (Nat × α))
      post Lean.Order.bot :=
  by vcgen


-- @@ L255-271 expanded
example (oa : OracleComp spec α) (out : Multiplicative Nat)
    (post : String × α → String → Multiplicative Nat → ℝ≥0∞) :
    Std.Do'.Triple (fun r w => wp oa (fun a => post (r, a) r (w * out)))
      ((do
          let r ←
            (MonadReaderOf.read :
                ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) String)
          (MonadLift.monadLift
                (MonadWriter.tell out : WriterT (Multiplicative Nat) (OracleComp spec) PUnit) :
              ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) PUnit)
          let a ←
            (MonadLift.monadLift
                  (MonadLift.monadLift oa : WriterT (Multiplicative Nat) (OracleComp spec) α) :
                ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) α)
          (pure (r, a) :
              ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) (String × α))) :
        ReaderT String (WriterT (Multiplicative Nat) (OracleComp spec)) (String × α))
      post Lean.Order.bot :=
  by vcgen


-- @@ L273-282 expanded
/-- info: [wpstep cache] hit `OracleComp.ProgramLogic.wp_replicate_succ`
---
info: [wpstep cache] miss `OracleComp.ProgramLogic.wp_replicate_zero`
-/
#guard_msgs in
  set_option vcvio.vcgen.traceCachedRules true in
  example (oa : OracleComp spec α) (post : List α → ℝ≥0∞) : wp (oa.replicate 0) post = post [] := by
    vcstep


-- @@ L284-292 expanded
/-- info: [vcspec cache] miss `OracleComp.ProgramLogic.TacticInternals.Unary.wp_pure_le_vcspec`
(raw, unaryWP)
-/
#guard_msgs in
  set_option vcvio.vcgen.traceCachedRules true in
  example (x : α) (post : α → ℝ≥0∞) : post x ≤ wp (pure x : OracleComp spec α) post := by vcstep


-- @@ L294-296 expanded
example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp oa (post ∘ f) ≤ wp (f <$> oa) post := by vcstep


-- @@ L298-300 expanded
example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    (if c then wp a post else wp b post) ≤ wp (if c then a else b) post := by vcstep


-- @@ L302-305 expanded
example (c : Prop) [Decidable c] (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α)
    (post : α → ℝ≥0∞) : (if h : c then wp (a h) post else wp (b h) post) ≤ wp (dite c a b) post :=
  by vcstep


-- @@ L307-317 expanded
/-- info: [vcspec cache] miss
`OracleComp.ProgramLogic.TacticInternals.Unary.wp_replicate_succ_le_vcspec`
(raw, unaryWP)
-/
#guard_msgs in
  set_option vcvio.vcgen.traceCachedRules true in
  example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
      wp oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs))) ≤
        wp (oa.replicate (n + 1)) post :=
    by vcstep


-- @@ L319-322 expanded
example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys))) ≤ wp ((x :: xs).mapM f) post := by
  vcstep


-- @@ L324-326 expanded
example (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp ([].mapM f : OracleComp spec (List β)) post = post [] := by vcstep


-- @@ L328-332 expanded
example (x : α) (xs : List α) (f : β → α → OracleComp spec β) (init : β) (post : β → ℝ≥0∞) :
    wp (f init x) (fun s => wp (xs.foldlM f s) post) ≤ wp ((x :: xs).foldlM f init) post := by
  vcstep


-- @@ L334-336 expanded
example (f : β → α → OracleComp spec β) (init : β) (post : β → ℝ≥0∞) :
    wp ([].foldlM f init : OracleComp spec β) post = post init := by vcstep


-- @@ L338-341 expanded
example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    (∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u) ≤
      wp (query t : OracleComp spec (spec.Range t)) post :=
  by vcstep


-- @@ L343-346 expanded
example [SampleableType α] (post : α → ℝ≥0∞) :
    (∑' u : α, probOutput (uniformSample α : ProbComp α) u * post u) ≤
      wp (uniformSample α : ProbComp α) post :=
  by vcstep


-- @@ L348-353 expanded
example (impl : QueryImpl spec (OracleComp spec))
    (hImpl :
      ∀ (t : spec.Domain), evalSPMF (impl t) = evalSPMF (query t : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) : wp (simulateQ impl oa) post = wp oa post := by
  simpa using OracleComp.ProgramLogic.wp_simulateQ_eq impl hImpl oa post


-- @@ L355-355 verbatim
/-! ## Registered `@[vcspec]` theorems -/


-- @@ L357-357 verbatim
@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true


-- @@ L359-362 verbatim
@[local vcspec] theorem triple_wrappedTrue :
    ⦃ 1 ⦄ wrappedTrue (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  simpa [wrappedTrue] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))


-- @@ L364-367 verbatim
example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  vcstep


-- @@ L369-371 verbatim
example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  vcstep


-- @@ L373-376 verbatim
@[local vcspec] theorem stdDoTriple_wrappedTrue :
    Std.Do'.Triple (1 : ℝ≥0∞) (wrappedTrue (spec := spec))
      (fun y => if y = true then (1 : ℝ≥0∞) else 0) Std.Do'.EPost.nil.mk := by
  exact triple_wrappedTrue (spec := spec)


-- @@ L378-380 verbatim
example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  vcstep with stdDoTriple_wrappedTrue


-- @@ L382-385 verbatim
example :
    Std.Do'.Triple (1 : ℝ≥0∞) (wrappedTrue (spec := spec))
      (fun _ => (1 : ℝ≥0∞)) Std.Do'.EPost.nil.mk := by
  vcstep


-- @@ L387-391 verbatim
@[local vcspec] theorem rawWP_wrappedTrue :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.wp (wrappedTrue (spec := spec))
        (fun y => if y = true then (1 : ℝ≥0∞) else 0) Std.Do'.EPost.nil.mk := by
  exact Std.Do'.Triple.iff.mp (stdDoTriple_wrappedTrue (spec := spec))


-- @@ L393-396 verbatim
example :
    (1 : ℝ≥0∞) ⊑
      Std.Do'.wp (wrappedTrue (spec := spec)) (fun _ => (1 : ℝ≥0∞)) Std.Do'.EPost.nil.mk := by
  vcstep


-- @@ L398-398 verbatim
@[irreducible] def wrappedTrueStep : OracleComp spec Bool := pure true


-- @@ L400-403 verbatim
@[local vcspec] theorem triple_wrappedTrueStep (_haux : True) :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  simpa [wrappedTrueStep] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))


-- @@ L405-408 verbatim
example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrueStep (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  vcstep


-- @@ L410-412 verbatim
example :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  vcstep with triple_wrappedTrueStep


-- @@ L414-414 verbatim
@[irreducible] def cacheTraceWrapped : OracleComp spec Bool := pure true


-- @@ L416-420 verbatim
@[local vcspec] theorem triple_cacheTraceWrapped :
    ⦃ 1 ⦄ cacheTraceWrapped (spec := spec)
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  simpa [cacheTraceWrapped] using
    (triple_pure (spec := spec) true (fun y => if y = true then (1 : ℝ≥0∞) else 0))


-- @@ L422-432 verbatim
/--
info: [vcspec cache] hit `triple_cacheTraceWrapped` (folded, unaryTriple)
---
info: [vcspec cache] hit `triple_cacheTraceWrapped` (folded, unaryTriple)
-/
#guard_msgs in
set_option vcvio.vcgen.traceCachedRules true in
example :
    (⦃ (1 : ℝ≥0∞) ⦄ (cacheTraceWrapped (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄) ∧
      (⦃ (1 : ℝ≥0∞) ⦄ (cacheTraceWrapped (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄) := by
  constructor <;> vcstep


-- @@ L434-434 verbatim
/-! ## `liftComp` -/


-- @@ L436-436 verbatim
section LiftComp


-- @@ L438-438 verbatim
variable {ι' : Type} {superSpec : OracleSpec ι'}

-- @@ L439-439 verbatim
variable [IsUniformSpec superSpec]

-- @@ L440-440 expanded
variable [h : SubSpec spec superSpec] [LawfulSubSpec spec superSpec]


-- @@ L442-445 expanded
example (oa : OracleComp spec α) (post : α → ℝ≥0∞) : wp (liftComp oa superSpec) post = wp oa post :=
  by simpa using OracleComp.ProgramLogic.wp_liftComp (spec := spec) (superSpec := superSpec) oa post


-- @@ L447-447 verbatim
end LiftComp
