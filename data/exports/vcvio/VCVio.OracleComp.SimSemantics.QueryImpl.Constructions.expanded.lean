/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.SimSemantics.SimulateQ


-- @@ L12-43 verbatim
/-!
# Basic Constructions of Simulation Oracles

This file defines a number of basic simulation oracles, as well as operations to combine them.

## `preInsert` and `postInsert`

The two main building blocks for instrumented `QueryImpl` values are `preInsert` and
`postInsert`. Both take a base `QueryImpl spec m` and a per-query side effect, and produce
a new `QueryImpl spec n` that wraps the base with that side effect:

* `preInsert  so nx` runs `nx t` *before* the handler `so t`. The side effect happens
  unconditionally, including when the handler later fails.
* `postInsert so nx` runs `nx t u` *after* the handler returns response `u`, so the side
  effect can depend on the response and is skipped when the handler fails.

Both come with a complete generic theory, parametric in a projection
`proj : ∀ {γ}, n γ → m γ` that strips the instrumentation: `proj_simulateQ_preInsert`,
`probFailure_proj_simulateQ_preInsert`, `NeverFail_proj_simulateQ_preInsert_iff`,
`evalSPMF_proj_simulateQ_preInsert`, `probOutput_proj_simulateQ_preInsert`,
`support_proj_simulateQ_preInsert`, `finSupport_proj_simulateQ_preInsert`, and the
induction principle `simulateQ_preInsert.induct` (with `postInsert` analogues). Query-bound
transfer through these wrappers lives in `QueryTracking/QueryBound.lean`.

Most of the wrappers in `QueryTracking/` (`withTraceBefore`, `withTrace`,
`withTraceAppendBefore`, `withTraceAppend`, `withCost`, `withCounting`, `withAddCost`,
`withUnitCost`, `withLogging`, `appendInputLog`) bottom out at these combinators. New
instrumentation should follow the same pattern when its shape is "for each query, run a
side effect and delegate" — wrappers whose control flow is conditional on external state
or the would-be response (cache-on-hit, seed fallback, budget gating) genuinely need a
custom `QueryImpl` and stay outside this hierarchy.
-/


-- @@ L45-45 verbatim
@[expose] public section


-- @@ L47-47 verbatim
open OracleSpec OracleComp Prod Sum


-- @@ L49-49 verbatim
universe u v w


-- @@ L51-51 verbatim
namespace QueryImpl


-- @@ L53-53 verbatim
section compose


-- @@ L55-57 verbatim
variable {m : Type u → Type v} [Monad m]
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α β γ : Type u}


-- @@ L59-63 verbatim
/-- Given an implementation of `spec` in terms of a new set of oracles `spec'`,
and an implementation of `spec'` in terms of arbitrary `m`, implement `spec` in terms of `m`. -/
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m :=
  fun t => simulateQ so' (so t)


-- @@ L65-65 verbatim
infixl : 65 " ∘ₛ " => QueryImpl.compose


-- @@ L67-69 expanded
@[simp]
lemma apply_compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec'))
    (t : spec.Domain) : (QueryImpl.compose so' so) t = simulateQ so' (so t) :=
  rfl


-- @@ L71-75 expanded
@[simp]
lemma simulateQ_compose [LawfulMonad m] (so' : QueryImpl spec' m)
    (so : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    simulateQ (QueryImpl.compose so' so) oa = simulateQ so' (simulateQ so oa) := by
  induction oa using OracleComp.inductionOn <;> simp_all


-- @@ L77-79 expanded
@[simp]
lemma compose_id' [LawfulMonad m] (so : QueryImpl spec m) :
    QueryImpl.compose so (QueryImpl.id' spec) = so := by ext x; simp


-- @@ L81-81 verbatim
end compose


-- @@ L83-83 verbatim
section insertPre


-- @@ L85-87 verbatim
variable {m : Type u → Type v}
    {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι} {α β γ : Type u}


-- @@ L89-92 verbatim
/-- Oracle-facing compatibility alias for `PFunctor.Handler.preInsert`. -/
abbrev preInsert (so : QueryImpl spec m) (nx : spec.Domain → n α) :
    QueryImpl spec n :=
  PFunctor.Handler.preInsert (P := spec.toPFunctor) so nx


-- @@ L94-98 verbatim
@[grind =]
lemma preInsert_apply [LawfulMonad n] (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    so.preInsert nx t = (do let _ ← nx t; liftM (so t)) := by
  simp [preInsert, seqRight_eq, monad_norm]


-- @@ L100-107 verbatim
/-- One-step characterisation of `simulateQ (preInsert so nx)` on a single query. -/
lemma simulateQ_preInsert_query [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (t : spec.Domain) :
    simulateQ (so.preInsert nx) (query t) = (do let _ ← nx t; liftM (so t)) := by
  have h : simulateQ (so.preInsert nx) (query t) = so.preInsert nx t := by
    simp
  exact h.trans (preInsert_apply so nx t)


-- @@ L109-136 verbatim
/-- Induction principle for `proj (simulateQ (so.preInsert nx) oa)` parametric in a
motive `OracleComp spec β → m β → Prop`. The recursion structure of
`proj_simulateQ_preInsert` is exposed as two cases mirroring `OracleComp.inductionOn`:
in `pure x` the projected term reduces to `pure x`, and in `query t >>= k` it reduces
to `so t >>= k'` for some continuation `k' u = proj (simulateQ (so.preInsert nx) (k u))`.
Tagged `@[elab_as_elim]` so it is usable as `induction oa using simulateQ_preInsert.induct`. -/
@[elab_as_elim]
lemma simulateQ_preInsert.induct [Monad m] [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    {motive : OracleComp spec β → m β → Prop}
    (h_pure : ∀ (x : β), motive (pure x : OracleComp spec β) (pure x))
    (h_query_bind : ∀ (t : spec.Domain) (k : spec.Range t → OracleComp spec β)
        (k' : spec.Range t → m β),
        (∀ u, motive (k u) (k' u)) → motive (query t >>= k) (so t >>= k'))
    (oa : OracleComp spec β) :
    motive oa (proj (simulateQ (so.preInsert nx) oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [simulateQ_pure, hproj_pure]
      exact h_pure x
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_spec_query, hproj_bind, hproj_apply]
      exact h_query_bind t k _ ih


-- @@ L138-156 verbatim
/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `preInsert so nx` and projecting back recovers `simulateQ so`. The proof
is the canonical use of `simulateQ_preInsert.induct`: the parametric motive is instantiated
to the equality with `simulateQ so oa`, leaving trivial cases. -/
lemma proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.preInsert nx) oa) = simulateQ so oa := by
  induction oa using simulateQ_preInsert.induct so nx proj hproj_pure hproj_bind hproj_apply with
  | h_pure x => rfl
  | h_query_bind t k k' ih =>
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
      exact bind_congr ih


-- @@ L158-171 expanded
/-- A `preInsert` instrumentation preserves failure probability for any base monad with
`[MonadLiftT m SPMF]`, given the projection bundle and its compatibility with failure
probabilities. -/
lemma probFailure_proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t) (oa : OracleComp spec β) :
    probFailure (proj (simulateQ (so.preInsert nx) oa)) = probFailure (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L173-184 verbatim
/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_preInsert`. -/
lemma neverFail_proj_simulateQ_preInsert_iff [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.preInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L186-195 verbatim
/-- When `nx` is constantly `pure x`, `preInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTraceBefore_const_one` no-op identity. -/
lemma simulateQ_preInsert_const_pure [Monad m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.preInsert (fun _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  have h : so.preInsert (fun _ => (pure x : n α)) = so.liftTarget n := by
    funext t; simp
  rw [h, simulateQ_liftTarget]


-- @@ L197-197 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `preInsert` -/


-- @@ L199-209 expanded
lemma evalSPMF_proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t) (oa : OracleComp spec β) :
    evalSPMF (proj (simulateQ (so.preInsert nx) oa)) = evalSPMF (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L211-221 expanded
lemma probOutput_proj_simulateQ_preInsert [Monad m] [LawfulMonad m] [LawfulMonad n]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t) (oa : OracleComp spec β) (x : β) :
    probOutput (proj (simulateQ (so.preInsert nx) oa)) x = probOutput (simulateQ so oa) x := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L223-233 verbatim
lemma support_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    support (proj (simulateQ (so.preInsert nx) oa)) = support (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L235-245 verbatim
lemma finSupport_proj_simulateQ_preInsert [Monad m]
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SetM] [HasEvalFinset m] [DecidableEq β]
    (so : QueryImpl spec m) (nx : spec.Domain → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.preInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    finSupport (proj (simulateQ (so.preInsert nx) oa)) = finSupport (simulateQ so oa) := by
  rw [proj_simulateQ_preInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L247-247 verbatim
end insertPre


-- @@ L249-249 verbatim
section insertPost


-- @@ L251-253 verbatim
variable {m : Type u → Type v} [Monad m]
    {n : Type u → Type w} [Monad n] [MonadLiftT m n]
    {ι : Type*} {spec : OracleSpec ι}


-- @@ L255-259 verbatim
/-- Oracle-facing compatibility alias for `PFunctor.Handler.postInsert`. -/
abbrev postInsert (so : QueryImpl spec m) {α}
    (nx : (t : spec.Domain) → spec.Range t → n α) :
    QueryImpl spec n :=
  PFunctor.Handler.postInsert (P := spec.toPFunctor) so nx


-- @@ L261-261 verbatim
variable {α β : Type u}


-- @@ L263-268 verbatim
omit [Monad m] in
@[grind =]
lemma postInsert_apply (so : QueryImpl spec m)
    (nx : (t : spec.Domain) → spec.Range t → n α) (t : spec.Domain) :
    so.postInsert nx t = (do let u ← liftM (so t); let _ ← nx t u; return u) := by
  exact PFunctor.Handler.postInsert_apply (P := spec.toPFunctor) so nx t


-- @@ L270-277 verbatim
omit [Monad m] in
/-- One-step characterisation of `simulateQ (postInsert so nx)` on a single query. -/
lemma simulateQ_postInsert_query [LawfulMonad n]
    (so : QueryImpl spec m)
    (nx : (t : spec.Domain) → spec.Range t → n α) (t : spec.Domain) :
    simulateQ (so.postInsert nx) (query t) =
      (do let u ← liftM (so t); let _ ← nx t u; return u) := by
  simp


-- @@ L279-306 verbatim
/-- Induction principle for `proj (simulateQ (so.postInsert nx) oa)` parametric in a
motive `OracleComp spec β → m β → Prop`. The recursion structure of
`proj_simulateQ_postInsert` is exposed as two cases mirroring `OracleComp.inductionOn`:
in `pure x` the projected term reduces to `pure x`, and in `query t >>= k` it reduces
to `so t >>= k'` for some continuation `k' u = proj (simulateQ (so.postInsert nx) (k u))`.
Tagged `@[elab_as_elim]` so it is usable as `induction oa using simulateQ_postInsert.induct`. -/
@[elab_as_elim]
lemma simulateQ_postInsert.induct [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    {motive : OracleComp spec β → m β → Prop}
    (h_pure : ∀ (x : β), motive (pure x : OracleComp spec β) (pure x))
    (h_query_bind : ∀ (t : spec.Domain) (k : spec.Range t → OracleComp spec β)
        (k' : spec.Range t → m β),
        (∀ u, motive (k u) (k' u)) → motive (query t >>= k) (so t >>= k'))
    (oa : OracleComp spec β) :
    motive oa (proj (simulateQ (so.postInsert nx) oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rw [simulateQ_pure, hproj_pure]
      exact h_pure x
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_spec_query, hproj_bind, hproj_apply]
      exact h_query_bind t k _ ih


-- @@ L308-326 verbatim
/-- Generic strip lemma: given a monad-morphism-style projection `proj : ∀ {γ}, n γ → m γ`
that preserves `pure` and `bind` and discards the inserted side effect on each query,
simulating with `postInsert so nx` and projecting back recovers `simulateQ so`. The proof
is the canonical use of `simulateQ_postInsert.induct`: the parametric motive is instantiated
to the equality with `simulateQ so oa`, leaving trivial cases. -/
lemma proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    proj (simulateQ (so.postInsert nx) oa) = simulateQ so oa := by
  induction oa using simulateQ_postInsert.induct so nx proj hproj_pure hproj_bind hproj_apply with
  | h_pure x => rfl
  | h_query_bind t k k' ih =>
      simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query]
      exact bind_congr ih


-- @@ L328-341 expanded
/-- A `postInsert` instrumentation preserves failure probability for any base monad with
`[MonadLiftT m SPMF]`, given the projection bundle and its compatibility with failure
probabilities. -/
lemma probFailure_proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t) (oa : OracleComp spec β) :
    probFailure (proj (simulateQ (so.postInsert nx) oa)) = probFailure (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L343-354 verbatim
/-- `NeverFail` biconditional companion of `probFailure_proj_simulateQ_postInsert`. -/
lemma neverFail_proj_simulateQ_postInsert_iff
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    NeverFail (proj (simulateQ (so.postInsert nx) oa)) ↔ NeverFail (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L356-364 verbatim
/-- When `nx` is constantly `pure x`, `postInsert so nx` is the lift of `so` and the
resulting simulation equals the lifted underlying simulation. Generic analogue of the
`run_simulateQ_withTrace_const_one` no-op identity. -/
lemma simulateQ_postInsert_const_pure
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    (so : QueryImpl spec m) (x : α) (oa : OracleComp spec β) :
    simulateQ (so.postInsert (fun _ _ => (pure x : n α))) oa = liftM (simulateQ so oa) := by
  have h : so.postInsert (fun _ _ => (pure x : n α)) = so.liftTarget n := by funext t; simp
  rw [h, simulateQ_liftTarget]


-- @@ L366-366 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `postInsert` -/


-- @@ L368-378 expanded
lemma evalSPMF_proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t) (oa : OracleComp spec β) :
    evalSPMF (proj (simulateQ (so.postInsert nx) oa)) = evalSPMF (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L380-390 expanded
lemma probOutput_proj_simulateQ_postInsert [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind :
      ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ), proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t) (oa : OracleComp spec β) (x : β) :
    probOutput (proj (simulateQ (so.postInsert nx) oa)) x = probOutput (simulateQ so oa) x := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L392-402 verbatim
lemma support_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    support (proj (simulateQ (so.postInsert nx) oa)) = support (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L404-414 verbatim
lemma finSupport_proj_simulateQ_postInsert
    [LawfulMonad m] [LawfulMonad n] [MonadLiftT m SetM] [HasEvalFinset m] [DecidableEq β]
    (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α)
    (proj : ∀ {γ : Type u}, n γ → m γ)
    (hproj_pure : ∀ {γ : Type u} (x : γ), proj (pure x : n γ) = pure x)
    (hproj_bind : ∀ {γ δ : Type u} (b : n γ) (f : γ → n δ),
        proj (b >>= f) = proj b >>= fun x => proj (f x))
    (hproj_apply : ∀ t, proj ((so.postInsert nx) t) = so t)
    (oa : OracleComp spec β) :
    finSupport (proj (simulateQ (so.postInsert nx) oa)) = finSupport (simulateQ so oa) := by
  rw [proj_simulateQ_postInsert so nx proj hproj_pure hproj_bind hproj_apply]


-- @@ L416-416 verbatim
end insertPost


-- @@ L418-418 verbatim
end QueryImpl
