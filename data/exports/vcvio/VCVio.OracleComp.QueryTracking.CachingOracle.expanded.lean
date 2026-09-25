/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection


-- @@ L14-22 verbatim
/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define `cachingOracle`, which caches queries to the oracles in `spec`,
querying fresh values from `spec` if no cached value exists.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open OracleComp OracleSpec


-- @@ L28-28 verbatim
universe u v w


-- @@ L30-30 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L32-32 verbatim
variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}


-- @@ L34-34 verbatim
namespace QueryImpl


-- @@ L36-36 verbatim
variable {m : Type u → Type v} [Monad m]


-- @@ L38-44 verbatim
/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) :=
  fun t => do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)


-- @@ L46-51 verbatim
@[simp] lemma withCaching_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCaching t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl


-- @@ L53-56 verbatim
lemma withCaching_run_some [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {cache : spec.QueryCache} {u : spec.Range t} (hcache : cache t = some u) :
    (so.withCaching t).run cache = pure (u, cache) := by
  simp [hcache]


-- @@ L58-62 verbatim
lemma withCaching_run_none [LawfulMonad m] (so : QueryImpl spec m) {t : spec.Domain}
    {cache : spec.QueryCache} (hcache : cache t = none) :
    (so.withCaching t).run cache =
      (fun u => (u, cache.cacheQuery t u)) <$> so t := by
  simp [hcache]


-- @@ L64-64 verbatim
/-! ## Caching with auxiliary state -/


-- @@ L66-66 verbatim
section CachingAux


-- @@ L68-68 verbatim
variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m']


-- @@ L70-85 verbatim
/-- Cache responses while threading an auxiliary state component.

The cache is consulted first. On a hit, the cached response is returned and the auxiliary state is
updated by `hit`. On a miss, `miss` produces both the response and the next auxiliary state; the
response is then installed in the cache. -/
def withCachingAux
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q)) :
    QueryImpl spec (StateT (spec.QueryCache × Q) m') :=
  fun t => StateT.mk fun s =>
    match s with
    | (cache, q) =>
        match cache t with
        | some u => pure (u, (cache, hit t u cache q))
        | none => (fun p : spec.Range t × Q => (p.1, (cache.cacheQuery t p.1, p.2))) <$>
            miss t cache q


-- @@ L87-97 verbatim
@[simp, grind =]
lemma withCachingAux_apply
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q))
    (t : spec.Domain) (s : spec.QueryCache × Q) :
    (withCachingAux (spec := spec) hit miss t).run s =
      (match s.1 t with
      | some u => pure (u, (s.1, hit t u s.1 s.2))
      | none =>
          (fun p : spec.Range t × Q => (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
            miss t s.1 s.2) := rfl


-- @@ L99-99 verbatim
end CachingAux


-- @@ L101-101 verbatim
section CacheAuxProjection


-- @@ L103-103 verbatim
variable {Q : Type u}

-- @@ L104-104 verbatim
variable [LawfulMonad m]


-- @@ L106-120 verbatim
/-- Projecting away the auxiliary state of `withCachingAux` recovers ordinary caching whenever
the miss handler has the same output marginal as the base implementation. -/
theorem withCachingAux_run_proj_eq
    (base : QueryImpl spec m)
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m (spec.Range t × Q))
    (hmiss : ∀ t cache q, Prod.fst <$> miss t cache q = base t)
    {α : Type u} (oa : OracleComp spec α) (cache : spec.QueryCache) (q : Q) :
    Prod.map id Prod.fst <$> (simulateQ (withCachingAux hit miss) oa).run (cache, q) =
      (simulateQ base.withCaching oa).run cache := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (impl₁ := withCachingAux hit miss) (impl₂ := base.withCaching)
    (proj := Prod.fst) ?_ oa (cache, q)
  intro t ⟨cache', q'⟩
  cases hcache : cache' t <;> simp [withCachingAux_apply, hcache, ← hmiss t cache' q']


-- @@ L122-136 verbatim
/-- Output-only corollary of `withCachingAux_run_proj_eq`. -/
theorem withCachingAux_run'_eq
    (base : QueryImpl spec m)
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m (spec.Range t × Q))
    (hmiss : ∀ t cache q, Prod.fst <$> miss t cache q = base t)
    {α : Type u} (oa : OracleComp spec α) (cache : spec.QueryCache) (q : Q) :
    (simulateQ (withCachingAux hit miss) oa).run' (cache, q) =
      (simulateQ base.withCaching oa).run' cache := by
  have hmap := congrArg (Prod.fst <$> ·)
    (withCachingAux_run_proj_eq base hit miss hmiss oa cache q)
  rw [StateT.run', StateT.run']
  change (fun a => id a.1) <$> (simulateQ (withCachingAux hit miss) oa).run (cache, q) =
    Prod.fst <$> (simulateQ base.withCaching oa).run cache
  simpa only [Functor.map_map, Function.comp_def, Prod.map] using hmap


-- @@ L138-138 verbatim
end CacheAuxProjection


-- @@ L140-140 verbatim
section CachingAuxInvariant


-- @@ L142-143 verbatim
variable {Q : Type w} {m' : Type (max u w) → Type v} [Monad m'] [LawfulMonad m']
  [MonadLiftT m' SetM] [LawfulMonadLiftT m' SetM]


-- @@ L145-164 verbatim
/-- One-step invariant preservation for the auxiliary component of `withCachingAux`. -/
theorem withCachingAux_aux_inv_of_mem
    (hit : (t : spec.Domain) → spec.Range t → spec.QueryCache → Q → Q)
    (miss : (t : spec.Domain) → spec.QueryCache → Q → m' (spec.Range t × Q))
    (inv : Q → Prop)
    (hhit : ∀ t u cache q, inv q → inv (hit t u cache q))
    (hmiss : ∀ t cache q, inv q → ∀ p ∈ support (miss t cache q), inv p.2)
    {t : spec.Domain} {cache : spec.QueryCache} {q : Q}
    {z : spec.Range t × spec.QueryCache × Q}
    (hq : inv q) (hz : z ∈ support ((withCachingAux hit miss t).run (cache, q))) :
    inv z.2.2 := by
  rw [withCachingAux_apply] at hz
  cases hcache : cache t with
  | some u =>
      simp only [hcache, support_pure, Set.mem_singleton_iff] at hz
      exact hz ▸ hhit t u cache q hq
  | none =>
      simp only [hcache, support_map] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      exact hmiss t cache q hq p hp


-- @@ L166-166 verbatim
end CachingAuxInvariant


-- @@ L168-179 verbatim
/-- A `withCachingAux` handler preserves an invariant on its auxiliary component when both hit and
miss auxiliary updates preserve it. -/
theorem PreservesInv.withCachingAux_aux
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀} {Q₀ : Type}
    (hit : (t : spec₀.Domain) → spec₀.Range t → spec₀.QueryCache → Q₀ → Q₀)
    (miss : (t : spec₀.Domain) → spec₀.QueryCache → Q₀ → ProbComp (spec₀.Range t × Q₀))
    (inv : Q₀ → Prop)
    (hhit : ∀ t u cache q, inv q → inv (hit t u cache q))
    (hmiss : ∀ t cache q, inv q → ∀ p ∈ support (miss t cache q), inv p.2) :
    QueryImpl.PreservesInv (withCachingAux hit miss)
      (fun s : spec₀.QueryCache × Q₀ => inv s.2) :=
  fun _ _ hq _ hz => withCachingAux_aux_inv_of_mem hit miss inv hhit hmiss hq hz


-- @@ L181-181 verbatim
section CacheMonotonicity


-- @@ L183-183 verbatim
variable [spec.DecidableEq]


-- @@ L185-199 verbatim
omit [spec.DecidableEq] in
/-- Running `withCaching` at state `cache` produces a result whose cache is `≥ cache`.
On a cache hit the state is unchanged; on a miss a single entry is added. -/
lemma withCaching_cache_le [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (so : QueryImpl spec m) (t : spec.Domain) (cache₀ : QueryCache spec)
    (z) (hz : z ∈ support ((so.withCaching t).run cache₀)) :
    cache₀ ≤ z.2 := by
  cases ht : cache₀ t with
  | some u =>
    rw [withCaching_run_some so ht, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    rw [withCaching_run_none so ht, support_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact QueryCache.le_cacheQuery cache₀ ht


-- @@ L201-206 verbatim
/-- `withCaching` preserves the invariant `(cache₀ ≤ ·)` (the cache only grows). -/
lemma PreservesInv.withCaching_le {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [spec₀.DecidableEq]
    (so : QueryImpl spec₀ ProbComp) (cache₀ : QueryCache spec₀) :
    QueryImpl.PreservesInv (so.withCaching) (cache₀ ≤ ·) :=
  fun t cache hle z hz => hle.trans (withCaching_cache_le so t cache z hz)


-- @@ L208-208 verbatim
end CacheMonotonicity


-- @@ L210-213 verbatim
/-! ## Forward query bounds for `withCaching`

A wrapped step makes ≤ 1 underlying query (zero on a hit, one on a miss), so any bound on
`so t` transfers to `(so.withCaching t).run cache`. -/


-- @@ L215-215 verbatim
section QueryBound


-- @@ L217-217 verbatim
variable {ι' : Type u} {spec' : OracleSpec ι'}


-- @@ L219-230 verbatim
lemma isQueryBoundP_run_withCaching
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    {p : ι' → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP (so t) p n) (cache : spec.QueryCache) :
    OracleComp.IsQueryBoundP ((so.withCaching t).run cache) p n := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isQueryBoundP_map_iff (p := p) _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial


-- @@ L232-242 verbatim
lemma isTotalQueryBound_run_withCaching
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain) {n : ℕ}
    (h : OracleComp.IsTotalQueryBound (so t) n) (cache : spec.QueryCache) :
    OracleComp.IsTotalQueryBound ((so.withCaching t).run cache) n := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial


-- @@ L244-254 verbatim
lemma isPerIndexQueryBound_run_withCaching [IsUniformSpec spec]
    (so : QueryImpl spec (OracleComp spec)) (t : spec.Domain) {qb : ι → ℕ}
    (h : OracleComp.IsPerIndexQueryBound (so t) qb) (cache : spec.QueryCache) :
    OracleComp.IsPerIndexQueryBound ((so.withCaching t).run cache) qb := by
  cases hcache : cache t with
  | none =>
      rw [withCaching_run_none _ hcache]
      exact (OracleComp.isPerIndexQueryBound_map_iff _ _ _).mpr h
  | some u =>
      rw [withCaching_run_some _ hcache]
      trivial


-- @@ L256-256 verbatim
end QueryBound


-- @@ L258-258 verbatim
end QueryImpl


-- @@ L260-260 verbatim
/-! ### Parametric `simulateQ` lifts for `withCaching` -/


-- @@ L262-262 verbatim
namespace OracleComp


-- @@ L264-265 verbatim
variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}
  {ι' : Type u} {spec' : OracleSpec ι'} [IsUniformSpec spec'] {α : Type u}


-- @@ L267-279 verbatim
theorem IsQueryBoundP.simulateQ_run_withCaching
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (so t) q 0)
    (cache : spec.QueryCache) :
    IsQueryBoundP ((simulateQ so.withCaching oa).run cache) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp => QueryImpl.isQueryBoundP_run_withCaching so t (hstep_p t hp))
    (fun t hnp => QueryImpl.isQueryBoundP_run_withCaching so t (hstep_np t hnp))
    cache


-- @@ L281-290 verbatim
theorem IsTotalQueryBound.simulateQ_run_withCaching
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t, IsTotalQueryBound (so t) 1)
    (cache : spec.QueryCache) :
    IsTotalQueryBound ((simulateQ so.withCaching oa).run cache) n :=
  IsTotalQueryBound.simulateQ_run_of_step h
    (fun t => QueryImpl.isTotalQueryBound_run_withCaching so t (hstep t))
    cache


-- @@ L292-301 verbatim
theorem IsPerIndexQueryBound.simulateQ_run_withCaching [IsUniformSpec spec]
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t, IsPerIndexQueryBound (so t) (Function.update 0 t 1))
    (cache : spec.QueryCache) :
    IsPerIndexQueryBound ((simulateQ so.withCaching oa).run cache) qb :=
  IsPerIndexQueryBound.simulateQ_run_of_uniform_step h
    (fun t => QueryImpl.isPerIndexQueryBound_run_withCaching so t (hstep t))
    cache


-- @@ L303-303 verbatim
end OracleComp


-- @@ L305-308 verbatim
/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def OracleSpec.cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching


-- @@ L310-310 verbatim
namespace cachingOracle


-- @@ L312-315 verbatim
/-- Definitional unfold of `cachingOracle` as caching wrapped around the lifting handler. -/
lemma eq_withCaching :
    (spec.cachingOracle : QueryImpl spec (StateT spec.QueryCache (OracleComp spec))) =
      (QueryImpl.ofLift spec (OracleComp spec)).withCaching := rfl


-- @@ L317-322 expanded
lemma apply_eq (t : spec.Domain) :
    cachingOracle t =
      (do
        match (← get) t with
        | Option.some u =>
          return u
        | Option.none =>
          let u ← OracleSpec.query t
          modifyGet fun cache => (u, cache.cacheQuery t u)) :=
  rfl


-- @@ L324-327 verbatim
/-- Cache hit: `cachingOracle t` returns the stored value without an underlying query. -/
lemma run_some {t : spec.Domain} {cache : spec.QueryCache} {u : spec.Range t}
    (h : cache t = some u) : (cachingOracle t).run cache = pure (u, cache) :=
  QueryImpl.withCaching_run_some _ h


-- @@ L329-333 expanded
/-- Cache miss: `cachingOracle t` issues a single underlying `query t` and stores it. -/
lemma run_none {t : spec.Domain} {cache : spec.QueryCache} (h : cache t = none) :
    (cachingOracle t).run cache =
      (fun u => (u, cache.cacheQuery t u)) <$> (liftM (OracleSpec.query t) : OracleComp spec _) :=
  by rw [eq_withCaching, QueryImpl.withCaching_run_none _ h, QueryImpl.ofLift_apply]


-- @@ L335-342 expanded
/-- Trivially true via `probFailure_eq_zero` since both sides are `OracleComp` computations.
A generic `withCaching` version for arbitrary base monads would require a separate argument
because caching changes the oracle semantics (cache hits skip the underlying oracle call). -/
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    probFailure ((simulateQ spec₀.cachingOracle oa).run cache) = probFailure oa := by simp


-- @@ L344-350 verbatim
/-- Trivially true via `probFailure_eq_zero`; see `probFailure_run_simulateQ`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type}
    (oa : OracleComp spec₀ α) (cache : QueryCache spec₀) :
    NeverFail ((simulateQ spec₀.cachingOracle oa).run cache) ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff, probFailure_run_simulateQ]


-- @@ L352-354 expanded
lemma simulateQ_query (t : spec.Domain) :
    simulateQ cachingOracle (liftM (OracleSpec.query t)) = cachingOracle t := by
  simp [_root_.simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]


-- @@ L356-358 verbatim
/-! ### Forward query bounds for `cachingOracle`

Forward only — the reverse fails because cache hits strictly reduce the simulated count. -/


-- @@ L360-366 verbatim
theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [IsUniformSpec spec₀] {α : Type}
    {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) (cache : spec₀.QueryCache) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.cachingOracle oa).run cache) n :=
  OracleComp.IsTotalQueryBound.simulateQ_run_withCaching _ h
    (fun t => (OracleComp.isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) cache


-- @@ L368-376 verbatim
theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [IsUniformSpec spec₀] {α : Type}
    {oa : OracleComp spec₀ α} {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n) (cache : spec₀.QueryCache) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.cachingOracle oa).run cache) p n :=
  OracleComp.IsQueryBoundP.simulateQ_run_withCaching _ h
    (fun t _ => (OracleComp.isQueryBoundP_query_iff p t 1).mpr (fun _ => Nat.one_pos))
    (fun t hnp => (OracleComp.isQueryBoundP_query_iff p t 0).mpr (fun hpt => absurd hpt hnp))
    cache


-- @@ L378-385 verbatim
theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [IsUniformSpec spec₀] {α : Type}
    {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb) (cache : spec₀.QueryCache) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.cachingOracle oa).run cache) qb :=
  OracleComp.IsPerIndexQueryBound.simulateQ_run_withCaching _ h
    (fun t => (OracleComp.isPerIndexQueryBound_query_iff t (Function.update 0 t 1)).mpr (by
      simp [Function.update_self])) cache


-- @@ L387-387 verbatim
end cachingOracle


-- @@ L389-389 verbatim
section withCacheOverlay


-- @@ L391-410 verbatim
/-- Run an `OracleComp` with a `QueryCache` as a priority layer over the real oracle.
Cached entries are returned directly (no oracle query), misses fall through to the real
oracle and get cached for subsequent lookups within the same computation.

This is the fundamental "programmable random oracle" primitive: pre-fill the cache with
programmed entries, then run the computation. Concretely:

  `withCacheOverlay cache oa = StateT.run' (simulateQ cachingOracle oa) cache`

Key properties:
- `withCacheOverlay ∅ oa` deduplicates queries but is otherwise equivalent to `oa`.
- `withCacheOverlay cache (query t)` returns `v` without an external query when
  `cache t = some v`, and queries the real oracle when `cache t = none`.

The cache-parametric runtime built on top of this combinator lives in
`VCVio.CryptoFoundations.FiatShamir.Sigma` as `FiatShamir.runtimeWithCache cache`, with
`FiatShamir.runtime` defined as `runtimeWithCache ∅`. -/
def OracleSpec.withCacheOverlay {α : Type u} (cache : spec.QueryCache) (oa : OracleComp spec α) :
    OracleComp spec α :=
  StateT.run' (simulateQ spec.cachingOracle oa) cache


-- @@ L412-415 verbatim
@[simp]
lemma withCacheOverlay_pure {α : Type u} (cache : spec.QueryCache) (a : α) :
    withCacheOverlay cache (pure a : OracleComp spec α) = pure a := by
  simp [withCacheOverlay]


-- @@ L417-427 verbatim
lemma withCacheOverlay_bind {α β : Type u} (cache : spec.QueryCache)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    withCacheOverlay cache (oa >>= ob) =
      ((simulateQ cachingOracle oa).run cache >>= fun p =>
        withCacheOverlay p.2 (ob p.1)) := by
  simp only [withCacheOverlay, simulateQ_bind, StateT.run']
  change Prod.fst <$> (((simulateQ cachingOracle oa >>=
    fun x => simulateQ cachingOracle (ob x)) :
      StateT (QueryCache spec) (OracleComp spec) β).run cache) = _
  rw [StateT.run_bind, map_bind]
  rfl


-- @@ L429-433 verbatim
lemma withCacheOverlay_map {α β : Type u} (cache : spec.QueryCache)
    (f : α → β) (oa : OracleComp spec α) :
    withCacheOverlay cache (f <$> oa) = f <$> withCacheOverlay cache oa := by
  rw [map_eq_bind_pure_comp, withCacheOverlay_bind]
  simp [withCacheOverlay]


-- @@ L435-444 verbatim
lemma withCacheOverlay_bind_pure {α β : Type u} (cache : spec.QueryCache)
    (oa : OracleComp spec α) (f : α → β) :
    withCacheOverlay cache (oa >>= fun x => pure (f x)) =
      f <$> withCacheOverlay cache oa := by
  calc
    withCacheOverlay cache (oa >>= fun x => pure (f x)) =
        withCacheOverlay cache (f <$> oa) := by
      rw [map_eq_bind_pure_comp]
      rfl
    _ = _ := withCacheOverlay_map cache f oa


-- @@ L446-449 verbatim
private lemma fst_map_cachingOracle_run_some (cache : spec.QueryCache) (t : spec.Domain)
    (v : spec.Range t) (hv : cache t = some v) :
    Prod.fst <$> (cachingOracle t).run cache = pure v := by
  rw [cachingOracle.run_some hv, map_pure]


-- @@ L451-456 expanded
private lemma fst_map_cachingOracle_run_none (cache : spec.QueryCache) (t : spec.Domain)
    (hv : cache t = none) :
    Prod.fst <$> (cachingOracle t).run cache =
      (OracleSpec.query t : OracleComp spec (spec.Range t)) :=
  by
  rw [cachingOracle.run_none hv]
  simp


-- @@ L458-463 expanded
lemma withCacheOverlay_query_hit (cache : spec.QueryCache) (t : spec.Domain) (v : spec.Range t)
    (hv : cache t = some v) :
    withCacheOverlay cache (OracleSpec.query t : OracleComp spec (spec.Range t)) = pure v :=
  by
  change
    Prod.fst <$>
        (simulateQ cachingOracle (OracleSpec.query t : OracleComp spec (spec.Range t))).run cache =
      _
  rw [cachingOracle.simulateQ_query, fst_map_cachingOracle_run_some cache t v hv]


-- @@ L465-470 expanded
lemma withCacheOverlay_query_miss (cache : spec.QueryCache) (t : spec.Domain)
    (hv : cache t = none) :
    withCacheOverlay cache (OracleSpec.query t : OracleComp spec (spec.Range t)) =
      OracleSpec.query t :=
  by
  change
    Prod.fst <$>
        (simulateQ cachingOracle (OracleSpec.query t : OracleComp spec (spec.Range t))).run cache =
      _
  rw [cachingOracle.simulateQ_query, fst_map_cachingOracle_run_none cache t hv]


-- @@ L472-472 verbatim
end withCacheOverlay


-- @@ L474-474 verbatim
namespace OracleComp


-- @@ L476-476 verbatim
variable [spec.DecidableEq]


-- @@ L478-496 verbatim
omit [spec.DecidableEq] in
/-- `simulateQ cachingOracle` only grows the cache: for any `oa`, if
`z ∈ support ((simulateQ cachingOracle oa).run cache₀)` then `cache₀ ≤ z.2`. -/
theorem simulateQ_cachingOracle_cache_le {α : Type u}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec)
    (z : α × QueryCache spec)
    (hmem : z ∈ support ((simulateQ cachingOracle oa).run cache₀)) :
    cache₀ ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure a =>
      simp only [StateT.run, simulateQ_pure] at hmem
      obtain rfl := hmem
      exact le_rfl
  | query_bind t mx ih =>
      simp only [simulateQ_query_bind, StateT.run_bind] at hmem
      rw [mem_support_bind_iff] at hmem
      obtain ⟨⟨u, cache_mid⟩, hmid, hrest⟩ := hmem
      have hle_mid : cache₀ ≤ cache_mid := QueryImpl.withCaching_cache_le _ _ cache₀ _ hmid
      exact hle_mid.trans (ih _ cache_mid z hrest)


-- @@ L498-518 verbatim
omit [spec.DecidableEq] in
/-- After running `cachingOracle` on a single query at `t`, the resulting cache
maps `t` to the returned value. -/
theorem cachingOracle_query_caches (t : spec.Domain)
    (cache₀ : QueryCache spec)
    (v : spec.Range t) (cache₁ : QueryCache spec)
    (hmem : (v, cache₁) ∈ support ((cachingOracle t).run cache₀)) :
    cache₁ t = some v := by
  simp only [cachingOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind] at hmem
  cases hc : cache₀ t with
  | some u =>
    simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact hc
  | none =>
    simp only [hc, StateT.run_bind, StateT.run_monadLift, monad_norm] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨u, _, hmem⟩ := hmem
    simp only [StateT.run_modifyGet, support_pure, Set.mem_singleton_iff] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact QueryCache.cacheQuery_self cache₀ t v


-- @@ L520-520 verbatim
end OracleComp
