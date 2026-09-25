/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.LoggingOracle


-- @@ L11-24 verbatim
/-!
# Combined Caching + Logging Handlers

This file packages the concrete "cache plus append-log" handlers that are
useful in proof developments but should live below `ProgramLogic`.

`QueryImpl.withCachingTraceAppend` is the generic transformer: it threads a
`QueryCache spec × ω` state, reuses cached answers on hits, falls back to the
underlying implementation on misses, and appends a response-dependent trace to
the second state component after every query.

`QueryImpl.withCachingLogging` and `OracleSpec.cachingLoggingOracle` are the
canonical specializations to `QueryLog spec`.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open OracleComp OracleSpec


-- @@ L30-30 verbatim
universe u v


-- @@ L32-32 verbatim
variable {ι : Type u} {spec : OracleSpec.{u, u} ι}


-- @@ L34-34 verbatim
namespace QueryImpl


-- @@ L36-36 verbatim
variable {m : Type u → Type v} [Monad m] [DecidableEq ι] [spec.DecidableEq]

-- @@ L37-37 verbatim
variable {ω : Type u} [EmptyCollection ω] [Append ω]


-- @@ L39-51 verbatim
/-- Cache responses in the first state component and append a response-dependent
trace to the second state component after every query.

On a cache hit, the underlying handler is not consulted; the cached answer is
returned directly and the trace still records the observed `(query, response)`
pair. On a cache miss, the underlying handler supplies the answer, which is then
installed in the cache before the trace is appended. -/
def withCachingTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (StateT (QueryCache spec × ω) m) :=
  withCachingAux
    (fun t u _ trace => trace ++ traceFn t u)
    (fun t _ trace => (fun u => (u, trace ++ traceFn t u)) <$> so t)


-- @@ L53-61 verbatim
omit [spec.DecidableEq] [EmptyCollection ω] in
@[simp, grind =]
lemma withCachingTraceAppend_apply (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (t : spec.Domain) :
    so.withCachingTraceAppend traceFn t =
      StateT.mk fun s => match s.1 t with
      | some u => pure (u, (s.1, s.2 ++ traceFn t u))
      | none => (fun p : spec.Range t × ω => (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
          ((fun u => (u, s.2 ++ traceFn t u)) <$> so t) := rfl


-- @@ L63-67 verbatim
/-- Specialization of `withCachingTraceAppend` to the canonical query log
`QueryLog spec`. -/
def withCachingLogging (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) m) :=
  so.withCachingTraceAppend (fun t u => [⟨t, u⟩])


-- @@ L69-77 verbatim
omit [spec.DecidableEq] in
@[simp, grind =]
lemma withCachingLogging_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCachingLogging t =
      StateT.mk fun s => match s.1 t with
      | some u => pure (u, (s.1, s.2 ++ [⟨t, u⟩]))
      | none => (fun p : spec.Range t × QueryLog spec =>
          (p.1, (s.1.cacheQuery t p.1, p.2))) <$>
          ((fun u => (u, s.2 ++ [⟨t, u⟩])) <$> so t) := rfl


-- @@ L79-82 verbatim
/-! ### Forward-direction query bounds for `withCachingTraceAppend`

The trace overlay does not change the underlying query count, so the `withCaching` bounds
transfer through `withCachingAux_run_proj_eq` via `isQueryBound_iff_of_map_eq`. -/


-- @@ L84-84 verbatim
variable {α : Type u} {ι' : Type u} {spec' : OracleSpec ι'}


-- @@ L86-95 verbatim
omit [Monad m] [spec.DecidableEq] in
private lemma _root_.QueryImpl.withCachingTraceAppend_run_proj_eq
    {ι₂ : Type u} {spec₂ : OracleSpec ι₂} [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec₂))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {α : Type u} (oa : OracleComp spec α) (s : QueryCache spec × ω) :
    Prod.map id Prod.fst <$> (simulateQ (so.withCachingTraceAppend traceFn) oa).run s =
      (simulateQ so.withCaching oa).run s.1 :=
  QueryImpl.withCachingAux_run_proj_eq so _ _
    (fun _ _ _ => by simp [Functor.map_map]) oa s.1 s.2


-- @@ L97-110 verbatim
omit [Monad m] [spec.DecidableEq] in
theorem isTotalQueryBound_run_simulateQ_withCachingTraceAppend
    [IsUniformSpec spec] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {oa : OracleComp spec α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n)
    (hstep : ∀ t, OracleComp.IsTotalQueryBound (so t) 1)
    (s : QueryCache spec × ω) :
    OracleComp.IsTotalQueryBound
      ((simulateQ (so.withCachingTraceAppend traceFn) oa).run s) n :=
  (OracleComp.isQueryBound_iff_of_map_eq
      (QueryImpl.withCachingTraceAppend_run_proj_eq so traceFn oa s) _ _).mpr
    (OracleComp.IsTotalQueryBound.simulateQ_run_withCaching so h hstep s.1)


-- @@ L112-127 verbatim
omit [Monad m] [spec.DecidableEq] in
theorem isQueryBoundP_run_simulateQ_withCachingTraceAppend
    [IsUniformSpec spec'] [LawfulAppend ω]
    (so : QueryImpl spec (OracleComp spec'))
    (traceFn : (t : spec.Domain) → spec.Range t → ω)
    {oa : OracleComp spec α}
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → OracleComp.IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → OracleComp.IsQueryBoundP (so t) q 0)
    (s : QueryCache spec × ω) :
    OracleComp.IsQueryBoundP
      ((simulateQ (so.withCachingTraceAppend traceFn) oa).run s) q n :=
  (OracleComp.isQueryBoundP_iff_of_map_eq
      (QueryImpl.withCachingTraceAppend_run_proj_eq so traceFn oa s)).mpr
    (OracleComp.IsQueryBoundP.simulateQ_run_withCaching so h hstep_p hstep_np s.1)


-- @@ L129-129 verbatim
end QueryImpl


-- @@ L131-134 verbatim
/-- Canonical combined caching + logging oracle over `OracleComp spec`. -/
def OracleSpec.cachingLoggingOracle [DecidableEq ι] [spec.DecidableEq] :
    QueryImpl spec (StateT (QueryCache spec × QueryLog spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCachingLogging


-- @@ L136-136 verbatim
namespace cachingLoggingOracle


-- @@ L138-138 verbatim
variable [DecidableEq ι] [spec.DecidableEq]


-- @@ L140-153 verbatim
@[simp]
lemma apply_eq (t : spec.Domain) :
    cachingLoggingOracle t = (do
      let (cache, trace) ← get
      match cache t with
      | some u =>
          modifyGet fun _ => (u, (cache, trace ++ [⟨t, u⟩]))
      | none =>
          let u ← (HasQuery.query t : OracleComp spec _)
          modifyGet fun _ => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) := by
  ext s
  rw [cachingLoggingOracle, QueryImpl.withCachingLogging, QueryImpl.withCachingTraceAppend,
    QueryImpl.withCachingAux_apply]
  cases hcache : s.1 t <;> simp [hcache]


-- @@ L155-161 verbatim
/-- Cache hit: return the stored response and append it to the query log. -/
lemma run_some {t : spec.Domain} {cache : QueryCache spec} {trace : QueryLog spec}
    {u : spec.Range t} (h : cache t = some u) :
    (cachingLoggingOracle t).run (cache, trace) =
      pure (u, (cache, trace ++ [⟨t, u⟩])) := by
  rw [apply_eq]
  simp [h]


-- @@ L163-170 verbatim
/-- Cache miss: issue the underlying query, cache its response, and append it to the query log. -/
lemma run_none {t : spec.Domain} {cache : QueryCache spec} {trace : QueryLog spec}
    (h : cache t = none) :
    (cachingLoggingOracle t).run (cache, trace) =
      (fun u => (u, (cache.cacheQuery t u, trace ++ [⟨t, u⟩]))) <$>
        (query t : OracleComp spec _) := by
  rw [apply_eq]
  simp [h, monad_norm]


-- @@ L172-198 verbatim
/-- Running the combined caching-and-logging handler is equivalent to first adding the
writer-style query log and then interpreting the resulting computation through the caching
handler. The explicit state rearrangement also appends the newly produced log to an arbitrary
initial trace, so the statement composes across phases. -/
theorem run_simulateQ_eq_map_run_simulateQ_withQueryLog {α : Type u}
    (oa : OracleComp spec α) (cache₀ : QueryCache spec) (trace₀ : QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run (cache₀, trace₀) =
      (fun z : (α × QueryLog spec) × QueryCache spec =>
        (z.1.1, (z.2, trace₀ ++ z.1.2))) <$>
        (simulateQ cachingOracle oa.withQueryLog).run cache₀ := by
  change (simulateQ cachingLoggingOracle oa).run (cache₀, trace₀) =
    (fun z : (α × QueryLog spec) × QueryCache spec =>
      (z.1.1, (z.2, trace₀ ++ z.1.2))) <$>
      (simulateQ cachingOracle (simulateQ loggingOracle oa).run).run cache₀
  induction oa using OracleComp.inductionOn generalizing cache₀ trace₀ with
  | pure x => simp
  | query_bind t mx ih =>
      rw [OracleComp.run_simulateQ_query_bind]
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind]
      rw [OracleComp.run_simulateQ_query_bind]
      cases hcache : cache₀ t with
      | none =>
          rw [run_none hcache, cachingOracle.run_none hcache]
          simp [ih, List.append_assoc, monad_norm]
      | some u =>
          rw [run_some hcache, cachingOracle.run_some hcache]
          simp [ih, List.append_assoc, monad_norm]


-- @@ L200-206 verbatim
/-- Projecting away the log component recovers the ordinary caching semantics. -/
theorem fst_map_run_simulateQ {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    Prod.map id Prod.fst <$> (simulateQ cachingLoggingOracle oa).run s =
      (simulateQ cachingOracle oa).run s.1 := by
  exact QueryImpl.withCachingTraceAppend_run_proj_eq
    (QueryImpl.ofLift spec (OracleComp spec)) (fun t u => [⟨t, u⟩]) oa s


-- @@ L208-217 verbatim
/-- Output-only projection corollary of `fst_map_run_simulateQ`. -/
theorem run'_simulateQ_eq {α : Type u}
    (oa : OracleComp spec α) (s : QueryCache spec × QueryLog spec) :
    (simulateQ cachingLoggingOracle oa).run' s =
      (simulateQ cachingOracle oa).run' s.1 := by
  have hmap := congrArg (fun p => Prod.fst <$> p) (fst_map_run_simulateQ oa s)
  rw [StateT.run', StateT.run']
  change (fun a => id a.1) <$> (simulateQ cachingLoggingOracle oa).run s =
    Prod.fst <$> (simulateQ cachingOracle oa).run s.1
  simpa only [Functor.map_map, Function.comp_def, Prod.map] using hmap


-- @@ L219-222 verbatim
/-! ### Forward-direction query bounds

The log overlay does not change the underlying query count, so the `cachingOracle` bounds
transfer through `fst_map_run_simulateQ` via `isQueryBound_iff_of_map_eq`. -/


-- @@ L224-231 verbatim
theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) n :=
  (OracleComp.isQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s) _ _).mpr
    (cachingOracle.isTotalQueryBound_run_simulateQ h s.1)


-- @@ L233-240 verbatim
theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.cachingLoggingOracle oa).run s) p n :=
  (OracleComp.isQueryBoundP_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isQueryBoundP_run_simulateQ h s.1)


-- @@ L242-249 verbatim
theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [spec₀.DecidableEq] [IsUniformSpec spec₀]
    {α : Type} {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb)
    (s : QueryCache spec₀ × QueryLog spec₀) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.cachingLoggingOracle oa).run s) qb :=
  (OracleComp.isPerIndexQueryBound_iff_of_map_eq (fst_map_run_simulateQ oa s)).mpr
    (cachingOracle.isPerIndexQueryBound_run_simulateQ h s.1)


-- @@ L251-251 verbatim
end cachingLoggingOracle
