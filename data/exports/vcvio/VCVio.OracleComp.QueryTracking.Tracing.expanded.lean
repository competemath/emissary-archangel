/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.SimSemantics.WriterT.Basic
public import PolyFun.Control.Trace
public import ToMathlib.Control.WriterT


-- @@ L15-60 verbatim
/-!
# Generic Trace Instrumentation for Query Implementations

Two primitive ways to attach a writer-valued trace to a `QueryImpl`. Each
comes in two flavours, mirroring Mathlib's two `Monad (WriterT ω M)` instances:

* `[Monoid ω]` flavour (`withTrace` / `withTraceBefore`): the trace lives in
  an arbitrary monoid `ω` and accumulates via `1` and `*`. This is what
  `QueryImpl.withCost` (`CountingOracle.lean`) uses, with `ω = QueryCount ι`
  (pointwise additive monoid).

* `[EmptyCollection ω] [Append ω]` flavour (`withTraceAppend` /
  `withTraceAppendBefore`): the trace accumulates via `∅` and `++`, matching
  the Append-based `Monad (WriterT ω m)` instance. This is what
  `QueryImpl.withLogging` (`LoggingOracle.lean`) uses, with
  `ω = QueryLog spec` (a list of query/response pairs).

The two flavours are mathematically the same (a free monoid view vs. an
append-list view), but they correspond to *different* `Monad (WriterT ω m)`
instances and Lean's resolver picks whichever one is unambiguously available.
We expose both so neither of `QueryCount`/`QueryLog` has to switch its
underlying writer interpretation.

For each flavour, "Before" emits `traceFn t` *before* running the handler
(so a handler failure still records the trace), while the bare version emits
`traceFn t u` *after* the handler returns response `u` (so a failure skips
the trace).

Concretely:

* `withCost = withTraceBefore` (the cost ignores the response).
* `withLogging so = withTraceAppend so (fun t u => [⟨t, u⟩])` (the log records
  the response, hence "after" semantics).

The generic lemmas (output marginal, failure probability, `NeverFail`
equivalence, `evalSPMF` / `support` / `probOutput` bridges) flow downstream
automatically.

## Connection to `Control.Trace`

The trace function `traceFn : (t : spec.Domain) → spec.Range t → ω` is a curried
form of `Idx spec.toPFunctor → ω`, which is precisely
`Control.Trace ω (Idx spec.toPFunctor)`. The `Tracing` API is therefore the
oracle-level counterpart of the abstract `Control.Trace` / `PFunctor.Trace`
infrastructure in `ToMathlib`.
-/


-- @@ L62-62 verbatim
@[expose] public section


-- @@ L64-64 verbatim
open OracleSpec OracleComp


-- @@ L66-66 verbatim
universe u v w


-- @@ L68-68 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}


-- @@ L70-70 verbatim
namespace QueryImpl


-- @@ L72-72 verbatim
variable {m : Type u → Type v} [Monad m]


-- @@ L74-74 verbatim
/-! ### `withTraceBefore`: response-independent trace, recorded before handler -/


-- @@ L76-76 verbatim
section withTraceBefore


-- @@ L78-78 verbatim
variable {ω : Type u} [Monoid ω]


-- @@ L80-85 verbatim
/-- Wrap an oracle implementation so that each query records `traceFn t` in
the writer `ω` *before* running the handler. The trace value depends only on
the query, so a failure inside the handler still leaves the trace recorded. -/
abbrev withTraceBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceBefore (P := spec.toPFunctor) so traceFn


-- @@ L87-90 verbatim
@[grind =]
lemma withTraceBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (t : spec.Domain) :
    so.withTraceBefore traceFn t = (do tell (traceFn t); so t) := by
  exact PFunctor.Handler.withTraceBefore_apply (P := spec.toPFunctor) so traceFn t


-- @@ L92-102 verbatim
lemma fst_map_run_withTraceBefore [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceBefore traceFn =
      so.preInsert (fun t => tell (traceFn t)) :=
    PFunctor.Handler.withTraceBefore_eq_preInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx


-- @@ L104-111 expanded
/-- A "before"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTraceBefore` does not change the
probability of failure. -/
lemma probFailure_run_simulateQ_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (mx : OracleComp spec α) :
    probFailure (simulateQ (so.withTraceBefore traceFn) mx).run = probFailure (simulateQ so mx) :=
  by rw [← fst_map_run_withTraceBefore so traceFn mx, probFailure_map]


-- @@ L113-117 verbatim
lemma neverFail_run_simulateQ_withTraceBefore_iff [LawfulMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceBefore traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceBefore]


-- @@ L119-126 verbatim
/-- When every query traces to the monoid identity `1`, `withTraceBefore` is a
no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTraceBefore_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTraceBefore (fun _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]


-- @@ L128-128 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceBefore` -/


-- @@ L130-134 expanded
lemma evalSPMF_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      evalSPMF (simulateQ so mx) :=
  congrArg evalSPMF (fst_map_run_withTraceBefore so traceFn mx)


-- @@ L136-141 expanded
lemma probOutput_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (mx : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) x =
      probOutput (simulateQ so mx) x :=
  by rw [fst_map_run_withTraceBefore]


-- @@ L143-147 verbatim
lemma support_fst_run_withTraceBefore [LawfulMonad m] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceBefore]


-- @@ L149-149 verbatim
end withTraceBefore


-- @@ L151-151 verbatim
/-! ### `withTrace`: response-dependent trace, recorded after handler -/


-- @@ L153-153 verbatim
section withTrace


-- @@ L155-155 verbatim
variable {ω : Type u} [Monoid ω]


-- @@ L157-163 verbatim
/-- Wrap an oracle implementation so that each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`.
A handler failure skips the trace (the response never materialised). -/
abbrev withTrace (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTrace (P := spec.toPFunctor) so traceFn


-- @@ L165-169 verbatim
@[grind =]
lemma withTrace_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTrace traceFn t = (do let u ← so t; tell (traceFn t u); return u) := by
  exact PFunctor.Handler.withTrace_apply (P := spec.toPFunctor) so traceFn t


-- @@ L171-182 verbatim
lemma fst_map_run_withTrace [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run = simulateQ so mx := by
  have h : so.withTrace traceFn =
      so.postInsert (fun t u => tell (traceFn t u)) :=
    PFunctor.Handler.withTrace_eq_postInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure WriterT.fst_map_run_bind
    (fun t => by simp) mx


-- @@ L184-194 expanded
/-- An "after"-style trace preserves failure probability for any base monad with
`MonadLiftT m SPMF`: instrumenting with `withTrace` does not change the probability
of failure. When `m = OracleComp spec`, both sides are `0` (trivially true);
when `m` can genuinely fail (e.g. `OptionT (OracleComp spec)`), this is a
non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withTrace [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (mx : OracleComp spec α) :
    probFailure (simulateQ (so.withTrace traceFn) mx).run = probFailure (simulateQ so mx) := by
  rw [← fst_map_run_withTrace so traceFn mx, probFailure_map]


-- @@ L196-201 verbatim
lemma neverFail_run_simulateQ_withTrace_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTrace traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTrace]


-- @@ L203-210 verbatim
/-- When every query/response pair traces to the monoid identity `1`,
`withTrace` is a no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTrace_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTrace (fun _ _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn <;> simp [*]


-- @@ L212-212 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTrace` -/


-- @@ L214-219 expanded
lemma evalSPMF_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      evalSPMF (simulateQ so mx) :=
  congrArg evalSPMF (fst_map_run_withTrace so traceFn mx)


-- @@ L221-226 expanded
lemma probOutput_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) x =
      probOutput (simulateQ so mx) x :=
  by rw [fst_map_run_withTrace]


-- @@ L228-233 verbatim
lemma support_fst_run_withTrace [LawfulMonad m] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTrace]


-- @@ L235-235 verbatim
end withTrace


-- @@ L237-238 verbatim
/-! ### `withTraceAppendBefore`: response-independent trace, recorded before
handler, accumulating via `∅` / `++` -/


-- @@ L240-240 verbatim
section withTraceAppendBefore


-- @@ L242-242 verbatim
variable {ω : Type u} [EmptyCollection ω] [Append ω]


-- @@ L244-251 verbatim
/-- Append-flavoured analogue of `withTraceBefore`: each query records
`traceFn t` in the writer `ω` *before* running the handler, and `WriterT`
uses the `[EmptyCollection ω] [Append ω]` `Monad` instance (`tell` is a single
push, `bind` concatenates with `++`). The trace value depends only on the
query, so a failure inside the handler still leaves the trace recorded. -/
abbrev withTraceAppendBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppendBefore (P := spec.toPFunctor) so traceFn


-- @@ L253-257 verbatim
@[grind =]
lemma withTraceAppendBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withTraceAppendBefore traceFn t = (do tell (traceFn t); so t) := by
  exact PFunctor.Handler.withTraceAppendBefore_apply (P := spec.toPFunctor) so traceFn t


-- @@ L259-269 verbatim
lemma fst_map_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceAppendBefore traceFn =
      so.preInsert (fun t => tell (traceFn t)) :=
    PFunctor.Handler.withTraceAppendBefore_eq_preInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_preInsert so (fun t => tell (traceFn t))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp [seqRight_eq_bind]) mx


-- @@ L271-276 expanded
lemma probFailure_run_simulateQ_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m)
    (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    probFailure (simulateQ (so.withTraceAppendBefore traceFn) mx).run =
      probFailure (simulateQ so mx) :=
  by rw [← fst_map_run_withTraceAppendBefore so traceFn mx, probFailure_map]


-- @@ L278-283 verbatim
lemma neverFail_run_simulateQ_withTraceAppendBefore_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppendBefore traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppendBefore]


-- @@ L285-285 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceAppendBefore` -/


-- @@ L287-292 expanded
lemma evalSPMF_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (mx : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      evalSPMF (simulateQ so mx) :=
  congrArg evalSPMF (fst_map_run_withTraceAppendBefore so traceFn mx)


-- @@ L294-299 expanded
lemma probOutput_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (mx : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) x =
      probOutput (simulateQ so mx) x :=
  by rw [fst_map_run_withTraceAppendBefore]


-- @@ L301-305 verbatim
lemma support_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppendBefore]


-- @@ L307-307 verbatim
end withTraceAppendBefore


-- @@ L309-310 verbatim
/-! ### `withTraceAppend`: response-dependent trace, recorded after handler,
accumulating via `∅` / `++` -/


-- @@ L312-312 verbatim
section withTraceAppend


-- @@ L314-314 verbatim
variable {ω : Type u} [EmptyCollection ω] [Append ω]


-- @@ L316-323 verbatim
/-- Append-flavoured analogue of `withTrace`: each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`,
using the `[EmptyCollection ω] [Append ω]` `Monad (WriterT ω m)` instance.
A handler failure skips the trace (the response never materialised). -/
abbrev withTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  PFunctor.Handler.withTraceAppend (P := spec.toPFunctor) so traceFn


-- @@ L325-329 verbatim
@[grind =]
lemma withTraceAppend_apply (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (t : spec.Domain) :
    so.withTraceAppend traceFn t = (do let u ← so t; tell (traceFn t u); return u) := by
  exact PFunctor.Handler.withTraceAppend_apply (P := spec.toPFunctor) so traceFn t


-- @@ L331-342 verbatim
lemma fst_map_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run = simulateQ so mx := by
  have h : so.withTraceAppend traceFn =
      so.postInsert (fun t u => tell (traceFn t u)) :=
    PFunctor.Handler.withTraceAppend_eq_postInsert (P := spec.toPFunctor) so traceFn
  rw [h]
  exact proj_simulateQ_postInsert so (fun t u => tell (traceFn t u))
    (proj := fun {γ} (x : WriterT ω m γ) => Prod.fst <$> x.run)
    WriterT.fst_map_run_pure' WriterT.fst_map_run_bind'
    (fun t => by simp) mx


-- @@ L344-349 expanded
lemma probFailure_run_simulateQ_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (mx : OracleComp spec α) :
    probFailure (simulateQ (so.withTraceAppend traceFn) mx).run = probFailure (simulateQ so mx) :=
  by rw [← fst_map_run_withTraceAppend so traceFn mx, probFailure_map]


-- @@ L351-357 verbatim
lemma neverFail_run_simulateQ_withTraceAppend_iff [LawfulMonad m]
    [LawfulAppend ω] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppend traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [neverFail_iff, probFailure_run_simulateQ_withTraceAppend]


-- @@ L359-359 verbatim
/-! #### `evalSPMF` / `probOutput` / `support` bridges for `withTraceAppend` -/


-- @@ L361-367 expanded
lemma evalSPMF_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (mx : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      evalSPMF (simulateQ so mx) :=
  congrArg evalSPMF (fst_map_run_withTraceAppend so traceFn mx)


-- @@ L369-375 expanded
lemma probOutput_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (mx : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) x =
      probOutput (simulateQ so mx) x :=
  by rw [fst_map_run_withTraceAppend]


-- @@ L377-382 verbatim
lemma support_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppend]


-- @@ L384-384 verbatim
end withTraceAppend


-- @@ L386-386 verbatim
end QueryImpl
