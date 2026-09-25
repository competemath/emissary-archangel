/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.QueryTracking.Tracing


-- @@ L12-26 verbatim
/-!
# Counting Queries Made by a Computation

This file defines a simulation oracle `countingOracle` for counting the number of queries made
while running the computation. The count is represented by a function from oracle indices to
counts, allowing each oracle to be tracked individually.

Tracking individually is not necessary, but gives tighter security bounds in some cases.
It also allows for generating things like seed values for a computation more tightly.

`QueryImpl.withCost` and `QueryImpl.withCounting` are response-independent traces, defined as
specialisations of `QueryImpl.withTraceBefore` (see `Tracing.lean`): the cost is accumulated
*before* the underlying handler runs, so failed queries still incur their cost. The counting
case picks `QueryCount.single` as the trace function.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open OracleSpec OracleComp


-- @@ L32-32 verbatim
universe u v w


-- @@ L34-34 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L36-36 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}


-- @@ L38-38 verbatim
namespace QueryImpl


-- @@ L40-40 verbatim
variable {m : Type u → Type v} [Monad m]


-- @@ L42-42 verbatim
section withCost


-- @@ L44-44 verbatim
variable {ω : Type u} [Monoid ω]


-- @@ L46-69 verbatim
/-- Wrap an oracle implementation to accumulate cost in a `WriterT ω` layer.
The cost function `costFn` assigns a cost value to each oracle query.
Cost is accumulated *before* the implementation runs, so failed queries are still costed.

This is the response-independent specialisation of `QueryImpl.withTraceBefore`:
the trace value depends only on the query, not on the response.

**Side-channel trace instrumentation.**
`withCost` doubles as automatic side-channel instrumentation: given any
`OracleComp spec α` and a cost function `costFn : spec.Domain → ω`,
`(simulateQ (base.withCost costFn) oa).run` produces `m (α × ω)` without
modifying the computation's source code. The cost function encodes the
observation model:

* `fun _ => ()` (constant-time): every query looks identical to the observer.
* `fun t => queryLabel t` (typed): the observer sees which oracle was queried
  but not the arguments or results.

This is the preferred approach when the observation model is "every oracle
query is visible." For observations at non-query points (e.g. pure-computation
timing), use the explicit `observe` / `runObs` API from `ObservationOracle`. -/
def withCost (so : QueryImpl spec m) (costFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  so.withTraceBefore costFn


-- @@ L71-72 verbatim
lemma withCost_eq_withTraceBefore (so : QueryImpl spec m) (costFn : spec.Domain → ω) :
    so.withCost costFn = so.withTraceBefore costFn := rfl


-- @@ L74-78 verbatim
@[simp, grind =]
lemma withCost_apply (so : QueryImpl spec m) (costFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withCost costFn t = (do tell (costFn t); so t) := by
  exact withTraceBefore_apply so costFn t


-- @@ L80-83 verbatim
lemma fst_map_run_withCost [LawfulMonad m]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withCost costFn) mx).run = simulateQ so mx :=
  fst_map_run_withTraceBefore so costFn mx


-- @@ L85-91 expanded
/-- Cost-tracking preserves failure probability: for any base monad `m` with `MonadLiftT m SPMF`,
wrapping an oracle implementation with `withCost` does not change the probability of failure. -/
lemma probFailure_run_simulateQ_withCost [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF] (so : QueryImpl spec m) (costFn : spec.Domain → ω)
    (mx : OracleComp spec α) :
    probFailure (simulateQ (so.withCost costFn) mx).run = probFailure (simulateQ so mx) :=
  probFailure_run_simulateQ_withTraceBefore so costFn mx


-- @@ L93-97 verbatim
lemma NeverFail_run_simulateQ_withCost_iff [LawfulMonad m] [MonadLiftT m SPMF]
    [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withCost costFn) mx).run ↔ NeverFail (simulateQ so mx) :=
  neverFail_run_simulateQ_withTraceBefore_iff so costFn mx


-- @@ L99-106 verbatim
/-- When every query costs the monoid identity `1`, the trace is always `1`,
so `withCost` is a no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withCost_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withCost (fun _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx :=
  run_simulateQ_withTraceBefore_const_one so mx


-- @@ L108-112 verbatim
/-! ### EvalDist Bridge for `withCost`

These lemmas connect the result-marginal distribution of a `withCost`-instrumented
computation to the distribution of the uninstrumented computation, enabling direct
probability-level reasoning about traced computations. -/


-- @@ L114-118 expanded
lemma evalSPMF_fst_run_withCost [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (so.withCost costFn) mx).run) = evalSPMF (simulateQ so mx) :=
  evalSPMF_fst_run_withTraceBefore so costFn mx


-- @@ L120-124 expanded
lemma probOutput_fst_run_withCost [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (so.withCost costFn) mx).run) x =
      probOutput (simulateQ so mx) x :=
  probOutput_fst_run_withTraceBefore so costFn mx x


-- @@ L126-130 verbatim
lemma support_fst_run_withCost [LawfulMonad m] [MonadLiftT m SetM]
    (so : QueryImpl spec m) (costFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withCost costFn) mx).run) =
      support (simulateQ so mx) :=
  support_fst_run_withTraceBefore so costFn mx


-- @@ L132-132 verbatim
end withCost


-- @@ L134-139 verbatim
/-- Wrap an oracle implementation to count queries in a `WriterT (QueryCount ι)` layer.
Counting happens before the implementation runs, so failed queries are still counted.
This is a special case of `withCost` where the cost function is `QueryCount.single`. -/
def withCounting [DecidableEq ι] (so : QueryImpl spec m) :
    QueryImpl spec (WriterT (QueryCount ι) m) :=
  so.withCost (QueryCount.single ·)


-- @@ L141-144 verbatim
@[simp, grind =]
lemma withCounting_apply [DecidableEq ι] (so : QueryImpl spec m) (t : spec.Domain) :
    so.withCounting t = (do tell (QueryCount.single t); so t) := by
  exact withCost_apply so (QueryCount.single ·) t


-- @@ L146-147 verbatim
lemma withCounting_eq_withCost [DecidableEq ι] (so : QueryImpl spec m) :
    so.withCounting = so.withCost (QueryCount.single ·) := rfl


-- @@ L149-152 verbatim
lemma fst_map_run_withCounting [DecidableEq ι] [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withCounting) mx).run = simulateQ so mx :=
  fst_map_run_withCost so _ mx


-- @@ L154-154 verbatim
end QueryImpl


-- @@ L156-160 verbatim
/-- Oracle with arbitrary cost tracking. The cost is accumulated in a `WriterT ω` layer
while preserving the original oracle behavior. -/
def costOracle {ω : Type u} [Monoid ω] (costFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCost costFn


-- @@ L162-166 verbatim
/-- Oracle for counting the number of queries made by a computation. The count is stored as a
function from oracle indices to counts, to give finer grained information about the count. -/
def OracleSpec.countingOracle [DecidableEq ι] :
    QueryImpl spec (WriterT (QueryCount ι) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCounting


-- @@ L168-174 verbatim
/-- Pointwise behavior of the generic cost oracle. -/
@[simp]
lemma costOracle_apply {ω : Type u} [Monoid ω] (costFn : spec.Domain → ω)
    (t : spec.Domain) :
    costOracle costFn t =
      (do tell (costFn t); liftM (liftM (spec.query t) : OracleComp spec _)) := by
  rw [costOracle, QueryImpl.withCost_apply, QueryImpl.ofLift_apply]


-- @@ L176-181 verbatim
/-- Pointwise behavior of the per-index counting oracle. -/
@[simp]
lemma OracleSpec.countingOracle_apply [DecidableEq ι] (t : spec.Domain) :
    spec.countingOracle t =
      (do tell (QueryCount.single t); liftM (liftM (spec.query t) : OracleComp spec _)) := by
  rw [OracleSpec.countingOracle, QueryImpl.withCounting_apply, QueryImpl.ofLift_apply]


-- @@ L183-184 verbatim
lemma countingOracle_eq_costOracle [DecidableEq ι] :
    spec.countingOracle = costOracle (QueryCount.single ·) := rfl


-- @@ L186-186 verbatim
namespace costOracle


-- @@ L188-188 verbatim
variable {ω : Type u} [Monoid ω]


-- @@ L190-193 verbatim
@[simp]
lemma fst_map_run_simulateQ (costFn : spec.Domain → ω) (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (costOracle costFn) oa).run = oa := by
  rw [costOracle, QueryImpl.fst_map_run_withCost, simulateQ_ofLift_eq_self]


-- @@ L195-198 expanded
lemma evalSPMF_fst_run_simulateQ [IsUniformSpec spec] (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) :
    evalSPMF (Prod.fst <$> (simulateQ (costOracle costFn) oa).run) = evalSPMF oa := by
  rw [fst_map_run_simulateQ]


-- @@ L200-203 expanded
lemma probOutput_fst_run_simulateQ [IsUniformSpec spec] (costFn : spec.Domain → ω)
    (oa : OracleComp spec α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (costOracle costFn) oa).run) x = probOutput oa x := by
  rw [fst_map_run_simulateQ]


-- @@ L205-208 verbatim
lemma support_run_simulateQ [IsUniformSpec spec]
    (costFn : spec.Domain → ω) (oa : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (costOracle costFn) oa).run) = support oa := by
  rw [fst_map_run_simulateQ]


-- @@ L210-210 verbatim
end costOracle


-- @@ L212-212 verbatim
namespace countingOracle


-- @@ L214-214 verbatim
variable [DecidableEq ι]


-- @@ L216-219 verbatim
@[simp]
lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ countingOracle oa).run = oa := by
  rw [countingOracle, QueryImpl.fst_map_run_withCounting, simulateQ_ofLift_eq_self]


-- @@ L221-224 verbatim
@[simp]
lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ countingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]


-- @@ L226-231 expanded
/-- Specialization of `QueryImpl.probFailure_run_simulateQ_withCost` to `countingOracle`. -/
lemma probFailure_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) :
    probFailure (simulateQ (spec₀.countingOracle) oa).run = probFailure oa := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.probFailure_run_simulateQ_withCost, simulateQ_ofLift_eq_self]


-- @@ L233-240 verbatim
/-- Specialization of `QueryImpl.NeverFail_run_simulateQ_withCost_iff` to `countingOracle`. -/
@[simp]
lemma NeverFail_run_simulateQ_iff {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀}
    [DecidableEq ι₀] [IsUniformSpec spec₀] {α : Type}
    (oa : OracleComp spec₀ α) :
    NeverFail (simulateQ (spec₀.countingOracle) oa).run ↔ NeverFail oa := by
  simp only [countingOracle, QueryImpl.withCounting_eq_withCost,
    QueryImpl.NeverFail_run_simulateQ_withCost_iff, simulateQ_ofLift_eq_self]


-- @@ L242-248 expanded
@[simp]
lemma probEvent_fst_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) (p : α → Prop) :
    (probEvent (simulateQ (spec₀.countingOracle) oa).run fun z => p z.1) = probEvent oa p := by
  rw [show (fun z : α × QueryCount ι₀ => p z.1) = p ∘ Prod.fst from rfl, ← probEvent_map,
    fst_map_run_simulateQ]


-- @@ L250-255 expanded
lemma probOutput_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) (x : α) :
    probOutput (Prod.fst <$> (simulateQ (spec₀.countingOracle) oa).run) x = probOutput oa x := by
  rw [fst_map_run_simulateQ]


-- @@ L257-260 expanded
lemma evalSPMF_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) :
    evalSPMF (Prod.fst <$> (simulateQ (spec₀.countingOracle) oa).run) = evalSPMF oa := by
  rw [fst_map_run_simulateQ]


-- @@ L262-265 verbatim
lemma support_fst_map_run_simulateQ {ι₀ : Type} {spec₀ : OracleSpec.{0, 0} ι₀} [DecidableEq ι₀]
    [IsUniformSpec spec₀] {α : Type} (oa : OracleComp spec₀ α) :
    support (Prod.fst <$> (simulateQ (spec₀.countingOracle) oa).run) = support oa := by
  rw [fst_map_run_simulateQ]


-- @@ L267-267 verbatim
section support


-- @@ L269-273 verbatim
/-- Compatibility helper matching old state-style counting semantics:
simulate with zero initial count, then offset by `qc`. -/
def simulate (oa : OracleComp spec α) (qc : QueryCount ι) :
    OracleComp spec (α × QueryCount ι) :=
  Prod.map id (qc + ·) <$> (simulateQ countingOracle oa).run


-- @@ L275-280 verbatim
lemma simulate_eq_map_simulate_zero (oa : OracleComp spec α) (qc : QueryCount ι) :
    simulate oa qc = Prod.map id (qc + ·) <$> simulate oa 0 := by
  simp only [simulate, Functor.map_map]
  congr 1
  funext ⟨x, q⟩
  simp


-- @@ L282-287 verbatim
/-- We can always reduce simulation with counting to start with `0`,
and add the initial count back at the end. -/
lemma support_simulate (oa : OracleComp spec α) (qc : QueryCount ι) :
    support (simulate oa qc) = Prod.map id (qc + ·) '' support (simulate oa 0) := by
  rw [simulate_eq_map_simulate_zero]
  simp [support_map]


-- @@ L289-295 verbatim
/-- Reduce membership in support of simulation with counting to simulation starting from `0`. -/
lemma mem_support_simulate_iff (oa : OracleComp spec α) (qc : QueryCount ι)
    (z : α × QueryCount ι) :
    z ∈ support (simulate oa qc) ↔
      ∃ qc', (z.1, qc') ∈ support (simulate oa 0) ∧ qc + qc' = z.2 := by
  rw [support_simulate]
  aesop


-- @@ L297-309 verbatim
lemma mem_support_simulate_iff_of_le (oa : OracleComp spec α) (qc : QueryCount ι)
    (z : α × QueryCount ι) (hz : qc ≤ z.2) :
    z ∈ support (simulate oa qc) ↔ (z.1, z.2 - qc) ∈ support (simulate oa 0) := by
  rw [mem_support_simulate_iff oa qc z]
  refine ⟨?_, ?_⟩
  · rintro ⟨qc', hmem, hq⟩
    convert hmem using 2
    funext i
    have hqi : qc i + qc' i = z.2 i := congrFun hq i
    simpa [Pi.sub_apply, hqi] using (Nat.add_sub_cancel_left (qc i) (qc' i))
  · refine fun hmem => ⟨z.2 - qc, hmem, ?_⟩
    funext i
    simp [Pi.add_apply, Pi.sub_apply, Nat.add_sub_of_le (hz i)]


-- @@ L311-314 verbatim
lemma le_of_mem_support_simulate {oa : OracleComp spec α} {qc : QueryCount ι}
    {z : α × QueryCount ι} (h : z ∈ support (simulate oa qc)) : qc ≤ z.2 := by
  obtain ⟨qc', _, hq⟩ := (mem_support_simulate_iff oa qc z).1 h
  exact fun i => le_of_le_of_eq (Nat.le_add_right _ _) (congrFun hq i)


-- @@ L316-316 verbatim
section snd_map


-- @@ L318-327 verbatim
lemma mem_support_snd_map_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) :
    qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι)) ↔
      ∃ qc'', ∃ x, (x, qc'') ∈ support (simulate oa 0) ∧ qc + qc'' = qc' := by
  simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨qc'', x, hmem, hq⟩ => ?_⟩
  · obtain ⟨qc'', hmem, hq⟩ := (mem_support_simulate_iff oa qc (x, qc')).1 hx
    exact ⟨qc'', x, hmem, hq⟩
  · exact ⟨x, (mem_support_simulate_iff oa qc (x, qc')).2 ⟨qc'', hmem, hq⟩⟩


-- @@ L329-342 verbatim
lemma mem_support_snd_map_simulate_iff_of_le (oa : OracleComp spec α)
    {qc qc' : QueryCount ι} (hqc : qc ≤ qc') :
    qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι)) ↔
      qc' - qc ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa 0) :
        OracleComp spec (QueryCount ι)) := by
  rw [mem_support_snd_map_simulate_iff]
  simp only [support_map, Set.mem_image, Prod.exists, exists_eq_right]
  refine ⟨fun ⟨qc'', x, hmem, hq⟩ => ⟨x, ?_⟩, fun ⟨x, hx⟩ => ⟨qc' - qc, x, hx, ?_⟩⟩
  · convert hmem using 2
    funext i
    simp [Pi.sub_apply, ← congrFun hq i]
  · funext i
    simp [Pi.add_apply, Pi.sub_apply, Nat.add_sub_of_le (hqc i)]


-- @@ L344-349 verbatim
lemma le_of_mem_support_snd_map_simulate {oa : OracleComp spec α}
    {qc qc' : QueryCount ι}
    (h : qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι))) : qc ≤ qc' := by
  obtain ⟨qc'', _, _, hq⟩ := (mem_support_snd_map_simulate_iff oa qc qc').1 h
  exact fun i => le_of_le_of_eq (Nat.le_add_right _ _) (congrFun hq i)


-- @@ L351-358 verbatim
lemma sub_mem_support_snd_map_simulate {oa : OracleComp spec α}
    {qc qc' : QueryCount ι}
    (h : qc' ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa qc) :
      OracleComp spec (QueryCount ι))) :
    qc' - qc ∈ support (((fun z : α × QueryCount ι => z.2) <$> simulate oa 0) :
      OracleComp spec (QueryCount ι)) :=
  (mem_support_snd_map_simulate_iff_of_le (oa := oa)
    (hqc := le_of_mem_support_snd_map_simulate h)).1 h


-- @@ L360-360 verbatim
end snd_map


-- @@ L362-371 verbatim
lemma add_mem_support_simulate {oa : OracleComp spec α} {qc : QueryCount ι}
    {z : α × QueryCount ι} (hz : z ∈ support (simulate oa qc)) (qc' : QueryCount ι) :
    (z.1, z.2 + qc') ∈ support (simulate oa (qc + qc')) := by
  rcases (mem_support_simulate_iff oa qc z).1 hz with ⟨qc1, hmem, hq⟩
  refine (mem_support_simulate_iff oa (qc + qc') (z.1, z.2 + qc')).2 ?_
  refine ⟨qc1, hmem, ?_⟩
  funext i
  have hi : qc i + qc1 i = z.2 i := by simpa [Pi.add_apply] using congrFun hq i
  simp only [Pi.add_apply]
  omega


-- @@ L373-378 verbatim
@[simp]
lemma add_right_mem_support_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) (x : α) :
    (x, qc + qc') ∈ support (simulate oa qc) ↔ (x, qc') ∈ support (simulate oa 0) := by
  rw [mem_support_simulate_iff]
  aesop


-- @@ L380-385 verbatim
@[simp]
lemma add_left_mem_support_simulate_iff (oa : OracleComp spec α)
    (qc qc' : QueryCount ι) (x : α) :
    (x, qc' + qc) ∈ support (simulate oa qc) ↔ (x, qc') ∈ support (simulate oa 0) := by
  rw [add_comm qc' qc]
  exact add_right_mem_support_simulate_iff oa qc qc' x


-- @@ L387-390 verbatim
lemma mem_support_simulate_pure_iff (x : α) (qc : QueryCount ι)
    (z : α × QueryCount ι) :
    z ∈ support (simulate (pure x : OracleComp spec α) qc) ↔ z = (x, qc) := by
  simp [simulate]


-- @@ L392-404 expanded
lemma apply_ne_zero_of_mem_support_simulate_queryBind {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {qc : QueryCount ι} {z : α × QueryCount ι}
    (hz : z ∈ support (simulate ((OracleSpec.query t : OracleComp spec _) >>= oa) qc)) :
    z.2 t ≠ 0 :=
  by
  obtain ⟨q0, hq0mem, hqsum⟩ :=
    (mem_support_simulate_iff (oa := ((OracleSpec.query t : OracleComp spec _) >>= oa)) qc z).1 hz
  obtain ⟨u, b, _hb, hq0⟩ :=
    (by simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hq0mem)
  have hqt : qc t + q0 t = z.2 t := congrFun hqsum t
  have hq0t : q0 t = QueryCount.single t t + b t := by
    simpa [Pi.add_apply] using (congrFun hq0 t).symm
  simp only [QueryCount.single, Pi.single_eq_same] at hq0t
  omega


-- @@ L406-428 expanded
lemma exists_mem_support_of_mem_support_simulate_queryBind {t : spec.Domain}
    {oa : spec.Range t → OracleComp spec α} {qc : QueryCount ι} {z : α × QueryCount ι}
    (hz : z ∈ support (simulate ((OracleSpec.query t : OracleComp spec _) >>= oa) qc)) :
    ∃ u, (z.1, Function.update z.2 t (z.2 t - 1)) ∈ support (simulate (oa u) qc) :=
  by
  obtain ⟨q0, hq0mem, hqsum⟩ :=
    (mem_support_simulate_iff (oa := ((OracleSpec.query t : OracleComp spec _) >>= oa)) qc z).1 hz
  obtain ⟨u, b, hb, hq0⟩ :=
    (by simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hq0mem)
  have hb0 : (z.1, b) ∈ support (simulate (oa u) 0) := by simpa [simulate, countingOracle] using hb
  refine
    ⟨u,
      (mem_support_simulate_iff (oa := oa u) qc (z := (z.1, Function.update z.2 t (z.2 t - 1)))).2
        ⟨b, hb0, ?_⟩⟩
  funext j
  have hqj : qc j + q0 j = z.2 j := congrFun hqsum j
  have hq0j : q0 j = QueryCount.single t j + b j := by
    simpa [Pi.add_apply] using (congrFun hq0 j).symm
  rcases eq_or_ne j t with rfl | hj
  · simp only [Pi.add_apply, QueryCount.single, Pi.single_eq_same, Function.update_self] at hq0j ⊢
    omega
  · simp only [Pi.add_apply, QueryCount.single, Pi.single_eq_of_ne hj,
      Function.update_of_ne hj] at hq0j ⊢
    omega


-- @@ L430-468 expanded
lemma mem_support_simulate_queryBind_iff (t : spec.Domain) (oa : spec.Range t → OracleComp spec α)
    (qc : QueryCount ι) (z : α × QueryCount ι) :
    z ∈ support (simulate ((OracleSpec.query t : OracleComp spec _) >>= oa) qc) ↔
      z.2 t ≠ 0 ∧ ∃ u, (z.1, Function.update z.2 t (z.2 t - 1)) ∈ support (simulate (oa u) qc) :=
  by
  refine ⟨?_, ?_⟩
  · intro hz
    exact
      ⟨apply_ne_zero_of_mem_support_simulate_queryBind hz,
        exists_mem_support_of_mem_support_simulate_queryBind hz⟩
  · rintro ⟨hz0, hu⟩
    rcases hu with ⟨u, hu⟩
    rcases
      (mem_support_simulate_iff (oa := oa u) qc (z := (z.1, Function.update z.2 t (z.2 t - 1)))).1
        hu with
      ⟨b, hb0, hbEq⟩
    have hbRun : (z.1, b) ∈ support ((simulateQ countingOracle (oa u)).run) := by
      simpa [simulate] using hb0
    have hbRun' : (z.1, b) ∈ support ((simulateQ (QueryImpl.id' spec).withCounting (oa u)).run) :=
      by simpa [countingOracle] using hbRun
    let q0 : QueryCount ι := QueryCount.single t + b
    have hq0mem :
      (z.1, q0) ∈ support (simulate ((OracleSpec.query t : OracleComp spec _) >>= oa) 0) :=
      by
      have hex :
        ∃ i a b',
          (a, b') ∈ support (simulateQ (QueryImpl.id' spec).withCounting (oa i)).run ∧
            (a, QueryCount.single t + b') = (z.1, q0) :=
        ⟨u, z.1, b, hbRun', by simp [q0]⟩
      simpa [simulate, countingOracle, QueryImpl.withCounting_apply] using hex
    have hqsum : qc + q0 = z.2 := by
      funext j
      have hbEqj : qc j + b j = (Function.update z.2 t (z.2 t - 1)) j := by
        simpa [Pi.add_apply] using congrFun hbEq j
      rcases eq_or_ne j t with rfl | hj
      · have hzpos : 0 < z.2 j := Nat.pos_of_ne_zero hz0
        simp only [q0, Pi.add_apply, QueryCount.single, Pi.single_eq_same,
          Function.update_self] at hbEqj ⊢
        omega
      · simp only [q0, Pi.add_apply, QueryCount.single, Pi.single_eq_of_ne hj,
          Function.update_of_ne hj] at hbEqj ⊢
        omega
    exact
      (mem_support_simulate_iff (oa := ((OracleSpec.query t : OracleComp spec _) >>= oa)) qc z).2
        ⟨q0, hq0mem, hqsum⟩


-- @@ L470-479 verbatim
lemma exists_mem_support_of_mem_support {oa : OracleComp spec α} {x : α} (hx : x ∈ support oa)
    (qc : QueryCount ι) : ∃ qc', (x, qc') ∈ support (simulate oa qc) := by
  have hx' : x ∈ support (Prod.fst <$> (simulateQ countingOracle oa).run) := by
    simpa [fst_map_run_simulateQ] using hx
  rw [support_map] at hx'
  obtain ⟨z, hz, rfl⟩ := hx'
  refine ⟨qc + z.2, (mem_support_simulate_iff (oa := oa) qc (z := (z.1, qc + z.2))).2
    ⟨z.2, ?_, rfl⟩⟩
  rw [simulate, support_map]
  exact ⟨z, hz, by simp [Prod.map]⟩


-- @@ L481-481 verbatim
end support


-- @@ L483-483 verbatim
end countingOracle
