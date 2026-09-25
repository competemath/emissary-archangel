/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.WriterCost


-- @@ L11-18 verbatim
/-!
# Query Cost Accounting

This file defines the `HasQuery`-level accounting surface for direct-style query programs.
A direct-style program is evaluated against a concrete `QueryImpl`, and query-cost statements
are phrased by running that implementation through the writer-cost instrumentation from
`WriterCost.lean`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open OracleSpec


-- @@ L24-24 verbatim
namespace HasQuery


-- @@ L26-26 verbatim
section programInstantiation


-- @@ L28-28 verbatim
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}


-- @@ L30-32 verbatim
/-- A direct-style computation parameterized by an oracle-query capability. -/
abbrev Program (spec : OracleSpec ι) (m : Type → Type*) (α : Type) :=
  [HasQuery spec m] → m α


-- @@ L34-34 verbatim
namespace Program


-- @@ L36-39 verbatim
/-- Evaluate a direct-style query program against a concrete implementation. -/
def eval (oa : Program spec m α) (impl : QueryImpl spec m) : m α := by
  letI := impl.toHasQuery
  exact oa


-- @@ L41-41 verbatim
section instrumentation


-- @@ L43-43 verbatim
variable [Monad m]


-- @@ L45-50 verbatim
/-- Evaluate a direct-style query program against an additive-cost instrumentation of `impl`. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (oa : Program spec (AddWriterT ω m) α)
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) : AddWriterT ω m α := by
  letI := (impl.withAddCost costFn).toHasQuery
  exact oa


-- @@ L52-56 verbatim
/-- Evaluate a direct-style query program against the unit-cost instrumentation of `impl`. -/
def withUnitCost (oa : Program spec (AddWriterT ℕ m) α)
    (impl : QueryImpl spec m) : AddWriterT ℕ m α := by
  letI := impl.withUnitCost.toHasQuery
  exact oa


-- @@ L58-61 verbatim
theorem withUnitCost_eq_withAddCost (oa : Program spec (AddWriterT ℕ m) α)
    (impl : QueryImpl spec m) :
    withUnitCost oa impl = withAddCost oa impl (fun _ ↦ 1) := by
  rfl


-- @@ L63-63 verbatim
end instrumentation


-- @@ L65-65 verbatim
end Program

-- @@ L66-66 verbatim
end programInstantiation


-- @@ L68-68 verbatim
section queryBounds


-- @@ L70-70 verbatim
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

-- @@ L71-71 verbatim
variable [Monad m] [LawfulMonad m]


-- @@ L73-81 expanded
lemma hasCost_withAddCost_query {ω : Type} [AddMonoid ω] (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (t : spec.Domain) :
    AddWriterT.HasCost
      (HasQuery.Program.withAddCost
        (fun [HasQuery spec (AddWriterT ω m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ω m) t)
        runtime costFn)
      (costFn t) :=
  by simp [HasQuery.Program.withAddCost]


-- @@ L83-95 verbatim
lemma queryBoundedAboveBy_withUnitCost_query
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedAboveBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  simpa [HasQuery.Program.withUnitCost] using
    AddWriterT.queryBoundedAboveBy_bind (n₁ := 1) (n₂ := 0)
      (AddWriterT.queryBoundedAboveBy_addTell 1)
      fun _ ↦ AddWriterT.queryBoundedAboveBy_monadLift (runtime t)


-- @@ L97-109 verbatim
lemma queryBoundedBelowBy_withUnitCost_query
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryBoundedBelowBy
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 := by
  simpa [HasQuery.Program.withUnitCost] using
    AddWriterT.queryBoundedBelowBy_bind (n₁ := 1) (n₂ := 0)
      (AddWriterT.queryBoundedBelowBy_addTell 1)
      fun _ ↦ AddWriterT.queryBoundedBelowBy_monadLift (runtime t)


-- @@ L111-121 verbatim
lemma queryCostExactly_withUnitCost_query
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl spec m) (t : spec.Domain) :
    AddWriterT.QueryCostExactly
      (HasQuery.Program.withUnitCost
        (fun [HasQuery spec (AddWriterT ℕ m)] =>
          HasQuery.query (spec := spec) (m := AddWriterT ℕ m) t)
        runtime)
      1 :=
  ⟨queryBoundedAboveBy_withUnitCost_query runtime t,
    queryBoundedBelowBy_withUnitCost_query runtime t⟩


-- @@ L123-123 verbatim
end queryBounds


-- @@ L125-125 verbatim
section costAccounting


-- @@ L127-127 verbatim
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} {α : Type}


-- @@ L129-131 verbatim
/-- A computation generic over a `HasQuery spec m` capability. -/
abbrev Computation (spec : OracleSpec ι) (m : Type → Type*) (α : Type) :=
  [HasQuery spec m] → m α


-- @@ L133-133 verbatim
section genericCost


-- @@ L135-135 verbatim
variable [Monad m]


-- @@ L137-142 verbatim
/-- Running `oa` in the additive-cost instrumentation of `runtime` yields an output-dependent
cost described by `f`. -/
def UsesCostAs {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (f : α → ω) : Prop :=
  AddWriterT.CostsAs (HasQuery.Program.withAddCost oa runtime costFn) f


-- @@ L144-148 expanded
/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs constant cost `w`. -/
def UsesCostExactly {ω : Type} [AddMonoid ω] (oa : Computation spec (AddWriterT ω m) α)
    (runtime : QueryImpl spec m) (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.HasCost (HasQuery.Program.withAddCost oa runtime costFn) w


-- @@ L150-157 verbatim
/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at most `w` on
every execution path. This is a semantic support bound, not merely an output-indexed cost
description. -/
def UsesCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtMost (HasQuery.Program.withAddCost oa runtime costFn) w


-- @@ L159-165 verbatim
/-- Running `oa` in the additive-cost instrumentation of `runtime` incurs cost at least `w` on
every execution path. -/
def UsesCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω] [MonadLiftT m SetM]
    [LawfulMonadLiftT m SetM]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (w : ω) : Prop :=
  AddWriterT.PathwiseCostAtLeast (HasQuery.Program.withAddCost oa runtime costFn) w


-- @@ L167-173 verbatim
lemma usesCostAtMost_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hwb : w ≤ b) :
    HasQuery.UsesCostAtMost oa runtime costFn b :=
  AddWriterT.pathwiseCostAtMost_of_hasCost h hwb


-- @@ L175-181 verbatim
lemma usesCostAtLeast_of_usesCostExactly {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w b : ω}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hbw : b ≤ w) :
    HasQuery.UsesCostAtLeast oa runtime costFn b :=
  AddWriterT.pathwiseCostAtLeast_of_hasCost h hbw


-- @@ L183-193 verbatim
lemma usesCostAtMost_query_of_le {ω : Type} [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) {b : ω}
    (ht : costFn t ≤ b) :
    HasQuery.UsesCostAtMost
      (fun [HasQuery spec (AddWriterT ω m)] =>
        HasQuery.query (spec := spec) (m := AddWriterT ω m) t)
      runtime costFn b :=
  usesCostAtMost_of_usesCostExactly
    (hasCost_withAddCost_query (runtime := runtime) (costFn := costFn) (t := t))
    ht


-- @@ L195-198 verbatim
/-- Unit-cost specialization: every query contributes cost `1`. -/
def UsesExactlyQueries (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  HasQuery.UsesCostExactly oa runtime (fun _ ↦ 1) n


-- @@ L200-204 verbatim
/-- Unit-cost specialization: every query contributes cost `1`, with an upper bound. -/
def UsesAtMostQueries [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedAboveBy (HasQuery.Program.withUnitCost oa runtime) n


-- @@ L206-210 verbatim
/-- Unit-cost specialization: every query contributes cost `1`, with a lower bound. -/
def UsesAtLeastQueries [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) (n : ℕ) : Prop :=
  AddWriterT.QueryBoundedBelowBy (HasQuery.Program.withUnitCost oa runtime) n


-- @@ L212-217 verbatim
lemma usesAtMostQueries_of_usesExactlyQueries
    [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hnb : n ≤ b) :
    HasQuery.UsesAtMostQueries oa runtime b :=
  usesCostAtMost_of_usesCostExactly h hnb


-- @@ L219-224 verbatim
lemma usesAtLeastQueries_of_usesExactlyQueries
    [LawfulMonad m] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m}
    {n b : ℕ} (h : HasQuery.UsesExactlyQueries oa runtime n) (hbn : b ≤ n) :
    HasQuery.UsesAtLeastQueries oa runtime b :=
  usesCostAtLeast_of_usesCostExactly h hbn


-- @@ L226-226 verbatim
end genericCost


-- @@ L228-228 verbatim
section expectedCost


-- @@ L230-231 verbatim
variable [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L233-244 verbatim
/-- The expected weighted query cost of `oa`, instantiated in `runtime` and instrumented by
`costFn`.

This is the primary expectation notion for generic `HasQuery` computations. It is computed from
the additive cost marginal in the base monad's subdistribution semantics, valued by `val`.

The unit-cost query-counting notion [`HasQuery.expectedQueries`] is a specialization of this
definition with `costFn := fun _ ↦ 1` and `val := fun n ↦ (n : ENNReal)`. -/
noncomputable def expectedQueryCost {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) (val : ω → ENNReal) : ENNReal :=
  AddWriterT.expectedCost (HasQuery.Program.withAddCost oa runtime costFn) val


-- @@ L246-251 verbatim
/-- The marginal distribution of weighted query costs induced by running `oa` in `runtime` with
query-cost function `costFn`. -/
def queryCostDist {ω : Type} [AddMonoid ω]
    (oa : Computation spec (AddWriterT ω m) α) (runtime : QueryImpl spec m)
    (costFn : spec.Domain → ω) : m ω :=
  AddWriterT.costs (HasQuery.Program.withAddCost oa runtime costFn)


-- @@ L253-256 verbatim
/-- The marginal distribution of the unit-cost query count induced by running `oa` in `runtime`. -/
abbrev queryCountDist
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m) : m ℕ :=
  HasQuery.queryCostDist oa runtime (fun _ ↦ 1)


-- @@ L258-262 verbatim
/-- Expected number of oracle queries made by `oa` when run in `runtime`, counting each query
with unit additive cost. -/
noncomputable abbrev expectedQueries
    (oa : Computation spec (AddWriterT ℕ m) α) (runtime : QueryImpl spec m) : ENNReal :=
  HasQuery.expectedQueryCost oa runtime (fun _ ↦ 1) (fun n ↦ (n : ENNReal))


-- @@ L264-277 expanded
omit [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] in
/-- Tail-sum formula for the expected number of oracle queries made by `oa` in `runtime`:

`E[number of queries] = ∑ i, Pr[i < number of queries]`.

This is the generic `HasQuery` version of [`AddWriterT.expectedCostNat_eq_tsum_tail_probs`]. -/
lemma expectedQueries_eq_tsum_tail_probs (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) :
    HasQuery.expectedQueries oa runtime =
      ∑' i : ℕ, probEvent (HasQuery.queryCountDist oa runtime) fun c ↦ i < c :=
  by
  simpa [HasQuery.expectedQueryCost, HasQuery.queryCountDist, HasQuery.queryCostDist,
    AddWriterT.expectedCostNat, HasQuery.Program.withUnitCost_eq_withAddCost] using
    AddWriterT.expectedCostNat_eq_tsum_tail_probs (oa := HasQuery.Program.withUnitCost oa runtime)


-- @@ L279-290 expanded
omit [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] in
/-- Tail domination bounds expected query count.

If `Pr[i < number of queries] ≤ a i` for every `i`, then
`ExpectedQueries[ oa in runtime ] ≤ ∑ i, a i`. -/
lemma expectedQueries_le_tsum_of_tail_probs_le (oa : Computation spec (AddWriterT ℕ m) α)
    (runtime : QueryImpl spec m) {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, (probEvent (HasQuery.queryCountDist oa runtime) fun c ↦ i < c) ≤ a i) :
    HasQuery.expectedQueries oa runtime ≤ ∑' i : ℕ, a i :=
  (HasQuery.expectedQueries_eq_tsum_tail_probs oa runtime).trans_le (ENNReal.tsum_le_tsum h)


-- @@ L292-304 expanded
/-- Finite tail-sum formula for expected query count under a pathwise upper bound.

If `oa` uses at most `n` oracle queries in every execution, then its expected query count is the
finite sum of the probabilities that the query count exceeds `i`, for `i < n`. -/
lemma expectedQueries_eq_sum_tail_probs_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime =
      ∑ i ∈ Finset.range n, probEvent (HasQuery.queryCountDist oa runtime) fun c ↦ i < c :=
  by
  simpa [HasQuery.expectedQueryCost, HasQuery.queryCostDist,
    HasQuery.Program.withUnitCost_eq_withAddCost] using
    (AddWriterT.expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost (oa :=
      HasQuery.Program.withUnitCost oa runtime) h)


-- @@ L306-313 verbatim
omit [LawfulMonadLiftT m SPMF] in
lemma expectedQueryCost_le_of_usesCostAtMost
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtMost oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val ≤ val w :=
  AddWriterT.expectedCost_le_of_pathwiseCostAtMost h hval


-- @@ L315-326 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
lemma expectedQueryCost_eq_tsum_outputs_of_usesCostAs {ω : Type} [AddMonoid ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {f : α → ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAs oa runtime costFn f) :
    HasQuery.expectedQueryCost oa runtime costFn val =
      ∑' a : α,
        probOutput (AddWriterT.outputs (HasQuery.Program.withAddCost oa runtime costFn)) a *
          val (f a) :=
  AddWriterT.expectedCost_eq_tsum_outputs_of_costsAs (oa :=
    HasQuery.Program.withAddCost oa runtime costFn) (f := f) (val := val) h


-- @@ L328-336 verbatim
omit [LawfulMonadLiftT m SPMF] in
lemma expectedQueries_le_of_usesAtMostQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtMostQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime ≤ n := by
  simpa [HasQuery.expectedQueryCost, HasQuery.Program.withUnitCost_eq_withAddCost] using
    (AddWriterT.expectedCost_le_of_pathwiseCostAtMost
      (oa := HasQuery.Program.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      Nat.mono_cast)


-- @@ L338-338 verbatim
end expectedCost


-- @@ L340-340 verbatim
section expectedCostPMF


-- @@ L342-343 verbatim
variable [Monad m] [MonadLiftT m PMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L345-353 verbatim
lemma le_expectedQueryCost_of_usesCostAtLeast
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostAtLeast oa runtime costFn w) (hval : Monotone val) :
    val w ≤ HasQuery.expectedQueryCost oa runtime costFn val := by
  simpa [HasQuery.expectedQueryCost, HasQuery.Program.withUnitCost_eq_withAddCost] using
    (AddWriterT.le_expectedCost_of_pathwiseCostAtLeast
      (oa := HasQuery.Program.withAddCost oa runtime costFn) (w := w) (val := val) h hval)


-- @@ L355-365 verbatim
lemma expectedQueryCost_eq_of_usesCostExactly
    {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : Computation spec (AddWriterT ω m) α} {runtime : QueryImpl spec m}
    {costFn : spec.Domain → ω} {w : ω} {val : ω → ENNReal}
    (h : HasQuery.UsesCostExactly oa runtime costFn w) (hval : Monotone val) :
    HasQuery.expectedQueryCost oa runtime costFn val = val w :=
  le_antisymm
    (expectedQueryCost_le_of_usesCostAtMost
      (usesCostAtMost_of_usesCostExactly h le_rfl) hval)
    (le_expectedQueryCost_of_usesCostAtLeast
      (usesCostAtLeast_of_usesCostExactly h le_rfl) hval)


-- @@ L367-374 verbatim
lemma le_expectedQueries_of_usesAtLeastQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesAtLeastQueries oa runtime n) :
    (n : ENNReal) ≤ HasQuery.expectedQueries oa runtime := by
  simpa [HasQuery.expectedQueryCost, HasQuery.Program.withUnitCost_eq_withAddCost] using
    (AddWriterT.le_expectedCost_of_pathwiseCostAtLeast
      (oa := HasQuery.Program.withUnitCost oa runtime) (w := n) (val := fun k ↦ (k : ENNReal)) h
      Nat.mono_cast)


-- @@ L376-384 verbatim
lemma expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
    [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (hUpper : HasQuery.UsesAtMostQueries oa runtime n)
    (hLower : HasQuery.UsesAtLeastQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime = n :=
  le_antisymm
    (expectedQueries_le_of_usesAtMostQueries hUpper)
    (le_expectedQueries_of_usesAtLeastQueries hLower)


-- @@ L386-393 verbatim
lemma expectedQueries_eq_of_usesExactlyQueries [LawfulMonad m]
    {oa : Computation spec (AddWriterT ℕ m) α} {runtime : QueryImpl spec m} {n : ℕ}
    (h : HasQuery.UsesExactlyQueries oa runtime n) :
    HasQuery.expectedQueries oa runtime = n :=
  expectedQueries_eq_of_usesAtMostQueries_of_usesAtLeastQueries
    (m := m) (oa := oa) (runtime := runtime) (n := n)
    (usesAtMostQueries_of_usesExactlyQueries h le_rfl)
    (usesAtLeastQueries_of_usesExactlyQueries h le_rfl)


-- @@ L395-395 verbatim
end expectedCostPMF


-- @@ L397-404 verbatim
/-- `Queries[ oa in runtime ] = n` means that the generic `HasQuery` computation `oa` makes
exactly `n` oracle queries when instantiated in `runtime` and instrumented with unit additive
cost per query.

The computation `oa` is written in direct `HasQuery` style. The notation elaborates it against
the unit-cost analysis monad induced by `runtime`, so statements can usually be written without
explicit monad annotations such as `m := AddWriterT ℕ m`. -/
syntax:max "Queries[ " term " in " term " ]" " = " term:50 : term


-- @@ L406-410 expanded
macro_rules
  |
  `(HasQuery.UsesExactlyQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n) =>
    `(HasQuery.UsesExactlyQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n)


-- @@ L412-417 verbatim
/-- `Queries[ oa in runtime ] ≤ n` means that every execution path of `oa` makes at most `n`
oracle queries when run in the unit-cost instrumentation of `runtime`.

This packages the common cryptographic statement “the construction uses at most `n` queries” on
top of [`HasQuery.UsesAtMostQueries`]. -/
syntax:max "Queries[ " term " in " term " ]" " ≤ " term:50 : term


-- @@ L419-423 expanded
macro_rules
  |
  `(HasQuery.UsesAtMostQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n) =>
    `(HasQuery.UsesAtMostQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n)


-- @@ L425-430 verbatim
/-- `Queries[ oa in runtime ] ≥ n` means that every execution of `oa` in the unit-cost
instrumentation of `runtime` incurs at least `n` query-cost units.

This is less common than the exact and upper-bound forms, but it is useful for statements saying
that a construction must query the oracle at least a certain number of times. -/
syntax:max "Queries[ " term " in " term " ]" " ≥ " term:50 : term


-- @@ L432-436 expanded
macro_rules
  |
  `(HasQuery.UsesAtLeastQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n) =>
    `(HasQuery.UsesAtLeastQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $n)


-- @@ L438-441 verbatim
/-- `QueryCost[ oa in runtime ] = n` is the unit-cost specialization of weighted query cost:
each oracle query contributes additive cost `1`, so the total query cost is just the number of
queries made by `oa`. -/
syntax:max "QueryCost[ " term " in " term " ]" " = " term:50 : term


-- @@ L443-447 expanded
macro_rules
  |
  `(HasQuery.UsesExactlyQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w) =>
    `(HasQuery.UsesExactlyQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w)


-- @@ L449-455 verbatim
/-- `QueryCost[ oa in runtime by costFn ] = w` means that `oa`, instantiated in `runtime` and
instrumented so that each query `t` contributes cost `costFn t`, has constant total query cost
`w`.

Use this when the cost model is not unit cost, for example when different query families or
different query shapes carry different weights. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " = " term:50 : term


-- @@ L457-461 expanded
macro_rules
  |
  `(HasQuery.UsesCostExactly
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w) =>
    `(HasQuery.UsesCostExactly
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w)


-- @@ L463-465 verbatim
/-- `QueryCost[ oa in runtime ] ≤ n` is the unit-cost specialization of pathwise query-cost upper
bounds. It says that every execution of `oa` makes at most `n` oracle queries. -/
syntax:max "QueryCost[ " term " in " term " ]" " ≤ " term:50 : term


-- @@ L467-471 expanded
macro_rules
  |
  `(HasQuery.UsesAtMostQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w) =>
    `(HasQuery.UsesAtMostQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w)


-- @@ L473-477 verbatim
/-- `QueryCost[ oa in runtime by costFn ] ≤ w` means that every execution path of `oa` has total
query cost bounded above by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≤ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≤ " term:50 : term


-- @@ L479-483 expanded
macro_rules
  |
  `(HasQuery.UsesCostAtMost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w) =>
    `(HasQuery.UsesCostAtMost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w)


-- @@ L485-487 verbatim
/-- `QueryCost[ oa in runtime ] ≥ n` is the unit-cost specialization of pathwise query-cost lower
bounds. It says that every execution of `oa` makes at least `n` oracle queries. -/
syntax:max "QueryCost[ " term " in " term " ]" " ≥ " term:50 : term


-- @@ L489-493 expanded
macro_rules
  |
  `(HasQuery.UsesAtLeastQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w) =>
    `(HasQuery.UsesAtLeastQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        $w)


-- @@ L495-499 verbatim
/-- `QueryCost[ oa in runtime by costFn ] ≥ w` means that every execution path of `oa` has total
query cost bounded below by `w` under the weighting function `costFn`.

This is the weighted analogue of [`Queries[ oa in runtime ] ≥ n`]. -/
syntax:max "QueryCost[ " term " in " term " by " term " ]" " ≥ " term:50 : term


-- @@ L501-505 expanded
macro_rules
  |
  `(HasQuery.UsesCostAtLeast
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w) =>
    `(HasQuery.UsesCostAtLeast
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $w)


-- @@ L507-509 verbatim
/-- `ExpectedQueryCost[ oa in runtime ]` is the expected number of oracle queries made by `oa`
when run in `runtime`, viewed as the unit-cost specialization of weighted expected query cost. -/
syntax:max "ExpectedQueryCost[ " term " in " term " ]" : term


-- @@ L511-515 expanded
macro_rules
  |
  `(HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        (fun _ ↦ 1) (fun n ↦ (n : ENNReal))) =>
    `(HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime
        (fun _ ↦ 1) (fun n ↦ (n : ENNReal)))


-- @@ L517-523 verbatim
/-- `ExpectedQueryCost[ oa in runtime by costFn via val ]` is the expected weighted query cost of
`oa` when instantiated in `runtime`.

Each query `t` contributes additive cost `costFn t`, and the total cost is then valued by
`val : ω → ENNReal` before taking expectation. This is the primary expected-cost term for generic
`HasQuery` constructions. -/
syntax:max "ExpectedQueryCost[ " term " in " term " by " term " via " term " ]" : term


-- @@ L525-529 expanded
macro_rules
  |
  `(HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $val) =>
    `(HasQuery.expectedQueryCost
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT _ _)] → AddWriterT _ _ _)) $runtime
        $costFn $val)


-- @@ L531-540 verbatim
/-- `ExpectedQueries[ oa in runtime ]` is the expected number of oracle queries made by `oa` when
run in `runtime`, with each query carrying unit additive cost.

The result is an `ℝ≥0∞` expectation, so it can be compared directly against natural-number
bounds such as `ExpectedQueries[ oa in runtime ] ≤ n`.

This is the unit-cost specialization of
[`ExpectedQueryCost[ oa in runtime by costFn via val ]`], with `costFn := fun _ ↦ 1` and
`val := fun n ↦ (n : ENNReal)`. -/
syntax:max "ExpectedQueries[ " term " in " term " ]" : term


-- @@ L542-546 expanded
macro_rules
  |
  `(HasQuery.expectedQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _))
        $runtime) =>
    `(HasQuery.expectedQueries
        (((fun [HasQuery _ _] => $oa) : [HasQuery _ (AddWriterT ℕ _)] → AddWriterT ℕ _ _)) $runtime)


-- @@ L548-548 verbatim
end costAccounting


-- @@ L550-550 verbatim
end HasQuery
