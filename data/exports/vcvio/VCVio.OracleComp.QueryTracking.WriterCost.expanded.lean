/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.QueryTracking.CountingOracle
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Map
public import ToMathlib.Control.WriterT
public import ToMathlib.Probability.ProbabilityMassFunction.TailSums
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


-- @@ L18-23 verbatim
/-!
# Writer Cost Accounting

This file collects reusable `AddWriterT` facts for pathwise and expected cost reasoning.
It also equips `QueryImpl` with additive writer-cost instrumentation.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open OracleSpec


-- @@ L29-29 verbatim
namespace QueryImpl


-- @@ L31-31 verbatim
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}


-- @@ L33-33 verbatim
section addCost


-- @@ L35-35 verbatim
variable [Monad m]


-- @@ L37-42 verbatim
/-- Instrument an implementation with additive cost accumulation in an `AddWriterT` layer. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω m) :=
  QueryImpl.withCost (spec := spec) (m := m) impl
    (fun t ↦ Multiplicative.ofAdd (costFn t))


-- @@ L44-49 verbatim
@[simp]
lemma withAddCost_apply {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    impl.withAddCost costFn t =
      (do AddWriterT.addTell (M := m) (costFn t); liftM (impl t)) := by
  simp [withAddCost, AddWriterT.addTell, QueryImpl.withCost]


-- @@ L51-58 verbatim
/-- Cost instrumentation on a left-summand query, with the component response type exposed. -/
lemma withAddCost_apply_inl {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {ω : Type} [AddMonoid ω] (impl : QueryImpl (spec₁ + spec₂) m)
    (costFn : (spec₁ + spec₂).Domain → ω) (t : spec₁.Domain) :
    impl.withAddCost costFn (Sum.inl t) = (do
      AddWriterT.addTell (costFn (Sum.inl t))
      liftM (impl.restrictLeft t)) := by
  rw [withAddCost_apply, restrictLeft_apply]


-- @@ L60-67 verbatim
/-- Cost instrumentation on a right-summand query, with the component response type exposed. -/
lemma withAddCost_apply_inr {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {ω : Type} [AddMonoid ω] (impl : QueryImpl (spec₁ + spec₂) m)
    (costFn : (spec₁ + spec₂).Domain → ω) (t : spec₂.Domain) :
    impl.withAddCost costFn (Sum.inr t) = (do
      AddWriterT.addTell (costFn (Sum.inr t))
      liftM (impl.restrictRight t)) := by
  rw [withAddCost_apply, restrictRight_apply]


-- @@ L69-72 verbatim
/-- Instrument an implementation with unit additive cost for every query. -/
def withUnitCost (impl : QueryImpl spec m) :
    QueryImpl spec (AddWriterT ℕ m) :=
  impl.withAddCost (fun _ ↦ 1)


-- @@ L74-78 verbatim
@[simp]
lemma withUnitCost_apply (impl : QueryImpl spec m) (t : spec.Domain) :
    impl.withUnitCost t =
      (do AddWriterT.addTell (M := m) 1; liftM (impl t)) := by
  simp [withUnitCost]


-- @@ L80-80 verbatim
end addCost


-- @@ L82-82 verbatim
end QueryImpl


-- @@ L84-84 verbatim
namespace AddWriterT


-- @@ L86-86 verbatim
variable {m : Type → Type*} [Monad m]

-- @@ L87-87 verbatim
variable {α β : Type}


-- @@ L89-89 verbatim
section pathwiseCost


-- @@ L91-91 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L93-97 verbatim
/-- Pathwise upper bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at most `w`. -/
def PathwiseCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, Multiplicative.toAdd z.2 ≤ w


-- @@ L99-103 verbatim
/-- Pathwise lower bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at least `w`. -/
def PathwiseCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, w ≤ Multiplicative.toAdd z.2


-- @@ L105-113 verbatim
/-- Pathwise exactness on support for an `AddWriterT` computation: every reachable execution result
carries exactly the additive cost `w`.

This is the weak extensional notion of pathwise exactness. If `oa.run` has empty support, it holds
vacuously for every `w`. Use [`AddWriterT.PathwiseHasCost`] when the intended meaning is that `oa`
has an exact pathwise cost and admits at least one reachable execution. -/
def PathwiseCostEqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w


-- @@ L115-119 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
@[simp] lemma pathwiseCostEqOnSupport_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseCostEqOnSupport oa w ↔ PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w :=
  Iff.rfl


-- @@ L121-130 verbatim
/-- Pathwise exact cost for an `AddWriterT` computation: `oa` has at least one reachable execution,
and every reachable execution result carries exactly the additive cost `w`.

This is the strong semantic notion of exact cost over execution paths.
Unlike [`AddWriterT.HasCost`], it does not require cost to be recoverable
from the final output alone. Unlike
[`AddWriterT.PathwiseCostEqOnSupport`], it is not vacuous on computations with empty support. -/
def PathwiseHasCost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w


-- @@ L132-137 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
@[simp] lemma pathwiseHasCost_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseHasCost oa w ↔
      (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w :=
  Iff.rfl


-- @@ L139-143 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseHasCost.nonempty {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    (support oa.run).Nonempty :=
  h.1


-- @@ L145-149 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseCostEqOnSupport.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtMost oa w :=
  h.1


-- @@ L151-155 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseCostEqOnSupport.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtLeast oa w :=
  h.2


-- @@ L157-161 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseHasCost.eqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostEqOnSupport oa w :=
  h.2


-- @@ L163-167 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseHasCost.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtMost oa w :=
  h.2.1


-- @@ L169-173 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseHasCost.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtLeast oa w :=
  h.2.2


-- @@ L175-182 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma PathwiseHasCost.unique {ω : Type} [AddMonoid ω] [PartialOrder ω]
    {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : PathwiseHasCost oa w₂) :
    w₁ = w₂ := by
  obtain ⟨z, hz⟩ := h₁.nonempty
  exact le_antisymm ((h₁.atLeast z hz).trans (h₂.atMost z hz))
    ((h₂.atLeast z hz).trans (h₁.atMost z hz))


-- @@ L184-194 verbatim
lemma pathwiseCostAtMost_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hwb : w ≤ b) :
    PathwiseCostAtMost oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h, support_map] at hzCost
  obtain ⟨_, _, hzCost⟩ := hzCost
  simpa [hzCost] using hwb


-- @@ L196-206 verbatim
lemma pathwiseCostAtLeast_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hbw : b ≤ w) :
    PathwiseCostAtLeast oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h, support_map] at hzCost
  obtain ⟨_, _, hzCost⟩ := hzCost
  simpa [hzCost] using hbw


-- @@ L208-208 verbatim
end pathwiseCost


-- @@ L210-210 verbatim
section expectedCost


-- @@ L212-212 verbatim
variable {ω : Type}

-- @@ L213-214 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [EvalDistCompatible m]


-- @@ L216-224 expanded
/-- The expected additive cost of an `AddWriterT` computation, obtained by taking the expectation
of its cost marginal.

This expectation is computed over the base monad's subdistribution semantics on `oa.costs`. In
particular, if the underlying computation can fail, the missing mass contributes `0`, exactly as
for other `wp`-style expectations in VCVio. -/
noncomputable def expectedCost (oa : AddWriterT ω m α) (val : ω → ENNReal) : ENNReal :=
  ∑' w : ω, probOutput oa.costs w * val w


-- @@ L226-229 verbatim
/-- Convenience specialization of [`AddWriterT.expectedCost`] to natural-valued additive costs. -/
noncomputable abbrev expectedCostNat
    (oa : AddWriterT ℕ m α) : ENNReal :=
  expectedCost oa (fun n ↦ ↑n)


-- @@ L231-246 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [LawfulMonadLiftT m SPMF]
    [EvalDistCompatible m] in
/-- Tail-sum formula for the natural-valued expected cost of an `AddWriterT` computation:

`E[cost] = ∑ i, Pr[i < cost]`.

This is the standard discrete expectation identity specialized to the writer-cost marginal. -/
lemma expectedCostNat_eq_tsum_tail_probs (oa : AddWriterT ℕ m α) :
    expectedCostNat oa = ∑' i : ℕ, probEvent oa.costs fun c ↦ i < c :=
  by
  unfold expectedCostNat expectedCost
  rw [ENNReal.tsum_mul_nat_eq_tsum_tail (fun n ↦ probOutput oa.costs n)]
  refine tsum_congr fun i ↦ ?_
  rw [probEvent_eq_tsum_indicator]
  refine tsum_congr fun n ↦ ?_
  by_cases h : i < n <;> simp [Set.indicator, h]


-- @@ L248-258 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [LawfulMonadLiftT m SPMF]
    [EvalDistCompatible m] in
/-- Tail domination bounds the expected natural-valued writer cost.

If the tail probability `Pr[i < cost]` is bounded by `a i` for every `i`, then
`E[cost] ≤ ∑ i, a i`. -/
lemma expectedCostNat_le_tsum_of_tail_probs_le (oa : AddWriterT ℕ m α) {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, (probEvent oa.costs fun c ↦ i < c) ≤ a i) : expectedCostNat oa ≤ ∑' i : ℕ, a i :=
  (expectedCostNat_eq_tsum_tail_probs oa).trans_le (ENNReal.tsum_le_tsum h)


-- @@ L260-277 expanded
omit [LawfulMonadLiftT m SPMF] in
/-- Finite tail-sum formula for natural-valued writer cost under a pathwise upper bound.

If every execution path of `oa` incurs cost at most `n`, then the tail probabilities vanish above
`n`, so the infinite tail sum truncates to `Finset.range n`. -/
lemma expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {n : ℕ} (h : PathwiseCostAtMost oa n) :
    expectedCostNat oa = ∑ i ∈ Finset.range n, probEvent oa.costs fun c ↦ i < c :=
  by
  rw [expectedCostNat_eq_tsum_tail_probs]
  symm
  rw [tsum_eq_sum (s := Finset.range n) (fun b hb ↦ ?_)]
  · have hnb : n ≤ b := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hb)
    refine probEvent_eq_zero fun c hc ↦ ?_
    rw [AddWriterT.costs_def, support_map] at hc
    rcases hc with ⟨z, hz, rfl⟩
    exact not_lt_of_ge (le_trans (h z hz) hnb)


-- @@ L279-294 expanded
omit [LawfulMonadLiftT m SetM] [LawfulMonadLiftT m SPMF] in
lemma expectedCost_le_of_support_bound (oa : AddWriterT ω m α) (val : ω → ENNReal) (c : ENNReal)
    (h : ∀ w ∈ support oa.costs, val w ≤ c) : expectedCost oa val ≤ c :=
  by
  unfold expectedCost
  calc
    ∑' w : ω, probOutput oa.costs w * val w ≤ ∑' w : ω, probOutput oa.costs w * c :=
      ENNReal.tsum_le_tsum fun w ↦ by
        by_cases hw : w ∈ support oa.costs
        · exact mul_le_mul_of_nonneg_left (h w hw) zero_le
        · rw [probOutput_eq_zero_of_not_mem_support hw, zero_mul, zero_mul]
    _ = (∑' w : ω, probOutput oa.costs w) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by gcongr; exact tsum_probOutput_le_one
    _ = c := one_mul c


-- @@ L296-305 verbatim
omit [LawfulMonadLiftT m SPMF] in
lemma expectedCost_le_of_pathwiseCostAtMost [AddMonoid ω]
    [LawfulMonad m] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} {val : ω → ENNReal}
    (h : PathwiseCostAtMost oa w) (hval : Monotone val) :
    expectedCost oa val ≤ val w := by
  refine expectedCost_le_of_support_bound oa val (val w) fun c hc ↦ ?_
  rw [AddWriterT.costs_def, support_map] at hc
  rcases hc with ⟨z, hz, rfl⟩
  exact hval (h z hz)


-- @@ L307-326 expanded
omit [LawfulMonadLiftT m SPMF] in
lemma le_expectedCost_of_pathwiseCostAtLeast [AddMonoid ω] [LawfulMonad m] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} {val : ω → ENNReal} (h : PathwiseCostAtLeast oa w)
    (hval : Monotone val) (hnf : probFailure oa.costs = 0) : val w ≤ expectedCost oa val :=
  by
  unfold expectedCost
  have hmass : ∑' c : ω, probOutput oa.costs c = 1 := by
    rw [tsum_probOutput_eq_sub (mx := oa.costs), hnf, tsub_zero]
  calc
    val w = (∑' c : ω, probOutput oa.costs c) * val w := by rw [hmass, one_mul]
    _ = ∑' c : ω, probOutput oa.costs c * val w := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' c : ω, probOutput oa.costs c * val c :=
      by
      refine ENNReal.tsum_le_tsum fun c ↦ ?_
      by_cases hc : c ∈ support oa.costs
      · rw [AddWriterT.costs_def, support_map] at hc
        rcases hc with ⟨z, hz, rfl⟩
        gcongr
        exact hval (h z hz)
      · rw [probOutput_eq_zero_of_not_mem_support hc, zero_mul, zero_mul]


-- @@ L328-343 expanded
omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [EvalDistCompatible m] in
lemma expectedCost_eq_tsum_outputs_of_costsAs [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [LawfulMonad m] {oa : AddWriterT ω m α} {f : α → ω} {val : ω → ENNReal} (h : oa.CostsAs f) :
    expectedCost oa val = ∑' a : α, probOutput oa.outputs a * val (f a) := by
  classical
  let : DecidableEq ω := Classical.decEq ω
  unfold expectedCost
  rw [h]
  simp_rw [probOutput_map_eq_tsum, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a ↦ ?_
  rw [ENNReal.tsum_mul_left]
  simp


-- @@ L345-345 verbatim
end expectedCost


-- @@ L347-347 verbatim
section weightedPathwiseBounds


-- @@ L349-349 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

-- @@ L350-350 verbatim
variable {ω : Type} [AddCommMonoid ω] [PartialOrder ω]


-- @@ L352-354 verbatim
lemma pathwiseCostAtMost_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtMost (pure x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost]


-- @@ L356-358 verbatim
lemma pathwiseCostAtLeast_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtLeast (pure x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast]


-- @@ L360-363 verbatim
lemma pathwiseCostEqOnSupport_pure [LawfulMonad m] (x : α) :
    PathwiseCostEqOnSupport (pure x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩


-- @@ L365-370 verbatim
lemma pathwiseHasCost_pure [LawfulMonad m] (x : α) :
    PathwiseHasCost (pure x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩⟩
  rw [WriterT.run_pure, support_pure]
  exact ⟨(x, 1), by simp⟩


-- @@ L372-374 verbatim
lemma pathwiseCostAtMost_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost, support_map]


-- @@ L376-378 verbatim
lemma pathwiseCostAtLeast_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast, support_map]


-- @@ L380-383 verbatim
lemma pathwiseCostEqOnSupport_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩


-- @@ L385-393 verbatim
lemma pathwiseHasCost_monadLift_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.run_monadLift, support_map]
  exact ⟨a, ha, rfl⟩


-- @@ L395-397 verbatim
lemma pathwiseCostAtMost_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (liftM x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost, support_map]


-- @@ L399-401 verbatim
lemma pathwiseCostAtLeast_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (liftM x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast, support_map]


-- @@ L403-406 verbatim
lemma pathwiseCostEqOnSupport_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (liftM x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩


-- @@ L408-416 verbatim
lemma pathwiseHasCost_liftM_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (liftM x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.liftM_def, WriterT.run_mk, support_map]
  exact ⟨a, ha, rfl⟩


-- @@ L418-420 verbatim
lemma pathwiseCostAtMost_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseCostAtMost_monadLift (m := m) (x := (liftM x : m α))


-- @@ L422-424 verbatim
lemma pathwiseCostAtLeast_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseCostAtLeast_monadLift (m := m) (x := (liftM x : m α))


-- @@ L426-430 verbatim
lemma pathwiseCostEqOnSupport_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_probCompLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_probCompLift (m := m) (ω := ω) x⟩


-- @@ L432-435 verbatim
lemma pathwiseHasCost_probCompLift_of_supportNonempty [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) (hx : (support (liftM x : m α)).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseHasCost_monadLift_of_supportNonempty (m := m) (ω := ω) (x := (liftM x : m α)) hx


-- @@ L437-441 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma pathwiseCostAtMost_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtMost oa w₁) (hw : w₁ ≤ w₂) :
    PathwiseCostAtMost oa w₂ :=
  fun z hz ↦ (h z hz).trans hw


-- @@ L443-447 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma pathwiseCostAtLeast_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtLeast oa w₂) (hw : w₁ ≤ w₂) :
    PathwiseCostAtLeast oa w₁ :=
  fun z hz ↦ hw.trans (h z hz)


-- @@ L449-451 verbatim
lemma pathwiseCostAtMost_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtMost (AddWriterT.addTell (M := m) w) w := by
  simp [PathwiseCostAtMost]


-- @@ L453-455 verbatim
lemma pathwiseCostAtLeast_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtLeast (AddWriterT.addTell (M := m) w) w := by
  simp [PathwiseCostAtLeast]


-- @@ L457-459 verbatim
lemma pathwiseCostEqOnSupport_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostEqOnSupport (AddWriterT.addTell (M := m) w) w :=
  ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩


-- @@ L461-465 verbatim
lemma pathwiseHasCost_addTell [LawfulMonad m] (w : ω) :
    PathwiseHasCost (AddWriterT.addTell (M := m) w) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩⟩
  rw [AddWriterT.run_addTell, support_pure]
  exact ⟨(PUnit.unit, Multiplicative.ofAdd w), by simp⟩


-- @@ L467-473 verbatim
lemma pathwiseCostAtMost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtMost oa w) :
    PathwiseCostAtMost (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'


-- @@ L475-481 verbatim
lemma pathwiseCostAtLeast_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtLeast oa w) :
    PathwiseCostAtLeast (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'


-- @@ L483-486 verbatim
lemma pathwiseCostEqOnSupport_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostEqOnSupport (f <$> oa) w :=
  ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩


-- @@ L488-495 verbatim
lemma pathwiseHasCost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseHasCost oa w) :
    PathwiseHasCost (f <$> oa) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩⟩
  rcases h.nonempty with ⟨z, hz⟩
  refine ⟨Prod.map f id z, ?_⟩
  rw [WriterT.run_map, support_map]
  exact ⟨z, hz, rfl⟩


-- @@ L497-509 verbatim
lemma pathwiseCostAtMost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtMost oa w₁) (h₂ : ∀ a, PathwiseCostAtMost (f a) w₂) :
    PathwiseCostAtMost (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨⟨a, wa⟩, haw, hz⟩
  rw [support_map] at hz
  rcases hz with ⟨⟨b, wb⟩, hbw, rfl⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)


-- @@ L511-523 verbatim
lemma pathwiseCostAtLeast_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtLeast oa w₁) (h₂ : ∀ a, PathwiseCostAtLeast (f a) w₂) :
    PathwiseCostAtLeast (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨⟨a, wa⟩, haw, hz⟩
  rw [support_map] at hz
  rcases hz with ⟨⟨b, wb⟩, hbw, rfl⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)


-- @@ L525-530 verbatim
lemma pathwiseCostEqOnSupport_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostEqOnSupport oa w₁) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w₂) :
    PathwiseCostEqOnSupport (oa >>= f) (w₁ + w₂) :=
  ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩


-- @@ L532-544 verbatim
lemma pathwiseHasCost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : ∀ a, PathwiseHasCost (f a) w₂) :
    PathwiseHasCost (oa >>= f) (w₁ + w₂) := by
  refine ⟨?_, ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩⟩
  rcases h₁.nonempty with ⟨⟨a, wa⟩, haw⟩
  rcases (h₂ a).nonempty with ⟨⟨b, wb⟩, hbw⟩
  refine ⟨(b, wa * wb), ?_⟩
  rw [WriterT.run_bind, mem_support_bind_iff]
  refine ⟨(a, wa), haw, ?_⟩
  rw [support_map]
  exact ⟨(b, wb), hbw, rfl⟩


-- @@ L546-550 verbatim
lemma pathwiseHasCost_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa 0) (h₂ : ∀ a, PathwiseHasCost (f a) w) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [zero_add] using pathwiseHasCost_bind (w₁ := 0) (w₂ := w) h₁ h₂


-- @@ L552-556 verbatim
lemma pathwiseHasCost_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa w) (h₂ : ∀ a, PathwiseHasCost (f a) 0) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [add_zero] using pathwiseHasCost_bind (w₁ := w) (w₂ := 0) h₁ h₂


-- @@ L558-562 verbatim
lemma pathwiseCostEqOnSupport_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa 0) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [zero_add] using pathwiseCostEqOnSupport_bind (w₁ := 0) (w₂ := w) h₁ h₂


-- @@ L564-568 verbatim
lemma pathwiseCostEqOnSupport_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa w) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) 0) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [add_zero] using pathwiseCostEqOnSupport_bind (w₁ := w) (w₂ := 0) h₁ h₂


-- @@ L570-584 verbatim
lemma pathwiseCostAtMost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtMost (f i) k) :
    PathwiseCostAtMost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      have hf : f = (Fin.elim0 : Fin 0 → AddWriterT ω m α) := funext fun i => Fin.elim0 i
      subst f
      rw [Fin.mOfFn, zero_nsmul]
      exact pathwiseCostAtMost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      simpa [add_comm] using
        (pathwiseCostAtMost_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦ pathwiseCostAtMost_map (Fin.cons a) (ih (fun i ↦ h i.succ))))


-- @@ L586-600 verbatim
lemma pathwiseCostAtLeast_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtLeast (f i) k) :
    PathwiseCostAtLeast (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      have hf : f = (Fin.elim0 : Fin 0 → AddWriterT ω m α) := funext fun i => Fin.elim0 i
      subst f
      rw [Fin.mOfFn, zero_nsmul]
      exact pathwiseCostAtLeast_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      simpa [add_comm] using
        (pathwiseCostAtLeast_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦ pathwiseCostAtLeast_map (Fin.cons a) (ih (fun i ↦ h i.succ))))


-- @@ L602-614 verbatim
lemma pathwiseHasCost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseHasCost (f i) k) :
    PathwiseHasCost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      simpa [Fin.mOfFn, zero_nsmul] using
        (pathwiseHasCost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α)))
  | succ n ih =>
      let consA : α → (Fin n → α) → Fin n.succ → α :=
        fun a ↦ @Fin.cons n (fun _ : Fin n.succ ↦ α) a
      simpa [Fin.mOfFn, succ_nsmul', add_comm, consA] using
        pathwiseHasCost_bind (m := m) (ω := ω) (w₁ := k) (w₂ := n • k) (h 0)
          (fun a ↦ pathwiseHasCost_map (f := consA a) (ih (fun i ↦ h i.succ)))


-- @@ L616-616 verbatim
end weightedPathwiseBounds


-- @@ L618-618 verbatim
section unitCostBounds


-- @@ L620-620 verbatim
variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L622-624 verbatim
/-- Pathwise upper bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedAboveBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtMost oa n


-- @@ L626-628 verbatim
/-- Pathwise lower bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedBelowBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtLeast oa n


-- @@ L630-632 verbatim
lemma queryBoundedAboveBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedAboveBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_pure x


-- @@ L634-636 verbatim
lemma queryBoundedBelowBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedBelowBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_pure x


-- @@ L638-640 verbatim
lemma queryBoundedAboveBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedAboveBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_monadLift x


-- @@ L642-644 verbatim
lemma queryBoundedBelowBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedBelowBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_monadLift x


-- @@ L646-650 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma queryBoundedAboveBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedAboveBy oa n₁) (hn : n₁ ≤ n₂) :
    QueryBoundedAboveBy oa n₂ :=
  pathwiseCostAtMost_mono h hn


-- @@ L652-656 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma queryBoundedBelowBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedBelowBy oa n₂) (hn : n₁ ≤ n₂) :
    QueryBoundedBelowBy oa n₁ :=
  pathwiseCostAtLeast_mono h hn


-- @@ L658-660 verbatim
lemma queryBoundedAboveBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedAboveBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtMost_addTell w


-- @@ L662-664 verbatim
lemma queryBoundedBelowBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedBelowBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtLeast_addTell w


-- @@ L666-669 verbatim
lemma queryBoundedAboveBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedAboveBy oa n) :
    QueryBoundedAboveBy (f <$> oa) n :=
  pathwiseCostAtMost_map f h


-- @@ L671-674 verbatim
lemma queryBoundedBelowBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedBelowBy oa n) :
    QueryBoundedBelowBy (f <$> oa) n :=
  pathwiseCostAtLeast_map f h


-- @@ L676-680 verbatim
lemma queryBoundedAboveBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedAboveBy oa n₁) (h₂ : ∀ a, QueryBoundedAboveBy (f a) n₂) :
    QueryBoundedAboveBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtMost_bind h₁ h₂


-- @@ L682-686 verbatim
lemma queryBoundedBelowBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedBelowBy oa n₁) (h₂ : ∀ a, QueryBoundedBelowBy (f a) n₂) :
    QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtLeast_bind h₁ h₂


-- @@ L688-691 verbatim
lemma queryBoundedAboveBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedAboveBy (f i) k) :
    QueryBoundedAboveBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtMost_fin_mOfFn h


-- @@ L693-696 verbatim
lemma queryBoundedBelowBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedBelowBy (f i) k) :
    QueryBoundedBelowBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtLeast_fin_mOfFn h


-- @@ L698-701 verbatim
/-- Pathwise exact cost for a unit-cost `AddWriterT` computation: every reachable execution
carries exactly `n` unit queries. -/
def QueryCostExactly (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostEqOnSupport oa n


-- @@ L703-705 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma QueryCostExactly.toAbove {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedAboveBy oa n := h.atMost


-- @@ L707-709 verbatim
omit [Monad m] [LawfulMonadLiftT m SetM] in
lemma QueryCostExactly.toBelow {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedBelowBy oa n := h.atLeast


-- @@ L711-713 verbatim
lemma queryCostExactly_pure [LawfulMonad m] (x : α) :
    QueryCostExactly (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_pure (m := m) (ω := ℕ) x


-- @@ L715-717 verbatim
lemma queryCostExactly_monadLift [LawfulMonad m] (x : m α) :
    QueryCostExactly (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_monadLift (m := m) (ω := ℕ) x


-- @@ L719-721 verbatim
lemma queryCostExactly_addTell [LawfulMonad m] (w : ℕ) :
    QueryCostExactly (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostEqOnSupport_addTell (m := m) w


-- @@ L723-726 verbatim
lemma queryCostExactly_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ}
    (f : α → β) (h : QueryCostExactly oa n) :
    QueryCostExactly (f <$> oa) n :=
  pathwiseCostEqOnSupport_map f h


-- @@ L728-732 verbatim
lemma queryCostExactly_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryCostExactly oa n₁) (h₂ : ∀ a, QueryCostExactly (f a) n₂) :
    QueryCostExactly (oa >>= f) (n₁ + n₂) :=
  pathwiseCostEqOnSupport_bind h₁ h₂


-- @@ L734-738 verbatim
lemma queryCostExactly_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryCostExactly (f i) k) :
    QueryCostExactly (Fin.mOfFn n f) (n * k) :=
  ⟨queryBoundedAboveBy_fin_mOfFn (fun i ↦ (h i).toAbove),
    queryBoundedBelowBy_fin_mOfFn (fun i ↦ (h i).toBelow)⟩


-- @@ L740-740 verbatim
end unitCostBounds


-- @@ L742-742 verbatim
section expectedUnitCost


-- @@ L744-745 verbatim
variable [MonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]


-- @@ L747-753 verbatim
lemma expectedCostNat_le_of_queryBoundedAboveBy [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryBoundedAboveBy oa n) :
    expectedCostNat oa ≤ n := by
  simpa using
    (expectedCost_le_of_pathwiseCostAtMost
      (oa := oa) (w := n) (val := fun k ↦ (k : ENNReal)) h Nat.mono_cast)


-- @@ L755-755 verbatim
end expectedUnitCost


-- @@ L757-757 verbatim
section expectedUnitCostPMF


-- @@ L759-760 verbatim
variable [MonadLiftT m PMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]


-- @@ L762-768 verbatim
lemma le_expectedCostNat_of_queryBoundedBelowBy [LawfulMonad m] [EvalDistCompatible m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryBoundedBelowBy oa n) :
    (n : ENNReal) ≤ expectedCostNat oa := by
  refine le_expectedCost_of_pathwiseCostAtLeast
    (oa := oa) (w := n) (val := fun k ↦ (k : ENNReal)) h Nat.mono_cast
    (probFailure_of_liftM_PMF _)


-- @@ L770-776 verbatim
lemma expectedCostNat_eq_of_queryCostExactly [LawfulMonad m] [EvalDistCompatible m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) :
    expectedCostNat oa = n :=
  le_antisymm
    (expectedCostNat_le_of_queryBoundedAboveBy h.toAbove)
    (le_expectedCostNat_of_queryBoundedBelowBy h.toBelow)


-- @@ L778-778 verbatim
end expectedUnitCostPMF


-- @@ L780-780 verbatim
end AddWriterT
