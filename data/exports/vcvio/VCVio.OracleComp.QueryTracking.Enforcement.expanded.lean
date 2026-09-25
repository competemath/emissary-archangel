/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound


-- @@ L10-25 verbatim
/-!
# Enforcement Oracle

Oracle wrapper that enforces a query budget by silently dropping queries beyond
the budget. This implements EasyCrypt's `Enforce`/`Bounder` pattern.

## Main Definitions

- `enforceOracle`: Oracle that tracks remaining budget via `StateT` and returns
  `default` for queries exceeding the budget.

## Main Results

- `enforceOracle.fst_map_run_simulateQ`: Enforcement is transparent for computations
  within their query bound.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open OracleSpec OracleComp


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L35-35 verbatim
variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}


-- @@ L37-46 expanded
/-- Enforcement oracle: wraps the original oracle with a per-index budget tracked via `StateT`.
When the remaining budget for the queried oracle is positive, the query is forwarded and
the budget decremented. When the budget is exhausted, `default` is returned silently. -/
def OracleSpec.enforceOracle [DecidableEq ι] [spec.Inhabited] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec)) := fun t =>
  StateT.mk fun budget =>
    if 0 < budget t then (·, Function.update budget t (budget t - 1)) <$> liftM (OracleSpec.query t)
    else pure (default, budget)


-- @@ L48-48 verbatim
namespace enforceOracle


-- @@ L50-50 verbatim
variable [DecidableEq ι] [IsUniformSpec spec]


-- @@ L52-58 expanded
@[simp]
lemma run_apply (t : ι) (budget : ι → ℕ) :
    (spec.enforceOracle t).run budget =
      if 0 < budget t then
        (·, Function.update budget t (budget t - 1)) <$> liftM (OracleSpec.query t)
      else pure (default, budget) :=
  rfl


-- @@ L60-76 expanded
/-- When the computation is within its query bound, enforcement is transparent:
the output distribution is identical to running without enforcement. -/
theorem fst_map_run_simulateQ {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) : Prod.fst <$> (simulateQ enforceOracle oa).run qb = oa := by
  induction oa using OracleComp.inductionOn generalizing qb with
  | pure _ => simp
  | query_bind t mx ih =>
    rw [isPerIndexQueryBound_query_bind_iff] at h
    obtain ⟨hpos, hcont⟩ := h
    simp only [simulateQ_query_bind]
    change
      Prod.fst <$>
          ((spec.enforceOracle t).run qb >>= fun p => (simulateQ enforceOracle (mx p.1)).run p.2) =
        liftM (OracleSpec.query t) >>= mx
    rw [run_apply, if_pos hpos]
    simp only [monad_norm, Function.comp]
    exact bind_congr fun u => by simpa only [map_eq_bind_pure_comp] using ih u (hcont u)


-- @@ L78-78 verbatim
section Probability


-- @@ L80-96 expanded
/-- For a computation that is structurally within budget, the budget check in the
counting semantics is redundant on the support. -/
theorem probEvent_counting_budget_eq {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    (probEvent (countingOracle.simulate oa 0) fun z => p z.1 ∧ z.2 ≤ qb) = probEvent oa p := by
  calc
    (probEvent (countingOracle.simulate oa 0) fun z => p z.1 ∧ z.2 ≤ qb) =
        probEvent (countingOracle.simulate oa 0) fun z => p z.1 :=
      by
      refine
        probEvent_congr' (oa := countingOracle.simulate oa 0) (oa' := countingOracle.simulate oa 0)
          ?_ rfl
      exact fun z hz => and_iff_left (h.counting_bounded hz)
    _ = probEvent oa p := by
      rw [countingOracle.simulate]
      simp only [zero_add]
      rw [show (Prod.map id fun x : QueryCount ι => x) = id from rfl, id_map,
        show (fun z : α × QueryCount ι => p z.1) = p ∘ Prod.fst from rfl, ← probEvent_map,
        countingOracle.fst_map_run_simulateQ]


-- @@ L98-106 expanded
/-- Penalty characterization under a structural query bound: the probability of an
event together with staying within budget under counting equals the event probability
under enforcement. -/
theorem probEvent_counting_budget_eq_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    (probEvent (countingOracle.simulate oa 0) fun z => p z.1 ∧ z.2 ≤ qb) =
      probEvent (Prod.fst <$> (simulateQ enforceOracle oa).run qb) p :=
  by
  rw [fst_map_run_simulateQ h]
  exact probEvent_counting_budget_eq h p


-- @@ L108-114 expanded
/-- EasyCrypt-style penalty inequality, obtained here as an equality under the
structural boundedness hypothesis. -/
theorem probEvent_counting_budget_le_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    (probEvent (countingOracle.simulate oa 0) fun z => p z.1 ∧ z.2 ≤ qb) ≤
      probEvent (Prod.fst <$> (simulateQ enforceOracle oa).run qb) p :=
  by rw [probEvent_counting_budget_eq_enforce h p]


-- @@ L116-116 verbatim
end Probability


-- @@ L118-118 verbatim
end enforceOracle
