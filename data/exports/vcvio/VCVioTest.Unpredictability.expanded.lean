/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Unpredictability
public import VCVio.OracleComp.QueryTracking.AdaptivePrefix


-- @@ L12-18 verbatim
/-!
# ROM Unpredictability Canaries

These examples pin the finite-target random-oracle bound, including its use of the number of
distinct target values rather than the number of positions from which those values were collected.
They also exercise the bound in a strictly nonzero universe.
-/


-- @@ L20-20 verbatim
public section


-- @@ L22-22 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L24-24 verbatim
namespace VCVioTest.Unpredictability


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
section UniversePolymorphism


-- @@ L30-31 verbatim
variable {ι : Type (u + 1)} [DecidableEq ι] [Inhabited ι]
  {spec : OracleSpec.{u + 1, u + 1} ι} [spec.DecidableEq] [IsUniformSpec spec]


-- @@ L33-64 expanded
/-- The finite-target bound applies to a genuine fresh query when the oracle's indices,
responses, and computation result live in an arbitrary nonzero universe. The singleton target
is reachable by the query at `default`, so this is not merely an elaboration-only `#check`. -/
example (v₀ : spec.Range default)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    (0 <
        probEvent
          ((simulateQ cachingOracle
                (liftM (spec.query default) : OracleComp spec (spec.Range default))).run
            ∅)
          fun z =>
          ∃ target ∈ ({ v₀ } : Finset (spec.Range default)),
            ∃ t₀ : spec.Domain,
              ∃ v : spec.Range t₀,
                z.2 t₀ = some v ∧ (∅ : QueryCache spec) t₀ = none ∧ HEq v target) ∧
      (probEvent
          ((simulateQ cachingOracle
                (liftM (spec.query default) : OracleComp spec (spec.Range default))).run
            ∅)
          fun z =>
          ∃ target ∈ ({ v₀ } : Finset (spec.Range default)),
            ∃ t₀ : spec.Domain,
              ∃ v : spec.Range t₀,
                z.2 t₀ = some v ∧ (∅ : QueryCache spec) t₀ = none ∧ HEq v target) ≤
        ((({ v₀ } : Finset (spec.Range default)).card * 1 : ℕ) : ℝ≥0∞) *
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  by
  constructor
  · rw [probEvent_pos_iff]
    refine ⟨(v₀, (∅ : QueryCache spec).cacheQuery default v₀), ?_, ?_⟩
    · simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [cachingOracle.run_none (by simp), support_map]
      exact ⟨v₀, by simp, rfl⟩
    · exact ⟨v₀, by simp, default, v₀, by simp, by simp, HEq.rfl⟩
  · apply probEvent_cache_hits_targets_le_of_noCollision
    · rw [← bind_pure (liftM (spec.query default) : OracleComp spec (spec.Range default)),
        isTotalQueryBound_query_bind_iff]
      exact ⟨Nat.one_pos, fun _ ↦ trivial⟩
    · exact hrange
    · rintro ⟨t₀, t₁, w₀, w₁, _, hcache, _, _⟩
      simp at hcache


-- @@ L66-66 verbatim
end UniversePolymorphism


-- @@ L68-68 expanded
abbrev TestSpec : OracleSpec Bool :=
  OracleSpec.ofFn (ι := Bool) (fun _ => Fin 4)


-- @@ L70-71 verbatim
noncomputable instance : IsUniformSpec TestSpec :=
  IsUniformSpec.ofFintypeInhabited TestSpec


-- @@ L73-75 verbatim
def oneQuery : OracleComp TestSpec Unit := do
  let _ ← (TestSpec.query false : OracleComp TestSpec (Fin 4))
  return ()


-- @@ L77-79 verbatim
private lemma oneQuery_totalBound : IsTotalQueryBound oneQuery 1 := by
  rw [oneQuery, isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩


-- @@ L81-81 verbatim
def twoTargets : Finset (Fin 4) := {0, 1}


-- @@ L83-84 verbatim
@[simp] lemma twoTargets_card : twoTargets.card = 2 := by
  decide


-- @@ L86-98 expanded
/-- A single fresh query hitting either of two distinct outputs receives the expected
`2 / 4` upper bound. This rejects accidentally dropping the target-cardinality factor. -/
example :
    (probEvent ((simulateQ TestSpec.cachingOracle oneQuery).run ∅) fun z =>
        ∃ v₀ ∈ twoTargets,
          ∃ t₀ : TestSpec.Domain,
            ∃ v : TestSpec.Range t₀,
              z.2 t₀ = some v ∧ (∅ : QueryCache TestSpec) t₀ = none ∧ HEq v v₀) ≤
      (2 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ :=
  by
  simpa [twoTargets] using
    (probEvent_cache_hits_targets_le_of_noCollision (oa := oneQuery) (n := 1) oneQuery_totalBound
      (by intro t; cases t <;> exact le_rfl) twoTargets (∅ : QueryCache TestSpec)
      (by
        intro ⟨_, _, _, _, _, hcache, _, _⟩
        simp at hcache))


-- @@ L100-101 verbatim
def initialCache : QueryCache TestSpec :=
  (∅ : QueryCache TestSpec).cacheQuery true 0


-- @@ L103-116 expanded
/-- The unique-preimage theorem permits a target value to occur once in the initial cache and
still bounds a fresh second preimage. This rejects silently strengthening freshness to require
that no target value was present before the residual phase. -/
example :
    (probEvent ((simulateQ TestSpec.cachingOracle oneQuery).run initialCache) fun z =>
        ∃ v₀ ∈ twoTargets,
          ∃ t₀ : TestSpec.Domain,
            ∃ v : TestSpec.Range t₀, z.2 t₀ = some v ∧ initialCache t₀ = none ∧ HEq v v₀) ≤
      (2 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ :=
  by
  simpa [twoTargets] using
    (probEvent_cache_hits_targets_le_of_unique_preimage (oa := oneQuery) (n := 1)
      oneQuery_totalBound (by intro t; cases t <;> exact le_rfl) twoTargets initialCache
      (by
        intro _ _ t₀ t₁ v₁ v₂ hcache₀ hcache₁ _ _
        cases t₀ <;> cases t₁ <;> simp [initialCache] at hcache₀ hcache₁ ⊢))


-- @@ L118-120 verbatim
/-- Deduplicating positional labels records two semantic target values, not three positions. -/
example : ({0, 1, 0} : Finset (Fin 4)).card = 2 := by
  decide


-- @@ L122-122 verbatim
/-! ## Adaptive-prefix cache hit accounting -/


-- @@ L124-124 verbatim
namespace AdaptivePrefixCanary


-- @@ L126-126 expanded
abbrev PrefixSpec : OracleSpec Bool :=
  OracleSpec.ofFn (ι := Bool) (fun _ => Bool)


-- @@ L128-132 verbatim
/-- The syntactic prefix asks the same query twice. -/
def repeatedPrefix : OracleComp PrefixSpec Unit := do
  let _ ← (PrefixSpec.query false : OracleComp PrefixSpec Bool)
  let _ ← (PrefixSpec.query false : OracleComp PrefixSpec Bool)
  return ()


-- @@ L134-139 verbatim
/-- Repeated cached queries still consume the total syntactic query budget. -/
example : IsTotalQueryBound repeatedPrefix 2 := by
  rw [repeatedPrefix, isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => trivial⟩


-- @@ L141-148 verbatim
/-- The bound is sharp: deleting the second syntactic query would make this false. -/
example : ¬ IsTotalQueryBound repeatedPrefix 1 := by
  rw [repeatedPrefix, isTotalQueryBound_query_bind_iff]
  simp only [Nat.lt_add_one_iff, nonpos_iff_eq_zero, true_and]
  intro h
  have hsecond := h false
  rw [isTotalQueryBound_query_bind_iff] at hsecond
  omega


-- @@ L150-153 verbatim
/-- The suffix exposes the complete prefix log; it does not issue another oracle query. -/
def returnLog (_ : Unit) (log : PrefixSpec.QueryLog) :
    OracleComp PrefixSpec PrefixSpec.QueryLog :=
  pure log


-- @@ L155-156 verbatim
def onceCached (answer : Bool) : PrefixSpec.QueryCache :=
  (∅ : PrefixSpec.QueryCache).cacheQuery false answer


-- @@ L158-159 verbatim
def cachedKeyCount (cache : PrefixSpec.QueryCache) : Nat :=
  (Finset.univ.filter fun input => (cache input).isSome).card


-- @@ L161-163 verbatim
@[simp] lemma cachedKeyCount_onceCached (answer : Bool) :
    cachedKeyCount (onceCached answer) = 1 := by
  cases answer <;> decide


-- @@ L165-173 verbatim
/-- For either miss response, the first query populates one key and the repeated query is a hit:
the log has length two, while the final cache is exactly the once-populated cache. This catches
both accidentally charging only cache misses to the total query budget and accidentally growing
the cache on a hit. -/
example (answer : Bool) :
    ([⟨false, answer⟩, ⟨false, answer⟩], onceCached answer) ∈ support
      (adaptivePrefixRunFrom returnLog repeatedPrefix
        (∅ : PrefixSpec.QueryCache) ([] : PrefixSpec.QueryLog)) := by
  simp [adaptivePrefixRunFrom, repeatedPrefix, returnLog, onceCached]


-- @@ L175-179 verbatim
/-- The miss/hit branches are distinguishable at another input: the populated cache contains
exactly the queried key and leaves the other Boolean key fresh. -/
example (answer : Bool) :
    (onceCached answer) false = some answer ∧ (onceCached answer) true = none := by
  simp [onceCached, QueryCache.cacheQuery_of_ne]


-- @@ L181-189 verbatim
/-- A nonempty input transcript is preserved, and two hits on a preloaded key neither overwrite
the cache nor disturb the earlier entry. -/
example (falseAnswer trueAnswer : Bool) :
    let cache := (onceCached falseAnswer).cacheQuery true trueAnswer
    let log : PrefixSpec.QueryLog := [⟨true, trueAnswer⟩]
    (log ++ [⟨false, falseAnswer⟩, ⟨false, falseAnswer⟩], cache) ∈ support
      (adaptivePrefixRunFrom returnLog repeatedPrefix cache log) := by
  simp [adaptivePrefixRunFrom, repeatedPrefix, returnLog, onceCached,
    QueryCache.cacheQuery_of_ne]


-- @@ L191-191 verbatim
end AdaptivePrefixCanary


-- @@ L193-193 verbatim
end VCVioTest.Unpredictability
