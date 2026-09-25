/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineBound
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineInvariant


-- @@ L12-19 verbatim
/-!
# One Stateful Merkle Commitment Phase

This module instantiates the generic predictable-target theorem with the semantic live targets and
stability invariant of an immutable extractor checkpoint state. The terminal hypothesis uses the
same potential at the remaining resource state, so a caller may record the phase output and invoke
the theorem recursively for the next commitment phase.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open OracleSpec OracleComp


-- @@ L25-25 verbatim
namespace MerkleTreeMultiExtractability


-- @@ L27-27 verbatim
variable {Cfg Query Address Y X R C : Type}


-- @@ L29-100 expanded
/-- Log-dependent stateful-phase bound. The proof-only accounting continuation may inspect the
cumulative query log produced by the prefix, while the executable phase remains
`adaptivePrefixRunFrom` with the original suffix. -/
theorem probEvent_stablePhaseRunFrom_logged_le [DecidableEq Query] [DecidableEq Address]
    [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (OracleSpec.ofFn (ι := Query) (fun _ => Y))]
    (view : MerkleTreeExtractor.QueryView Query Address Y) {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (suffix :
      X →
        (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R)
    (continuation :
      X →
        (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) C)
    (win : R → Prop) (nodeBudget checkpointCount overhead : ℕ)
    (prefixComp : OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) X) (remaining cached : ℕ)
    (log : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog)
    (hbound : IsTotalQueryBound (loggedAccountingBind prefixComp log continuation) remaining)
    (cache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
    (hno : ¬CacheHasCollision cache)
    (hcacheBound :
      ∃ keys : Finset Query, keys.card ≤ cached ∧ ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog :
      ∀ input value, cache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log) (hnodeBudget : state.totalNodeBudget ≤ nodeBudget)
    (hcheckpointCount : state.checkpoints.length ≤ checkpointCount)
    (hterminal :
      ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
        (terminalLog : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog),
        IsTotalQueryBound (continuation x terminalLog) terminalRemaining →
          ¬CacheHasCollision terminalCache →
            (∃ keys : Finset Query,
                keys.card ≤ terminalCached ∧ ∀ input, terminalCache input ≠ none → input ∈ keys) →
              (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
                (∀ input value,
                    terminalCache input = some value →
                      ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
                  state.StableAt view terminalLog →
                    (probEvent
                        ((simulateQ (OracleSpec.ofFn (ι := Query) (fun _ => Y)).cachingOracle
                              (suffix x terminalLog)).run
                          terminalCache)
                        fun z => win z.1) ≤
                      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
                            terminalRemaining terminalCached :
                          ENNReal) *
                        (Nat.card Y : ENNReal)⁻¹) :
    (probEvent
        (adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R) suffix prefixComp cache log)
        fun z => win z.1) ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead remaining cached :
          ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  by
  apply
    probEvent_onlineAdaptivePrefixRunFrom_logged_le suffix continuation win
      (state.liveTargetSet view) (fun _ currentLog => state.StableAt view currentLog) nodeBudget
      checkpointCount overhead prefixComp remaining cached log hbound cache hno hcacheBound
      hlogCache hcacheLog hstable
  · intro currentCache currentLog query response hstableCurrent hresponse hcacheLogCurrent
    obtain ⟨⟨entryQuery, entryValue⟩, hentry, hquery, hvalue⟩ :=
      hcacheLogCurrent query response hresponse
    have hentryEq : (⟨entryQuery, entryValue⟩ : (_query : Query) × Y) = ⟨query, response⟩ :=
      by
      rw [Sigma.ext_iff]
      exact ⟨hquery, heq_of_eq hvalue⟩
    rw [← hentryEq]
    exact hstableCurrent.append_cached view entryQuery entryValue hentry
  · intro currentCache currentLog query response hstableCurrent _hnone _hno hresponse
    exact hstableCurrent.append_of_not_mem_liveTargetSet view query response hresponse
  · intro currentCached currentCache currentLog hkeys hlogCacheCurrent _hcacheLogCurrent _
    obtain ⟨keys, hkeysCard, hkeysMem⟩ := hkeys
    apply
      (state.liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover view currentLog
          currentCache keys currentCached hkeysCard
          { log_agrees := fun query response hentry => hlogCacheCurrent ⟨query, response⟩ hentry
            cache_keys := hkeysMem }).trans
    exact sharedExtractedLabelCountBound_mono_budget hnodeBudget hcheckpointCount
  · exact hterminal


-- @@ L102-174 expanded
/-- A stateful phase is bounded by any uniform node/checkpoint envelope containing its immutable
checkpoint state. Using a uniform envelope is the strongest composable form: after a pure phase
boundary records a new checkpoint, the recursive phase can keep the same final resource budget.
The local target-cardinality obligation is discharged by
`liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover`. -/
theorem probEvent_stablePhaseRunFrom_le [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [IsUniformSpec (OracleSpec.ofFn (ι := Query) (fun _ => Y))]
    (view : MerkleTreeExtractor.QueryView Query Address Y) {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (suffix :
      X →
        (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R)
    (continuation : X → OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) C) (win : R → Prop)
    (nodeBudget checkpointCount overhead : ℕ)
    (prefixComp : OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) X) (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
    (log : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog) (hno : ¬CacheHasCollision cache)
    (hcacheBound :
      ∃ keys : Finset Query, keys.card ≤ cached ∧ ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog :
      ∀ input value, cache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log) (hnodeBudget : state.totalNodeBudget ≤ nodeBudget)
    (hcheckpointCount : state.checkpoints.length ≤ checkpointCount)
    (hterminal :
      ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
        (terminalLog : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog),
        IsTotalQueryBound (continuation x) terminalRemaining →
          ¬CacheHasCollision terminalCache →
            (∃ keys : Finset Query,
                keys.card ≤ terminalCached ∧ ∀ input, terminalCache input ≠ none → input ∈ keys) →
              (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
                (∀ input value,
                    terminalCache input = some value →
                      ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
                  state.StableAt view terminalLog →
                    (probEvent
                        ((simulateQ (OracleSpec.ofFn (ι := Query) (fun _ => Y)).cachingOracle
                              (suffix x terminalLog)).run
                          terminalCache)
                        fun z => win z.1) ≤
                      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead
                            terminalRemaining terminalCached :
                          ENNReal) *
                        (Nat.card Y : ENNReal)⁻¹) :
    (probEvent
        (adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R) suffix prefixComp cache log)
        fun z => win z.1) ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount overhead remaining cached :
          ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  by
  apply
    probEvent_onlineAdaptivePrefixRunFrom_le suffix continuation win (state.liveTargetSet view)
      (fun _ currentLog => state.StableAt view currentLog) nodeBudget checkpointCount overhead
      prefixComp remaining cached hbound cache log hno hcacheBound hlogCache hcacheLog hstable
  · intro currentCache currentLog query response hstableCurrent hresponse hcacheLogCurrent
    obtain ⟨⟨entryQuery, entryValue⟩, hentry, hquery, hvalue⟩ :=
      hcacheLogCurrent query response hresponse
    have hentryEq : (⟨entryQuery, entryValue⟩ : (_query : Query) × Y) = ⟨query, response⟩ :=
      by
      rw [Sigma.ext_iff]
      exact ⟨hquery, heq_of_eq hvalue⟩
    rw [← hentryEq]
    exact hstableCurrent.append_cached view entryQuery entryValue hentry
  · intro currentCache currentLog query response hstableCurrent _hnone _hno hresponse
    exact hstableCurrent.append_of_not_mem_liveTargetSet view query response hresponse
  · intro currentCached currentCache currentLog hkeys hlogCacheCurrent _hcacheLogCurrent _
    obtain ⟨keys, hkeysCard, hkeysMem⟩ := hkeys
    apply
      (state.liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover view currentLog
          currentCache keys currentCached hkeysCard
          { log_agrees := fun query response hentry => hlogCacheCurrent ⟨query, response⟩ hentry
            cache_keys := hkeysMem }).trans
    exact sharedExtractedLabelCountBound_mono_budget hnodeBudget hcheckpointCount
  · exact hterminal


-- @@ L176-222 expanded
/-- Exact-state specialization of `probEvent_stablePhaseRunFrom_le`. This is convenient for a
terminal phase that will not record additional checkpoints. -/
theorem probEvent_stablePhaseRunFrom_exact_le [DecidableEq Query] [DecidableEq Address]
    [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (OracleSpec.ofFn (ι := Query) (fun _ => Y))]
    (view : MerkleTreeExtractor.QueryView Query Address Y) {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (suffix :
      X →
        (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R)
    (continuation : X → OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) C) (win : R → Prop)
    (overhead : ℕ) (prefixComp : OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) X)
    (remaining cached : ℕ) (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
    (log : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog) (hno : ¬CacheHasCollision cache)
    (hcacheBound :
      ∃ keys : Finset Query, keys.card ≤ cached ∧ ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog :
      ∀ input value, cache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log)
    (hterminal :
      ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
        (terminalLog : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog),
        IsTotalQueryBound (continuation x) terminalRemaining →
          ¬CacheHasCollision terminalCache →
            (∃ keys : Finset Query,
                keys.card ≤ terminalCached ∧ ∀ input, terminalCache input ≠ none → input ∈ keys) →
              (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
                (∀ input value,
                    terminalCache input = some value →
                      ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
                  state.StableAt view terminalLog →
                    (probEvent
                        ((simulateQ (OracleSpec.ofFn (ι := Query) (fun _ => Y)).cachingOracle
                              (suffix x terminalLog)).run
                          terminalCache)
                        fun z => win z.1) ≤
                      (multiCheckpointErrorNumerator state.totalNodeBudget state.checkpoints.length
                            overhead terminalRemaining terminalCached :
                          ENNReal) *
                        (Nat.card Y : ENNReal)⁻¹) :
    (probEvent
        (adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R) suffix prefixComp cache log)
        fun z => win z.1) ≤
      (multiCheckpointErrorNumerator state.totalNodeBudget state.checkpoints.length overhead
            remaining cached :
          ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  probEvent_stablePhaseRunFrom_le view state suffix continuation win state.totalNodeBudget
    state.checkpoints.length overhead prefixComp remaining cached hbound cache log hno hcacheBound
    hlogCache hcacheLog hstable le_rfl le_rfl hterminal


-- @@ L224-224 verbatim
end MerkleTreeMultiExtractability
