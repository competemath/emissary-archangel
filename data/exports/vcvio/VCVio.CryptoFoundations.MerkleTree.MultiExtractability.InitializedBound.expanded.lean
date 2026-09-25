/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.SequentialBound


-- @@ L11-17 verbatim
/-!
# Initialized Sequential Merkle Bounds

This module initializes the stateful stopping theorem at the empty cache, log, and extractor
history. The finite-maximum numerator is obtained from a single bound on the complete adversarial
execution.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open OracleSpec OracleComp


-- @@ L23-23 verbatim
namespace MerkleTreeMultiExtractability


-- @@ L25-25 verbatim
variable {Cfg Query Address Y R C : Type}


-- @@ L27-34 expanded
/-- Run a fixed commitment prefix from the canonical private and extractor states, then execute
the terminal computation supplied by the caller. -/
def SequentialCommitter.runFromEmptyThen (committer : SequentialCommitter Cfg Query Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (finish :
      committer.State →
        ExtractorState Cfg Query Address Y config →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R) :
    OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R :=
  committer.runCommitmentsThen rounds 0 committer.initialState ExtractorState.empty finish


-- @@ L36-99 expanded
/-- Empty-state specialization of the global-budget sequential theorem.

The single hypothesis at `queryBound` accounts for every commitment phase and the final
log-dependent accounting computation. The executable runner still ends in the independent
`finish`, and the empty initial cache turns the safe potential into the finite-max numerator. -/
theorem SequentialCommitter.probEvent_runFromEmptyThen_logged_le [DecidableEq Query]
    [DecidableEq Address] [DecidableEq Y] [Finite Y] [Inhabited Y]
    [IsUniformSpec (OracleSpec.ofFn (ι := Query) (fun _ => Y))]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y) (config : Configuration Cfg Address)
    (finish :
      committer.State →
        ExtractorState Cfg Query Address Y config →
          OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) R)
    (accountingFinish :
      committer.State →
        ExtractorState Cfg Query Address Y config →
          (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog →
            OracleComp (OracleSpec.ofFn (ι := Query) (fun _ => Y)) C)
    (win : R → Prop) (nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hfinish :
      ∀ privateState (state : ExtractorState Cfg Query Address Y config)
        (terminalRemaining terminalCached : ℕ)
        (cache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
        (log : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryLog),
        IsTotalQueryBound (accountingFinish privateState state log) terminalRemaining →
          state.cumulativeLog = log →
            ¬CacheHasCollision cache →
              (∃ keys : Finset Query,
                  keys.card ≤ terminalCached ∧ ∀ input, cache input ≠ none → input ∈ keys) →
                (∀ entry ∈ log, cache entry.1 = some entry.2) →
                  (∀ input value,
                      cache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
                    state.StableAt view log →
                      state.totalNodeBudget ≤ nodeBudget →
                        state.checkpoints.length ≤ checkpointCount →
                          (probEvent
                              ((simulateQ (OracleSpec.ofFn (ι := Query) (fun _ => Y)).cachingOracle
                                    (finish privateState state)).run
                                cache)
                              fun z => win z.1) ≤
                            (multiCheckpointErrorNumerator nodeBudget checkpointCount
                                  verifierOverhead terminalRemaining terminalCached :
                                ENNReal) *
                              (Nat.card Y : ENNReal)⁻¹)
    (rounds queryBound : ℕ)
    (hbound :
      IsTotalQueryBound
        (committer.runCommitmentsThenAccounting accountingFinish rounds 0 committer.initialState
          (ExtractorState.empty : ExtractorState Cfg Query Address Y config) [])
        queryBound)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget) (hcheckpoints : rounds ≤ checkpointCount) :
    (probEvent
        ((simulateQ (OracleSpec.ofFn (ι := Query) (fun _ => Y)).cachingOracle
              (committer.runFromEmptyThen config rounds finish)).run
          ∅)
        fun z => win z.1) ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead queryBound :
          ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ :=
  by
  have hraw :=
    committer.probEvent_runCommitmentsThen_logged_le view finish accountingFinish win nodeBudget
      checkpointCount verifierOverhead perCheckpoint hconfig hfinish rounds 0 committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
      (∅ : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache) [] queryBound 0 hbound rfl
      (by
        rintro ⟨_, _, _, _, _, hcached, _, _⟩
        simp at hcached)
      ⟨∅, by simp, fun input hinput => (hinput (by simp)).elim⟩ (by simp) (by simp)
      (ExtractorState.stableAt_empty view config [])
      (by simpa [ExtractorState.totalNodeBudget, nodeBudgetOfCheckpoints] using hnodes)
      (by simpa using hcheckpoints)
  simpa [SequentialCommitter.runFromEmptyThen, multiCheckpointROMErrorNumerator] using hraw


-- @@ L101-101 verbatim
end MerkleTreeMultiExtractability
