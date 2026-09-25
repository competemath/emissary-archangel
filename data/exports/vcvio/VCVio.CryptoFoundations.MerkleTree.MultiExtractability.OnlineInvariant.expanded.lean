/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.ExtractionKernel
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Evolution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Targets


-- @@ L13-21 verbatim
/-!
# Online Stability Invariant for Stateful Merkle Extraction

The predictable-target stopping theorem needs a semantic good-state invariant. `StableAt` says
that every immutable checkpoint still extracts the same partial tree at the current cumulative
log. It is true initially, is preserved by re-querying a cached entry, and is preserved by a fresh
response outside the live target union computed before that response was sampled. At a phase
boundary, recording the newly emitted root establishes stability for the new checkpoint as well.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace MerkleTreeMultiExtractability


-- @@ L27-27 verbatim
open BinaryTree


-- @@ L29-29 verbatim
variable {Cfg Query Address Y : Type}


-- @@ L31-40 verbatim
/-- Every recorded checkpoint extraction agrees with re-extraction at `log`. -/
def ExtractorState.StableAt [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (log : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  ∀ tag checkpoint, ⟨tag, checkpoint⟩ ∈ state.checkpoints →
    checkpoint.extractedTree view =
      MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
        log checkpoint.root


-- @@ L42-49 verbatim
/-- The empty checkpoint history is stable at every log. -/
theorem ExtractorState.stableAt_empty [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    (config : Configuration Cfg Address)
    (log : MerkleTreeExtractor.QueryLog Query Y) :
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).StableAt view log := by
  intro tag checkpoint hcheckpoint
  simp at hcheckpoint


-- @@ L51-65 verbatim
/-- A cached log append preserves stability because the exact entry already appeared in the log. -/
theorem ExtractorState.StableAt.append_cached
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (query : Query) (response : Y)
    (hmem : (⟨query, response⟩ : (_query : Query) × Y) ∈ log) :
    state.StableAt view (log ++ [⟨query, response⟩]) := by
  intro tag checkpoint hcheckpoint
  rw [hstable tag checkpoint hcheckpoint]
  exact (tree_append_singleton_eq_of_mem view (config.skeleton tag)
    (config.addressKey tag) log checkpoint.root ⟨query, response⟩ hmem).symm


-- @@ L67-88 verbatim
/-- A fresh response outside the pre-sample live target union cannot change any recorded
checkpoint extraction. -/
theorem ExtractorState.StableAt.append_of_not_mem_liveTargetSet
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (query : Query) (response : Y)
    (hresponse : response ∉ state.liveTargetSet view log) :
    state.StableAt view (log ++ [⟨query, response⟩]) := by
  intro tag checkpoint hcheckpoint
  rw [hstable tag checkpoint hcheckpoint]
  apply not_ne_iff.mp
  intro hchanged
  apply hresponse
  simp only [ExtractorState.liveTargetSet, List.mem_toFinset,
    ExtractorState.liveTargetList, List.mem_flatMap]
  refine ⟨⟨tag, checkpoint⟩, hcheckpoint, ?_⟩
  exact tree_ne_append_singleton_implies_response_mem_targets view
    (config.skeleton tag) (config.addressKey tag) log checkpoint.root query response hchanged


-- @@ L90-117 verbatim
/-- At a stable log, the dynamically re-extracted live target union is exactly the immutable
checkpoint target union.  Thus harmless log growth cannot silently enlarge the set against which
the next response is tested. -/
theorem ExtractorState.StableAt.liveTargetSet_eq_targetSet
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log) :
    state.liveTargetSet view log = state.targetSet view := by
  ext target
  simp only [ExtractorState.liveTargetSet, ExtractorState.targetSet, List.mem_toFinset,
    ExtractorState.liveTargetList, ExtractorState.targetList, targetsOfCheckpoints,
    List.mem_flatMap]
  constructor
  · rintro ⟨⟨tag, checkpoint⟩, hcheckpoint, htarget⟩
    refine ⟨⟨tag, checkpoint⟩, hcheckpoint, ?_⟩
    have heq := MerkleTreeExtractor.targets_eq_of_tree_eq view (config.skeleton tag)
      (config.addressKey tag) checkpoint.cumulativeLog log checkpoint.root checkpoint.root
      (hstable tag checkpoint hcheckpoint)
    simpa [Checkpoint.targets] using heq ▸ htarget
  · rintro ⟨⟨tag, checkpoint⟩, hcheckpoint, htarget⟩
    refine ⟨⟨tag, checkpoint⟩, hcheckpoint, ?_⟩
    have heq := MerkleTreeExtractor.targets_eq_of_tree_eq view (config.skeleton tag)
      (config.addressKey tag) checkpoint.cumulativeLog log checkpoint.root checkpoint.root
      (hstable tag checkpoint hcheckpoint)
    simpa [Checkpoint.targets] using heq.symm ▸ htarget


-- @@ L119-131 verbatim
/-- Fixed-set form of the one-entry stability rule. -/
theorem ExtractorState.StableAt.append_of_not_mem_targetSet
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (query : Query) (response : Y)
    (hresponse : response ∉ state.targetSet view) :
    state.StableAt view (log ++ [⟨query, response⟩]) := by
  apply hstable.append_of_not_mem_liveTargetSet view query response
  rwa [hstable.liveTargetSet_eq_targetSet view]


-- @@ L133-153 verbatim
/-- Appending a whole suffix preserves stability when every response avoids the immutable target
set of the recorded checkpoints. -/
theorem ExtractorState.StableAt.append_of_forall_not_mem_targetSet
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (suffix : MerkleTreeExtractor.QueryLog Query Y)
    (havoid : ∀ entry ∈ suffix, entry.2 ∉ state.targetSet view) :
    state.StableAt view (log ++ suffix) := by
  induction suffix generalizing log with
  | nil => simpa using hstable
  | cons entry suffix ih =>
      have hhead : entry.2 ∉ state.targetSet view := havoid entry (by simp)
      have hstable' := hstable.append_of_not_mem_targetSet view entry.1 entry.2 hhead
      have htail : ∀ tailEntry ∈ suffix, tailEntry.2 ∉ state.targetSet view := by
        intro tailEntry hmem
        exact havoid tailEntry (by simp [hmem])
      simpa [List.append_assoc] using ih hstable' htail


-- @@ L155-169 verbatim
/-- If a suffix destroys checkpoint stability, some response in that suffix belongs to the
target set fixed at the beginning of the suffix. -/
theorem ExtractorState.StableAt.exists_target_of_not_stable_append
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log)
    (suffix : MerkleTreeExtractor.QueryLog Query Y)
    (hnotStable : ¬ state.StableAt view (log ++ suffix)) :
    ∃ entry ∈ suffix, entry.2 ∈ state.targetSet view := by
  by_contra hnone
  push Not at hnone
  exact hnotStable (hstable.append_of_forall_not_mem_targetSet view suffix hnone)


-- @@ L171-223 expanded
/-- If a suffix adds no fresh value from the fixed target set, it preserves stability.  Target-
valued cache hits are harmless because the exact query/response entry was already present in the
initial log; non-target misses use the causal one-entry rule. -/
theorem ExtractorState.StableAt.append_of_no_freshTarget [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y) {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config} {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log) (suffix : MerkleTreeExtractor.QueryLog Query Y)
    (initialCache finalCache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
    (hcacheLog :
      ∀ input value,
        initialCache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hmono : initialCache ≤ finalCache)
    (hsuffixFinal : ∀ entry ∈ suffix, finalCache entry.1 = some entry.2)
    (hnoFresh :
      ∀ target ∈ state.targetSet view,
        ¬MerkleTreeExtractability.CacheAddsValue initialCache finalCache target) :
    state.StableAt view (log ++ suffix) := by
  induction suffix generalizing log with
  | nil => simpa using hstable
  | cons entry suffix
    ih =>
    have hfinal : finalCache entry.1 = some entry.2 := hsuffixFinal entry (by simp)
    have hstable' : state.StableAt view (log ++ [entry]) := by
      cases hinitial : initialCache entry.1 with
      | none =>
        apply hstable.append_of_not_mem_targetSet view entry.1 entry.2
        intro htarget
        exact hnoFresh entry.2 htarget ⟨entry.1, hfinal, hinitial⟩
      | some value =>
        have hvalueFinal := hmono hinitial
        rw [hfinal] at hvalueFinal
        obtain rfl := Option.some.inj hvalueFinal
        obtain ⟨cachedEntry, hcachedEntry, hquery, hvalue⟩ := hcacheLog entry.1 entry.2 hinitial
        have hentryEq : cachedEntry = entry :=
          by
          rcases cachedEntry with ⟨cachedQuery, cachedValue⟩
          rw [Sigma.ext_iff]
          exact ⟨hquery, heq_of_eq hvalue⟩
        subst cachedEntry
        exact hstable.append_cached view entry.1 entry.2 hcachedEntry
    have hsuffixFinal' : ∀ tailEntry ∈ suffix, finalCache tailEntry.1 = some tailEntry.2 :=
      by
      intro tailEntry hmem
      exact hsuffixFinal tailEntry (by simp [hmem])
    have hcacheLog' :
      ∀ input value,
        initialCache input = some value →
          ∃ cachedEntry ∈ log ++ [entry], cachedEntry.1 = input ∧ cachedEntry.2 = value :=
      by
      intro input value hcached
      obtain ⟨cachedEntry, hmem, hquery, hvalue⟩ := hcacheLog input value hcached
      exact ⟨cachedEntry, List.mem_append_left _ hmem, hquery, hvalue⟩
    simpa [List.append_assoc] using ih hstable' hcacheLog' hsuffixFinal'


-- @@ L225-247 expanded
/-- Terminal destabilization yields a target value added under a key absent from the initial
cache.  This is the deterministic fixed-target form consumed by the terminal ROM theorem. -/
theorem ExtractorState.StableAt.exists_freshTarget_of_not_stable_append [DecidableEq Address]
    [DecidableEq Y] (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y} (hstable : state.StableAt view log)
    (suffix : MerkleTreeExtractor.QueryLog Query Y)
    (initialCache finalCache : (OracleSpec.ofFn (ι := Query) (fun _ => Y)).QueryCache)
    (hcacheLog :
      ∀ input value,
        initialCache input = some value → ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hmono : initialCache ≤ finalCache)
    (hsuffixFinal : ∀ entry ∈ suffix, finalCache entry.1 = some entry.2)
    (hnotStable : ¬state.StableAt view (log ++ suffix)) :
    ∃ target ∈ state.targetSet view,
      MerkleTreeExtractability.CacheAddsValue initialCache finalCache target :=
  by
  by_contra hnone
  push Not at hnone
  exact
    hnotStable
      (hstable.append_of_no_freshTarget view suffix initialCache finalCache hcacheLog hmono
        hsuffixFinal hnone)


-- @@ L249-266 verbatim
/-- Recording a root at a stable phase boundary preserves all old equalities and makes the new
checkpoint stable by construction. -/
theorem ExtractorState.StableAt.record
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (hstable : state.StableAt view (state.cumulativeLog ++ phaseLog)) :
    (state.record tag phaseLog root).StableAt view
      (state.cumulativeLog ++ phaseLog) := by
  intro recordedTag checkpoint hcheckpoint
  rw [ExtractorState.record_checkpoints] at hcheckpoint
  rcases List.mem_append.mp hcheckpoint with hold | hnew
  · exact hstable recordedTag checkpoint hold
  · simp only [List.mem_singleton] at hnew
    cases hnew
    rfl


-- @@ L268-283 verbatim
/-- Proof-facing cumulative-log form of `StableAt.record`. -/
theorem ExtractorState.StableAt.recordCumulative
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (tag : Cfg) (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    (hstable : state.StableAt view cumulativeLog) :
    (state.recordCumulative tag cumulativeLog root).StableAt view cumulativeLog := by
  intro recordedTag checkpoint hcheckpoint
  rw [ExtractorState.recordCumulative_checkpoints] at hcheckpoint
  rcases List.mem_append.mp hcheckpoint with hold | hnew
  · exact hstable recordedTag checkpoint hold
  · simp only [List.mem_singleton] at hnew
    cases hnew
    rfl


-- @@ L285-295 verbatim
/-- Stability rules out the checkpoint-versus-terminal branch at the same log. -/
theorem ExtractorState.StableAt.not_hasCheckpointTerminalExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view (state.terminalLog terminalSuffix)) :
    ¬ HasCheckpointTerminalExtractionDisagreement view state terminalSuffix := by
  rintro ⟨tag, checkpoint, hcheckpoint, hdisagreement⟩
  exact hdisagreement (hstable tag checkpoint hcheckpoint)


-- @@ L297-309 verbatim
/-- At a common stable log, two checkpoints with the same configuration and root necessarily
extract the same tree. -/
theorem ExtractorState.StableAt.not_hasEqualRootExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    {log : MerkleTreeExtractor.QueryLog Query Y}
    (hstable : state.StableAt view log) :
    ¬ HasEqualRootExtractionDisagreement view state := by
  rintro ⟨tag, left, right, hleft, hright, hroot, hne⟩
  apply hne
  rw [hstable tag left hleft, hstable tag right hright, hroot]


-- @@ L311-328 verbatim
/-- Under terminal stability, the strongest three-branch event reduces exactly to accepted-opening
disagreement. This is stronger than the public two-branch reduction: equal-root inconsistency is
also impossible at one common stable log. -/
theorem failure_iff_hasAcceptedOpeningDisagreement_of_stableAt
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view (state.terminalLog terminalSuffix)) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix ↔
      HasAcceptedOpeningDisagreement view state attempts := by
  simp only [AnyCheckpointExtractionDisagreement]
  have hnoEqual := hstable.not_hasEqualRootExtractionDisagreement view
  have hnoTerminal :=
    hstable.not_hasCheckpointTerminalExtractionDisagreement view terminalSuffix
  tauto


-- @@ L330-343 verbatim
/-- The textbook two-branch event has the same accepted-opening normal form under stability. -/
theorem textbookFailure_iff_hasAcceptedOpeningDisagreement_of_stableAt
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : state.StableAt view terminalLog) :
    OpeningOrEqualRootDisagreement view state attempts ↔
      HasAcceptedOpeningDisagreement view state attempts := by
  simp only [OpeningOrEqualRootDisagreement]
  have hnoEqual := hstable.not_hasEqualRootExtractionDisagreement view
  tauto


-- @@ L345-345 verbatim
end MerkleTreeMultiExtractability
