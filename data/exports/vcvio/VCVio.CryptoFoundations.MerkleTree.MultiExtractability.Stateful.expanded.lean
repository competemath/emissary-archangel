/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Extractor
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Batch.Opening


-- @@ L12-42 verbatim
/-!
# Stateful transcript extraction for Merkle batch openings

This module defines the deterministic state carried by a multi-commitment Merkle extractor.
Commitment phases contribute query-log segments to one cumulative transcript.  At each commitment,
the extractor records the cumulative log and the claimed root, tagged by the tree configuration in
force for that commitment.  The extracted partial tree is a pure projection of that immutable
checkpoint through `MerkleTreeExtractor.tree`.

A batch opening uses the intrinsic, path-pruned `InductiveMerkleTree.BatchProof`, packaged
with its dependent selector and selected values.  The package does not carry a separate nonempty
hypothesis: existence of its `proof` field already implies that its selector contains a selected
leaf.

The three failure predicates are deliberately deterministic:

* `AcceptedOpeningDisagreement` says that an accepted claimed opening differs from the canonical
  opening obtained from its commitment checkpoint;
* `EqualRootExtractionDisagreement` says that two checkpoints for the same configuration and root
  yield different partial trees;
* `CheckpointTerminalExtractionDisagreement` says that a checkpoint extraction changes when the
  terminal transcript is used, covering queries made after the final commitment.

`AnyCheckpointExtractionDisagreement` is the disjunction of these three events. This file defines
the deterministic event only; the game and resource-accounting modules provide its probability
bound.

Disagreement events relate an opening or pair of checkpoints only within the same configuration
tag. Reuse of one root across distinct tags is outside the modeled event, even when the tags select
different skeletons or address maps.
-/


-- @@ L44-44 verbatim
@[expose] public section


-- @@ L46-46 verbatim
namespace MerkleTreeMultiExtractability


-- @@ L48-48 verbatim
open BinaryTree InductiveMerkleTree


-- @@ L50-50 verbatim
universe u v w


-- @@ L52-52 verbatim
variable {Cfg : Type u} {Query : Type v} {Address : Type w} {Y Z : Type}

-- @@ L53-53 verbatim
variable {s : Skeleton}


-- @@ L55-55 verbatim
/-! ## Configurations and commitment checkpoints -/


-- @@ L57-66 verbatim
/-- A family of Merkle configurations over a shared query view and response type.

Indexing the shape and address map by `Cfg` makes a tag determine its dependent tree type.  The
structure intentionally contains no oracle-independence assertion; callers must supply any domain
separation required between tags. -/
structure Configuration (Cfg : Type u) (Address : Type w) where
  /-- Shape of commitments made under each configuration tag. -/
  skeleton : Cfg → Skeleton
  /-- Address assigned to every internal position under a configuration tag. -/
  addressKey : (tag : Cfg) → SkeletonInternalIndex (skeleton tag) → Address


-- @@ L68-77 verbatim
/-- Immutable extraction input captured immediately after one commitment phase.

The `config` and `tag` parameters are phantom in the stored `root` and `cumulativeLog` fields, but
they determine the skeleton and address map used by `Checkpoint.extractedTree`. -/
structure Checkpoint (Query : Type v) (Y : Type) (config : Configuration Cfg Address)
    (tag : Cfg) where
  /-- Root emitted by the commitment phase. -/
  root : Y
  /-- Complete cumulative transcript through the end of this commitment phase. -/
  cumulativeLog : MerkleTreeExtractor.QueryLog Query Y


-- @@ L79-86 verbatim
/-- Reconstruct the partial tree recorded by a commitment checkpoint. -/
def Checkpoint.extractedTree [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    FullData (Option Y) (config.skeleton tag) :=
  MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
    checkpoint.cumulativeLog checkpoint.root


-- @@ L88-98 verbatim
/-- Canonical extracted opening for the selector carried by a claimed opening. -/
def Checkpoint.extractedOpening [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag)
    (opening : BatchOpening Y (config.skeleton tag)) :
    BatchOpening (Option Y) (config.skeleton tag) where
  selector := opening.selector
  values := selectedValues (Checkpoint.extractedTree view checkpoint).toLeafData opening.selector
  proof := generateBatchProof (Checkpoint.extractedTree view checkpoint)
    opening.selector opening.anySelected


-- @@ L100-103 verbatim
/-- A checkpoint paired with the configuration that determines its dependent tree shape. -/
abbrev AnyCheckpoint (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) :=
  (tag : Cfg) ×' Checkpoint Query Y config tag


-- @@ L105-114 verbatim
/-- Stateful accumulator for sequential commitment phases.

`cumulativeLog` contains all completed commitment-phase segments.  `checkpoints` retains an
immutable snapshot after every recorded root. -/
structure ExtractorState (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) where
  /-- Transcript accumulated across all recorded commitment phases. -/
  cumulativeLog : MerkleTreeExtractor.QueryLog Query Y
  /-- Configuration-tagged checkpoint history, in commitment order. -/
  checkpoints : List (AnyCheckpoint Cfg Query Address Y config)


-- @@ L116-120 verbatim
/-- Empty state before any commitment phase has run. -/
def ExtractorState.empty {config : Configuration Cfg Address} :
    ExtractorState Cfg Query Address Y config where
  cumulativeLog := []
  checkpoints := []


-- @@ L122-129 verbatim
/-- Append one phase-local query log and record the resulting cumulative checkpoint. -/
def ExtractorState.record {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    ExtractorState Cfg Query Address Y config :=
  let cumulativeLog := state.cumulativeLog ++ phaseLog
  { cumulativeLog
    checkpoints := state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩] }


-- @@ L131-138 verbatim
/-- Record a checkpoint from an already accumulated log. This is the proof-facing form used when
the caching/logging interpreter returns the full current log rather than a phase-local suffix. -/
def ExtractorState.recordCumulative {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    ExtractorState Cfg Query Address Y config where
  cumulativeLog := cumulativeLog
  checkpoints := state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩]


-- @@ L140-146 verbatim
/-- `recordCumulative` agrees with the executable phase-suffix transition. -/
theorem ExtractorState.recordCumulative_append
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    state.recordCumulative tag (state.cumulativeLog ++ phaseLog) root =
      state.record tag phaseLog root := rfl


-- @@ L148-153 verbatim
@[simp]
theorem ExtractorState.recordCumulative_cumulativeLog
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.recordCumulative tag cumulativeLog root).cumulativeLog = cumulativeLog := rfl


-- @@ L155-161 verbatim
@[simp]
theorem ExtractorState.recordCumulative_checkpoints
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (cumulativeLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.recordCumulative tag cumulativeLog root).checkpoints =
      state.checkpoints ++ [⟨tag, { root, cumulativeLog }⟩] := rfl


-- @@ L163-166 verbatim
@[simp]
theorem ExtractorState.empty_cumulativeLog :
    ∀ {config : Configuration Cfg Address},
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).cumulativeLog = [] := rfl


-- @@ L168-171 verbatim
@[simp]
theorem ExtractorState.empty_checkpoints :
    ∀ {config : Configuration Cfg Address},
    (ExtractorState.empty : ExtractorState Cfg Query Address Y config).checkpoints = [] := rfl


-- @@ L173-178 verbatim
@[simp]
theorem ExtractorState.record_cumulativeLog
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).cumulativeLog = state.cumulativeLog ++ phaseLog := rfl


-- @@ L180-187 verbatim
@[simp]
theorem ExtractorState.record_checkpoints
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).checkpoints =
      state.checkpoints ++
        [⟨tag, { root, cumulativeLog := state.cumulativeLog ++ phaseLog }⟩] := rfl


-- @@ L189-195 verbatim
/-- Recording one commitment adds exactly one checkpoint. -/
theorem ExtractorState.record_checkpoints_length
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).checkpoints.length = state.checkpoints.length + 1 := by
  simp


-- @@ L197-201 verbatim
/-- Every recorded checkpoint transcript is a prefix of the state's current transcript. -/
def ExtractorState.CheckpointLogsPrefixCumulativeLog {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Prop :=
  ∀ tag checkpoint, ⟨tag, checkpoint⟩ ∈ state.checkpoints →
    checkpoint.cumulativeLog <+: state.cumulativeLog


-- @@ L203-209 verbatim
/-- The empty extractor state satisfies the checkpoint-prefix invariant. -/
theorem ExtractorState.checkpointLogsPrefixCumulativeLog_empty
    {config : Configuration Cfg Address} :
    ExtractorState.CheckpointLogsPrefixCumulativeLog
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config) := by
  intro tag checkpoint hmem
  simp at hmem


-- @@ L211-225 verbatim
/-- Recording one commitment preserves the checkpoint-prefix invariant. -/
theorem ExtractorState.CheckpointLogsPrefixCumulativeLog.record
    {config : Configuration Cfg Address}
    {state : ExtractorState Cfg Query Address Y config}
    (hstate : state.CheckpointLogsPrefixCumulativeLog)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (state.record tag phaseLog root).CheckpointLogsPrefixCumulativeLog := by
  intro recordedTag checkpoint hmem
  rw [ExtractorState.record_checkpoints] at hmem
  rcases List.mem_append.mp hmem with hprevious | hnew
  · exact (hstate recordedTag checkpoint hprevious).trans
      (List.prefix_append state.cumulativeLog phaseLog)
  · simp only [List.mem_singleton] at hnew
    cases hnew
    exact List.prefix_rfl


-- @@ L227-234 verbatim
/-- The checkpoint added by `record` occurs in the resulting history. -/
theorem ExtractorState.recorded_checkpoint_mem {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) (tag : Cfg)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    (⟨tag, { root, cumulativeLog := state.cumulativeLog ++ phaseLog }⟩ :
      AnyCheckpoint Cfg Query Address Y config) ∈
      (state.record tag phaseLog root).checkpoints := by
  simp


-- @@ L236-241 verbatim
/-- Append a terminal phase log after all commitment checkpoints have been recorded. -/
def ExtractorState.terminalLog {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) :
    MerkleTreeExtractor.QueryLog Query Y :=
  state.cumulativeLog ++ phaseLog


-- @@ L243-248 verbatim
/-- The commitment transcript is a prefix of the terminal transcript built from a suffix log. -/
theorem ExtractorState.prefix_terminalLog {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (phaseLog : MerkleTreeExtractor.QueryLog Query Y) :
    state.cumulativeLog <+: state.terminalLog phaseLog :=
  List.prefix_append _ _


-- @@ L250-250 verbatim
/-! ## Opening attempts and deterministic failure events -/


-- @@ L252-260 verbatim
/-- One verifier decision for a claimed opening against a recorded commitment checkpoint. -/
structure EvaluatedOpeningClaim (Query : Type v) (Y : Type)
    (config : Configuration Cfg Address) (tag : Cfg) where
  /-- Checkpoint whose root the opening claims to open. -/
  checkpoint : Checkpoint Query Y config tag
  /-- Dependent nonempty pruned batch opening. -/
  opening : BatchOpening Y (config.skeleton tag)
  /-- Result returned by the verifier. -/
  accepted : Bool


-- @@ L262-265 verbatim
/-- An opening attempt paired with its dependent configuration. -/
abbrev AnyEvaluatedOpeningClaim (Cfg : Type u) (Query : Type v) (Address : Type w) (Y : Type)
    (config : Configuration Cfg Address) :=
  (tag : Cfg) ×' EvaluatedOpeningClaim Query Y config tag


-- @@ L267-276 verbatim
/-- An accepted opening disagrees with the canonical partial opening extracted at commitment time.

The comparison maps every adversarial value and proof hash through `some`; consequently `none` in
the extracted tree is observable and causes disagreement. -/
def AcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (attempt : EvaluatedOpeningClaim Query Y config tag) : Prop :=
  attempt.accepted = true ∧
    attempt.checkpoint.extractedOpening view attempt.opening ≠ attempt.opening.map some


-- @@ L278-284 verbatim
/-- Two checkpoints for the same configuration and root reconstruct different partial trees. -/
def EqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (left right : Checkpoint Query Y config tag) : Prop :=
  left.root = right.root ∧
    Checkpoint.extractedTree view left ≠ Checkpoint.extractedTree view right


-- @@ L286-292 verbatim
@[simp]
theorem not_equalRootExtractionDisagreement_self [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    ¬ EqualRootExtractionDisagreement view checkpoint checkpoint := by
  simp [EqualRootExtractionDisagreement]


-- @@ L294-305 verbatim
/-- A commitment-time extraction changes when reconstructed from the terminal cumulative log.

This is distinct from equal-root inconsistency between two commitment checkpoints: a terminal
opening phase may extend the transcript even when it emits no new commitment. -/
def CheckpointTerminalExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag)
    (terminalLog : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  Checkpoint.extractedTree view checkpoint ≠
    MerkleTreeExtractor.tree view (config.skeleton tag) (config.addressKey tag)
      terminalLog checkpoint.root


-- @@ L307-314 verbatim
@[simp]
theorem not_checkpointTerminalExtractionDisagreement_self
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) :
    ¬ CheckpointTerminalExtractionDisagreement view checkpoint checkpoint.cumulativeLog := by
  simp [CheckpointTerminalExtractionDisagreement, Checkpoint.extractedTree]


-- @@ L316-328 verbatim
/-- Some accepted, recorded opening attempt disagrees with its checkpoint extraction.

The attempt and recorded checkpoint must carry the same configuration tag; cross-tag root reuse is
outside this event. -/
def HasAcceptedOpeningDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)) : Prop :=
  ∃ tag attempt,
    ⟨tag, attempt⟩ ∈ attempts ∧
    ⟨tag, attempt.checkpoint⟩ ∈ state.checkpoints ∧
    AcceptedOpeningDisagreement view attempt


-- @@ L330-341 verbatim
/-- Two recorded checkpoints for one configuration and root have inconsistent extractions.

Both checkpoints must carry the same configuration tag; cross-tag root reuse is outside this
event. -/
def HasEqualRootExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config) : Prop :=
  ∃ tag left right,
    ⟨tag, left⟩ ∈ state.checkpoints ∧
    ⟨tag, right⟩ ∈ state.checkpoints ∧
    EqualRootExtractionDisagreement view left right


-- @@ L343-352 verbatim
/-- Some recorded checkpoint extraction changes under the terminal transcript. -/
def HasCheckpointTerminalExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  ∃ tag checkpoint,
    ⟨tag, checkpoint⟩ ∈ state.checkpoints ∧
    CheckpointTerminalExtractionDisagreement view checkpoint
      (state.terminalLog terminalSuffix)


-- @@ L354-366 verbatim
/-- Deterministic bad event for stateful multi-commitment batch extraction.

Its opening and equal-root branches compare checkpoints only within one configuration tag;
cross-tag root reuse is outside the event. -/
def AnyCheckpointExtractionDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) : Prop :=
  HasAcceptedOpeningDisagreement view state attempts ∨
    HasEqualRootExtractionDisagreement view state ∨
      HasCheckpointTerminalExtractionDisagreement view state terminalSuffix


-- @@ L368-379 verbatim
/-- An accepted chosen opening disagrees with its checkpoint
extraction, or two equal roots at checkpoints of the same configuration have inconsistent
extractions. Checkpoint-to-terminal evolution is an internal strengthening used in the proof, not
part of this public event. Both branches compare checkpoints only within one configuration tag;
cross-tag root reuse is outside the event. -/
def OpeningOrEqualRootDisagreement [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)) : Prop :=
  HasAcceptedOpeningDisagreement view state attempts ∨
    HasEqualRootExtractionDisagreement view state


-- @@ L381-393 verbatim
/-- Opening or equal-root disagreement implies disagreement at some checkpoint. -/
theorem OpeningOrEqualRootDisagreement.toAnyCheckpointExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : OpeningOrEqualRootDisagreement view state attempts) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix := by
  rcases h with hopening | hequalRoot
  · exact Or.inl hopening
  · exact Or.inr (Or.inl hequalRoot)


-- @@ L395-409 verbatim
/-- If checkpoint extraction is stable under the terminal suffix, the strong and textbook events
coincide. This is a deterministic specialization, independent of any probability semantics. -/
theorem anyCheckpointDisagreement_iff_openingOrEqualRootDisagreement_of_noTerminalDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (hstable : ¬ HasCheckpointTerminalExtractionDisagreement
      view state terminalSuffix) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix ↔
      OpeningOrEqualRootDisagreement view state attempts := by
  simp only [AnyCheckpointExtractionDisagreement, OpeningOrEqualRootDisagreement]
  tauto


-- @@ L411-420 verbatim
theorem AnyCheckpointExtractionDisagreement.ofAcceptedOpeningDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasAcceptedOpeningDisagreement view state attempts) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix :=
  Or.inl h


-- @@ L422-431 verbatim
theorem AnyCheckpointExtractionDisagreement.ofEqualRootExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasEqualRootExtractionDisagreement view state) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix :=
  Or.inr (Or.inl h)


-- @@ L433-442 verbatim
theorem AnyCheckpointExtractionDisagreement.ofCheckpointTerminalExtractionDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y)
    (h : HasCheckpointTerminalExtractionDisagreement view state terminalSuffix) :
    AnyCheckpointExtractionDisagreement view state attempts terminalSuffix :=
  Or.inr (Or.inr h)


-- @@ L444-454 verbatim
/-- With no recorded commitments, none of the three disagreement branches can occur. -/
theorem not_anyCheckpointExtractionDisagreement_empty [DecidableEq Address] [DecidableEq Y]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (terminalSuffix : MerkleTreeExtractor.QueryLog Query Y) :
    ¬ AnyCheckpointExtractionDisagreement view
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)
        attempts terminalSuffix := by
  simp [AnyCheckpointExtractionDisagreement, HasAcceptedOpeningDisagreement,
    HasEqualRootExtractionDisagreement, HasCheckpointTerminalExtractionDisagreement]


-- @@ L456-456 verbatim
end MerkleTreeMultiExtractability
