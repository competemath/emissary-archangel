/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part06


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 07 -/


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open StateTransition (EvalsToInTime)

-- @@ L18-18 verbatim
open scoped BigOperators


-- @@ L20-20 verbatim
namespace GapCVP


-- @@ L22-22 verbatim
open GapCVP.TraceGolf (oneStep rebound)


-- @@ L24-24 verbatim
namespace CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM


-- @@ L26-26 verbatim
open Computability Turing GapCVP.CL GapCVP.CLCompleteVerifierSimulation GapCVP.CLCellRowBounds

-- @@ L27-27 verbatim
open GapCVP.BinaryEncoding GapCVP.ThreeCNFReduction GapCVP.SourceUniformTuringTM

-- @@ L28-28 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceOrder

-- @@ L29-29 verbatim
open GapCVP.CNFFlatStructuralRecordWorkerTM GapCVP.CNFFlatSourceGridDescriptorTM

-- @@ L30-30 verbatim
open GapCVP.CNFCappedFlatSourceListFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L31-31 verbatim
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

-- @@ L32-32 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

-- @@ L33-33 verbatim
open GapCVP.CNFFiveFamilyFlatSortedLiteralFamilies

-- @@ L34-34 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

-- @@ L35-35 verbatim
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM


-- @@ L37-41 verbatim
private def fiveSourceCellNegativePairLiteralList
    {T S : ℕ} (time : Time T) (position : Position T)
    (first second : Symbol S) : List (SignedLiteral T S) :=
  [negative (time, position, first),
    negative (time, position, second)]


-- @@ L43-78 verbatim
private theorem sortedElements_atMostOneClause_eq_pair
    {T S : ℕ} (time : Time T) (position : Position T)
    (first second : Symbol S) (hpair : first < second) :
    sortedElements (atMostOneClause time position first second) =
      fiveSourceCellNegativePairLiteralList
        time position first second := by
  apply sortedElements_eq_of_nodup_source_pairwise
  · intro literal
    simp only [fiveSourceCellNegativePairLiteralList, List.mem_cons, List.not_mem_nil, or_false,
        atMostOneClause,
        Finset.mem_insert, Finset.mem_singleton]
  · simp only [fiveSourceCellNegativePairLiteralList, negative, List.nodup_cons, List.mem_cons,
      Prod.mk.injEq,
        ne_of_lt hpair, and_false, and_true, List.not_mem_nil, or_self, not_false_eq_true,
            List.nodup_nil, and_self]
  · have hcode :
        Encodable.encode (negative (time, position, first)) ≤
          Encodable.encode (negative (time, position, second)) := by
      change
        Nat.pair
            (Nat.pair time.val
              (Nat.pair position.val first.val))
            (Encodable.encode false) ≤
          Nat.pair
            (Nat.pair time.val
              (Nat.pair position.val second.val))
            (Encodable.encode false)
      apply Nat.le_of_lt
      apply Nat.pair_lt_pair_left
      apply Nat.pair_lt_pair_right
      apply Nat.pair_lt_pair_right
      exact hpair
    simpa only [fiveSourceCellNegativePairLiteralList, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil,
        or_false, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
            and_true, ge_iff_le] using hcode


-- @@ L80-84 verbatim
private def fiveFlatRankedAtMostDescriptorPayload
    (grid : Polynomial ℕ) (first second : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatRankedSourceDescriptorStream grid false
    [first, second] input


-- @@ L86-92 verbatim
private noncomputable def fiveFamilyFlatRankedAtMostDescriptorPayloadComputable
    (grid : Polynomial ℕ) (first second : ℕ) :
    BitTM
      (fiveFlatRankedAtMostDescriptorPayload
        grid first second) :=
  fiveFamilyFlatRankedSourceDescriptorStreamComputable
    grid false [first, second]


-- @@ L94-98 verbatim
private def fiveFlatRankedAtMostDuplicatedCodePayload
    (grid : Polynomial ℕ) (first second : ℕ)
    (input : List Bool) : List Bool :=
  fiveFlatRankedSourceDuplicatedCodeStream grid false
    [first, second] input


-- @@ L100-106 verbatim
private noncomputable def fiveFamilyFlatRankedAtMostDuplicatedCodePayloadComputable
    (grid : Polynomial ℕ) (first second : ℕ) :
    BitTM
      (fiveFlatRankedAtMostDuplicatedCodePayload
        grid first second) :=
  fiveFamilyFlatRankedSourceDuplicatedCodeStreamComputable
    grid false [first, second]


-- @@ L108-118 verbatim
/-- GapCVP reduction support. -/
def fiveFlatRowMajorAtMostClauseRecordWord
    (grid : Polynomial ℕ) (first second : ℕ)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (fiveFlatRankedAtMostDescriptorPayload
        grid first second input) ++
    lengthPrefixedWord
      (fiveFlatRankedAtMostDuplicatedCodePayload
        grid first second input) ++
      lengthPrefixedWord [true, true]


-- @@ L120-147 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyFlatRowMajorAtMostClauseRecordComputable
    (grid : Polynomial ℕ) (first second : ℕ) :
    BitTM
      (fiveFlatRowMajorAtMostClauseRecordWord
        grid first second) := by
  have descriptors := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatRankedAtMostDescriptorPayloadComputable
      grid first second)
    structuralPrefixWriterComputable
  have codes := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatRankedAtMostDuplicatedCodePayloadComputable
      grid first second)
    structuralPrefixWriterComputable
  have count := constantWordComputable
    (lengthPrefixedWord [true, true])
  have physical := pointwiseAppendComputable
    descriptors (pointwiseAppendComputable codes count)
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (fiveFlatRankedAtMostDescriptorPayload
            grid first second input) ++
        lengthPrefixedWord
          (fiveFlatRankedAtMostDuplicatedCodePayload
            grid first second input) ++
          lengthPrefixedWord [true, true])
  simpa only [List.append_assoc, Function.comp_apply] using physical


-- @@ L149-183 verbatim
private theorem fiveFamilyFlatRankedAtMostDescriptorPayload_rowMajor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original))
    (first second : Symbol (completePhaseSymbolCount machine.tm))
    (hpair : first < second) :
    fiveFlatRankedAtMostDescriptorPayload
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      first.val second.val
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDescriptorPayload
        (atMostOneClause time position first second) := by
  unfold fiveFlatRankedAtMostDescriptorPayload
    fiveFlatRankedSourceDescriptorStream
    flatSourceClauseDescriptorPayload
  rw [sortedElements_atMostOneClause_eq_pair
    time position first second hpair]
  simp only [fiveSourceCellNegativePairLiteralList,
    flatSignedLiteralDescriptorStream, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  unfold fiveFamilyFlatRankedSourceDescriptorWord
  rw [fiveFlatIndexedVariableCode_rowMajor
    bound machine original suffix time position first,
    fiveFlatIndexedVariableCode_rowMajor
      bound machine original suffix time position second,
    tableauSourceSignedLiteralDescriptorWord_variable,
    tableauSourceSignedLiteralDescriptorWord_variable]
  rfl


-- @@ L185-219 verbatim
private theorem fiveFamilyFlatRankedAtMostDuplicatedCodePayload_rowMajor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original))
    (first second : Symbol (completePhaseSymbolCount machine.tm))
    (hpair : first < second) :
    fiveFlatRankedAtMostDuplicatedCodePayload
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      first.val second.val
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseDuplicatedCodePayload
        (atMostOneClause time position first second) := by
  unfold fiveFlatRankedAtMostDuplicatedCodePayload
    fiveFlatRankedSourceDuplicatedCodeStream
    flatSourceClauseDuplicatedCodePayload flatSourceFinsetCodes
  rw [sortedElements_atMostOneClause_eq_pair
    time position first second hpair]
  simp only [fiveSourceCellNegativePairLiteralList,
    flatDuplicatedUnarySourceStream, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  unfold fiveFamilyFlatRankedSourceDuplicatedCodeWord
  rw [fiveFlatIndexedVariableCode_rowMajor
    bound machine original suffix time position first,
    fiveFlatIndexedVariableCode_rowMajor
      bound machine original suffix time position second,
    duplicatedUnarySignedLiteralCodeWord_sourceVariable,
    duplicatedUnarySignedLiteralCodeWord_sourceVariable]
  rfl


-- @@ L221-230 verbatim
private theorem fiveFamilyFlatAtMostClause_exact_card
    {T S : ℕ} (time : Time T) (position : Position T)
    (first second : Symbol S) (hpair : first < second) :
    (atMostOneClause time position first second).card = 2 := by
  have hsort := congrArg List.length
    (sortedElements_atMostOneClause_eq_pair
      time position first second hpair)
  simpa only [sortedElements_length, fiveSourceCellNegativePairLiteralList, List.length_cons,
      List.length_nil,
      zero_add, Nat.reduceAdd] using hsort


-- @@ L232-259 verbatim
theorem fiveFamilyFlatRowMajorAtMostClauseRecordWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (time : Time (rowWidth bound machine original))
    (position : Position (rowWidth bound machine original))
    (first second : Symbol (completePhaseSymbolCount machine.tm))
    (hpair : first < second) :
    fiveFlatRowMajorAtMostClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      first.val second.val
      (lengthPrefixedWord
        (List.replicate
          (fiveFamilyFlatSourceRowMajorIndex time position) true) ++
        lengthPrefixedWord original ++ suffix) =
      flatSourceClauseAnnotatedRecord
        (atMostOneClause time position first second) := by
  unfold fiveFlatRowMajorAtMostClauseRecordWord
    flatSourceClauseAnnotatedRecord
  rw [fiveFamilyFlatRankedAtMostDescriptorPayload_rowMajor
    bound machine original suffix time position first second hpair,
    fiveFamilyFlatRankedAtMostDuplicatedCodePayload_rowMajor
      bound machine original suffix time position first second hpair]
  unfold flatSourceClauseUnaryCountPayload
  rw [fiveFamilyFlatAtMostClause_exact_card
    time position first second hpair]
  rfl


-- @@ L261-268 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def fiveFlatSourceVariableSingletonRecordWord
    (sign : Bool) (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (tableauSourceSignedLiteralDescriptorWord sign input) ++
    lengthPrefixedWord
      (duplicatedUnarySignedLiteralCodeWord sign input) ++
      lengthPrefixedWord [true]


-- @@ L270-292 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyFlatSourceVariableSingletonRecordComputable
    (sign : Bool) :
    BitTM
      (fiveFlatSourceVariableSingletonRecordWord sign) := by
  have descriptors := GapCVP.TMComposition.computableInPolyTime
    (tableauSourceSignedLiteralDescriptorComputable sign)
    structuralPrefixWriterComputable
  have codes := GapCVP.TMComposition.computableInPolyTime
    (duplicatedUnarySignedLiteralCodeComputable sign)
    structuralPrefixWriterComputable
  have count := constantWordComputable
    (lengthPrefixedWord [true])
  have physical := pointwiseAppendComputable
    descriptors (pointwiseAppendComputable codes count)
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (tableauSourceSignedLiteralDescriptorWord sign input) ++
        lengthPrefixedWord
          (duplicatedUnarySignedLiteralCodeWord sign input) ++
          lengthPrefixedWord [true])
  simpa only [List.append_assoc, Function.comp_apply] using physical


-- @@ L294-309 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyFlatSourceVariableSingletonRecordWord_valid
    {T S : ℕ} (atom : Variable T S) (sign : Bool) :
    fiveFlatSourceVariableSingletonRecordWord sign
      (List.replicate (Encodable.encode atom) true) =
      flatSourceClauseAnnotatedRecord
        ({(atom, sign)} : Clause T S) := by
  unfold fiveFlatSourceVariableSingletonRecordWord
    flatSourceClauseAnnotatedRecord
  rw [tableauSourceSignedLiteralDescriptorWord_variable,
    duplicatedUnarySignedLiteralCodeWord_sourceVariable,
    fiveFamilyFlatSingletonDescriptorPayload,
    fiveFamilyFlatSingletonDuplicatedCodePayload]
  unfold flatSourceClauseUnaryCountPayload
  simp only [Encodable.encode_prod_val, List.append_assoc, sourceLiteral, Finset.card_singleton,
      List.replicate_one]


-- @@ L311-311 verbatim
end CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM


-- @@ L313-313 verbatim
namespace SourceFourFamilyMarkerRotationTM


-- @@ L315-315 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.FormulaSemanticCert

-- @@ L316-316 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.OutputBoundedDependentRecordFold

-- @@ L317-317 verbatim
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM

-- @@ L318-318 verbatim
open GapCVP.SourceMixedRadixPreservedFourFamilyRecordTM

-- @@ L319-319 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

-- @@ L320-320 verbatim
open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM


-- @@ L322-329 verbatim
/-- GapCVP reduction support. -/
def fourFamilyOriginalMarkerRotationOutput
    (marker : List Bool → List Bool) (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourceFlatAtomicRecordStep
      (sourcePreservedPhysicalAtomicDescriptorOutput
        (sourceMixedRadixGuardedOriginalAtomOutput marker)
        input)).tail


-- @@ L331-355 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyOriginalMarkerRotationComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker) :
    BitTM
      (fourFamilyOriginalMarkerRotationOutput marker) := by
  have hguard := sourceMixedRadixGuardedOriginalAtomComputable
    computer
  have hpreserved := sourcePreservedPhysicalAtomicDescriptorComputable
    hguard
  have hrecord := GapCVP.TMComposition.computableInPolyTime
    hpreserved sourceFlatAtomicRecordComputable
  have htail := GapCVP.TMComposition.computableInPolyTime
    hrecord dropHeadComputable
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    htail firstFieldSuffixComputable
  change BitTM
    (fun input => firstFieldSuffix
      (sourceFlatAtomicRecordStep
        (sourcePreservedPhysicalAtomicDescriptorOutput
          (sourceMixedRadixGuardedOriginalAtomOutput marker)
          input)).tail)
  simpa only [sourcePreservedPhysicalAtomicDescriptorOutput_eq,
      sourceFlatAtomicRecordStep_descriptor,
      List.cons_append, List.tail_cons, Function.comp_def] using hsuffix


-- @@ L357-366 verbatim
theorem sourceFourFamilyOriginalMarkerRotationOutput_eq
    (marker : List Bool → List Bool) (input : List Bool) :
    fourFamilyOriginalMarkerRotationOutput marker input =
      firstFieldSuffix
        (input ++ marker (firstFieldContents input)) := by
  unfold fourFamilyOriginalMarkerRotationOutput
  rw [sourcePreservedPhysicalAtomicDescriptorOutput_eq]
  rw [sourceFlatAtomicRecordStep_descriptor]
  simp only [sourceMixedRadixGuardedOriginalAtomOutput, Function.comp_apply, List.cons_append,
      List.tail_cons]


-- @@ L368-375 verbatim
@[simp] private theorem sourceFourFamilyOriginalMarkerRotationOutput_query
    (marker : List Bool → List Bool)
    (query suffix : List Bool) :
    fourFamilyOriginalMarkerRotationOutput marker
        (lengthPrefixedWord query ++ suffix) =
      suffix ++ marker query := by
  rw [sourceFourFamilyOriginalMarkerRotationOutput_eq]
  simp only [firstFieldContents_valid, List.append_assoc, firstFieldSuffix_valid]


-- @@ L377-381 verbatim
/-- GapCVP reduction support. -/
@[expose] def fourFamilyOriginalMarkerStream
    (marker : List Bool → List Bool)
    (queries : List (List Bool)) : List Bool :=
  queries.flatMap marker


-- @@ L383-403 verbatim
private theorem sourceFourFamilyOriginalMarkerRotation_iterate_queries
    (marker : List Bool → List Bool)
    (queries : List (List Bool)) (suffix : List Bool) :
    ((fourFamilyOriginalMarkerRotationOutput marker)^[
      queries.length])
        (sourceMixedRadixOriginalSourceQueryStream queries ++ suffix) =
      suffix ++ fourFamilyOriginalMarkerStream
        marker queries := by
  induction queries generalizing suffix with
  | nil =>
      simp only [List.length_nil, sourceMixedRadixOriginalSourceQueryStream, List.flatMap_nil,
          List.nil_append,
          Function.iterate_zero, id_eq, fourFamilyOriginalMarkerStream, List.append_nil]
  | cons query remaining ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [sourceMixedRadixOriginalSourceQueryStream,
        fourFamilyOriginalMarkerStream,
        List.flatMap_cons, List.append_assoc]
      rw [sourceFourFamilyOriginalMarkerRotationOutput_query]
      simpa only [List.append_assoc, sourceMixedRadixOriginalSourceQueryStream,
          fourFamilyOriginalMarkerStream] using ih (suffix ++ marker query)


-- @@ L405-410 verbatim
theorem sourceFourFamilyFirstFieldSuffix_length_le
    (input : List Bool) :
    (firstFieldSuffix input).length ≤ input.length := by
  exact
    sourceMixedRadixPhysicalFirstFieldSuffix_length_le
      input


-- @@ L412-423 verbatim
private theorem sourceFourFamilyOriginalMarkerRotation_length_le
    (marker : List Bool → List Bool)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ 1)
    (input : List Bool) :
    (fourFamilyOriginalMarkerRotationOutput
      marker input).length ≤ input.length + 1 := by
  rw [sourceFourFamilyOriginalMarkerRotationOutput_eq]
  have hfield := sourceFourFamilyFirstFieldSuffix_length_le
    (input ++ marker (firstFieldContents input))
  have hbit := hmarker (firstFieldContents input)
  simp only [List.length_append] at hfield
  omega


-- @@ L425-440 verbatim
private theorem sourceFourFamilyOriginalMarkerRotation_iterate_length_le
    (marker : List Bool → List Bool)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ 1)
    (seed : List Bool) (stage : ℕ) :
    (((fourFamilyOriginalMarkerRotationOutput
      marker)^[stage]) seed).length ≤ seed.length + stage := by
  induction stage with
  | zero =>
      simp only [Function.iterate_zero, id_eq, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := sourceFourFamilyOriginalMarkerRotation_length_le
        marker hmarker
          (((fourFamilyOriginalMarkerRotationOutput
            marker)^[stage]) seed)
      omega


-- @@ L442-459 verbatim
private theorem sourceFourFamilyOriginalMarkerRotation_polynomiallyBoundedFoldStates
    (marker : List Bool → List Bool)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ 1) :
    PolynomiallyBoundedFoldStates
      (fourFamilyOriginalMarkerRotationOutput marker)
      (Polynomial.X + Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate :=
    sourceFourFamilyOriginalMarkerRotation_iterate_length_le
      marker hmarker seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_X]
  omega


-- @@ L461-473 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyOriginalMarkerFoldComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker)
    (hmarker : ∀ input : List Bool, (marker input).length ≤ 1) :
    BitTM
      (boundedRecordFoldOutput
        (fourFamilyOriginalMarkerRotationOutput marker)) :=
  boundedDependentRecordFoldComputable
    (sourceFourFamilyOriginalMarkerRotationComputable computer)
    (Polynomial.X + Polynomial.X)
    (sourceFourFamilyOriginalMarkerRotation_polynomiallyBoundedFoldStates
      marker hmarker)


-- @@ L475-486 verbatim
theorem boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
    (marker : List Bool → List Bool)
    (queries : List (List Bool)) (suffix : List Bool) :
    boundedRecordFoldOutput
        (fourFamilyOriginalMarkerRotationOutput marker)
        (unaryBoundedFoldWord queries.length
          (sourceMixedRadixOriginalSourceQueryStream queries ++ suffix)) =
      suffix ++ fourFamilyOriginalMarkerStream marker queries := by
  unfold boundedRecordFoldOutput
  rw [parseUnaryBoundedFold_word]
  exact sourceFourFamilyOriginalMarkerRotation_iterate_queries
    marker queries suffix


-- @@ L488-488 verbatim
end SourceFourFamilyMarkerRotationTM


-- @@ L490-490 verbatim
namespace SourceFourFamilyBooleanPredicateTM


-- @@ L492-492 verbatim
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L493-493 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure

-- @@ L494-494 verbatim
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFEncodedClauseSort

-- @@ L495-495 verbatim
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFNaturalOrderTotalComparator

-- @@ L496-496 verbatim
open GapCVP.CNFNaturalOrderCertifiedComparator GapCVP.CNFGuardedFiveFamilyTagDispatchTM

-- @@ L497-497 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L499-502 verbatim
/-- GapCVP reduction support. -/
def sourceFourFamilyBooleanNotWord : List Bool → List Bool :=
  markerConditionalOutput
    (fun _ : List Bool => [false]) [true]


-- @@ L504-509 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyBooleanNotComputable :
    BitTM
      sourceFourFamilyBooleanNotWord :=
  markerConditionalComputable
    (sourceFixedWordComputable [false]) [true]


-- @@ L511-514 verbatim
@[simp] theorem sourceFourFamilyBooleanNotWord_bit
    (bit : Bool) :
    sourceFourFamilyBooleanNotWord [bit] = [!bit] := by
  cases bit <;> rfl


-- @@ L516-522 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourceFourFamilyBooleanAndPairWord : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput
      (fun _ : List Bool => [true]) [false])
    [false]


-- @@ L524-531 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyBooleanAndPairComputable :
    BitTM
      sourceFourFamilyBooleanAndPairWord :=
  markerConditionalComputable
    (markerConditionalComputable
      (sourceFixedWordComputable [true]) [false])
    [false]


-- @@ L533-537 verbatim
@[simp] theorem sourceFourFamilyBooleanAndPairWord_bits
    (first second : Bool) :
    sourceFourFamilyBooleanAndPairWord [first, second] =
      [first && second] := by
  cases first <;> cases second <;> rfl


-- @@ L539-545 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourceFourFamilyBooleanAndOutput
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceFourFamilyBooleanAndPairWord
    (first input ++ second input)


-- @@ L547-561 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyBooleanAndComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (sourceFourFamilyBooleanAndOutput first second) := by
  have hpair := pointwiseAppendComputable
    hfirst hsecond
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpair sourceFourFamilyBooleanAndPairComputable
  change BitTM
    (fun input => sourceFourFamilyBooleanAndPairWord
      (first input ++ second input))
  simpa only [Function.comp_def] using hphysical


-- @@ L563-571 verbatim
theorem fourFamilyBooleanAndOutput_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    sourceFourFamilyBooleanAndOutput first second input =
      [firstBit && secondBit] := by
  simp only [sourceFourFamilyBooleanAndOutput, hfirst, hsecond, List.cons_append, List.nil_append,
      sourceFourFamilyBooleanAndPairWord_bits]


-- @@ L573-577 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourceFourFamilyBooleanNotOutput
    (marker : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanNotWord ∘ marker


-- @@ L579-586 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyBooleanNotOutputComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker) :
    BitTM
      (sourceFourFamilyBooleanNotOutput marker) :=
  GapCVP.TMComposition.computableInPolyTime
    computer sourceFourFamilyBooleanNotComputable


-- @@ L588-595 verbatim
theorem fourFamilyBooleanNotOutput_bit
    (marker : List Bool → List Bool)
    (input : List Bool) (bit : Bool)
    (hmarker : marker input = [bit]) :
    sourceFourFamilyBooleanNotOutput marker input =
      [!bit] := by
  simp only [sourceFourFamilyBooleanNotOutput, Function.comp_apply, hmarker,
      sourceFourFamilyBooleanNotWord_bit]


-- @@ L597-599 verbatim
private def sourceFourFamilyFirstUnaryNaturalRecordOutput
    (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord (firstFieldContents input)


-- @@ L601-610 verbatim
private noncomputable def sourceFourFamilyFirstUnaryNaturalRecordComputable :
    BitTM
      sourceFourFamilyFirstUnaryNaturalRecordOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable
    structuralAtomicNaturalWriterComputable
  change BitTM
    (fun input => structuralAtomicNaturalWord
      (firstFieldContents input))
  simpa only [Function.comp_def] using hphysical


-- @@ L612-615 verbatim
private def sourceFourFamilySecondUnaryNaturalRecordOutput
    (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord
    (firstFieldContents (firstFieldSuffix input))


-- @@ L617-627 verbatim
private noncomputable def sourceFourFamilySecondUnaryNaturalRecordComputable :
    BitTM
      sourceFourFamilySecondUnaryNaturalRecordOutput := by
  have hfirst := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hfirst structuralAtomicNaturalWriterComputable
  change BitTM
    (fun input => structuralAtomicNaturalWord
      (firstFieldContents (firstFieldSuffix input)))
  simpa only [Function.comp_def] using hphysical


-- @@ L629-633 verbatim
/-- GapCVP reduction support. -/
def fourFamilyDelimitedUnaryComparisonInput
    (input : List Bool) : List Bool :=
  sourceFourFamilyFirstUnaryNaturalRecordOutput input ++
    sourceFourFamilySecondUnaryNaturalRecordOutput input


-- @@ L635-641 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyDelimitedUnaryComparisonInputComputable :
    BitTM
      fourFamilyDelimitedUnaryComparisonInput :=
  pointwiseAppendComputable
    sourceFourFamilyFirstUnaryNaturalRecordComputable
    sourceFourFamilySecondUnaryNaturalRecordComputable


-- @@ L643-654 verbatim
theorem sourceFourFamilyDelimitedUnaryComparisonInput_valid
    (first second : ℕ) (suffix : List Bool) :
    fourFamilyDelimitedUnaryComparisonInput
        (lengthPrefixedWord (List.replicate first true) ++
          lengthPrefixedWord (List.replicate second true) ++ suffix) =
      lengthPrefixedWord (Computability.encodeNat first) ++
        lengthPrefixedWord (Computability.encodeNat second) := by
  simp only [fourFamilyDelimitedUnaryComparisonInput,
      sourceFourFamilyFirstUnaryNaturalRecordOutput,
      List.append_assoc, firstFieldContents_valid, structuralAtomicNaturalWord_eq_prefix,
          List.length_replicate,
      sourceFourFamilySecondUnaryNaturalRecordOutput, firstFieldSuffix_valid]


-- @@ L656-661 verbatim
/-- GapCVP reduction support. -/
@[expose]
def fourFamilyNaturalOrderingBitsOutput
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (sourcePreservingDelimitedNaturalComparisonWord input)


-- @@ L663-673 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyNaturalOrderingBitsComputable :
    BitTM
      fourFamilyNaturalOrderingBitsOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    sourcePreservingDelimitedNaturalComparisonComputable
    firstFieldSuffixComputable
  change BitTM
    (fun input => firstFieldSuffix
      (sourcePreservingDelimitedNaturalComparisonWord input))
  simpa only [Function.comp_def] using hphysical


-- @@ L675-678 verbatim
private def sourceFourFamilyOrderingLessBitWord
    (input : List Bool) : List Bool :=
  fixedDelimitedWordEqualityBitWord [false, true]
    (lengthPrefixedWord input)


-- @@ L680-689 verbatim
private noncomputable def sourceFourFamilyOrderingLessBitComputable :
    BitTM
      sourceFourFamilyOrderingLessBitWord := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    GapCVP.CLStructuralPrefixWriter.structuralPrefixWriterComputable
    (fixedDelimitedWordEqualityBitComputable [false, true])
  change BitTM
    (fun input => fixedDelimitedWordEqualityBitWord [false, true]
      (lengthPrefixedWord input))
  simpa only [fixedDelimitedWordEqualityBitWord_eq, Function.comp_def] using hphysical


-- @@ L691-702 verbatim
@[simp] private theorem sourceFourFamilyOrderingLessBitWord_ordering
    (outcome : EncodedWordOrdering) :
    sourceFourFamilyOrderingLessBitWord
        (encodedWordOrderingWord outcome) =
      [decide (outcome = .less)] := by
  unfold sourceFourFamilyOrderingLessBitWord
  rw [fixedDelimitedWordEqualityBitWord_eq]
  have hselector := fixedDelimitedWordEqualitySelector_valid
    [false, true] (encodedWordOrderingWord outcome) []
  simp only [List.append_nil] at hselector
  rw [hselector]
  cases outcome <;> rfl


-- @@ L704-707 verbatim
private def sourceFourFamilyUnaryLessBitOutput : List Bool → List Bool :=
  sourceFourFamilyOrderingLessBitWord ∘
    (fourFamilyNaturalOrderingBitsOutput ∘
      fourFamilyDelimitedUnaryComparisonInput)


-- @@ L709-716 verbatim
private noncomputable def sourceFourFamilyUnaryLessBitComputable :
    BitTM
      sourceFourFamilyUnaryLessBitOutput :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      sourceFourFamilyDelimitedUnaryComparisonInputComputable
      sourceFourFamilyNaturalOrderingBitsComputable)
    sourceFourFamilyOrderingLessBitComputable


-- @@ L718-739 verbatim
private theorem sourceFourFamilyUnaryLessBitOutput_valid
    (first second : ℕ) (suffix : List Bool) :
    sourceFourFamilyUnaryLessBitOutput
        (lengthPrefixedWord (List.replicate first true) ++
          lengthPrefixedWord (List.replicate second true) ++ suffix) =
      [decide (first < second)] := by
  unfold sourceFourFamilyUnaryLessBitOutput
  simp only [Function.comp_apply,
    sourceFourFamilyDelimitedUnaryComparisonInput_valid,
    fourFamilyNaturalOrderingBitsOutput]
  have hcomparison := sourcePreservingNaturalComparison_valid
    (Computability.encodeNat first)
    (Computability.encodeNat second) []
  simp only [List.append_nil] at hcomparison
  rw [hcomparison, firstFieldSuffix_valid]
  rw [sourceFourFamilyOrderingLessBitWord_ordering]
  rw [littleEndianNaturalOrdering_eq_value_order]
  simp only [littleEndianNaturalValue_encodeNat]
  by_cases hfirst : first < second
  · simp only [hfirst, ↓reduceIte, decide_true]
  · by_cases hsecond : second < first <;>
      simp [hfirst, hsecond]


-- @@ L741-748 verbatim
private theorem sourceFourFamilyUnaryLessBitOutput_length
    (input : List Bool) :
    (sourceFourFamilyUnaryLessBitOutput input).length = 1 := by
  unfold sourceFourFamilyUnaryLessBitOutput
    sourceFourFamilyOrderingLessBitWord
  simp only [fixedDelimitedWordEqualityBitWord_eq, Function.comp_apply, List.length_cons,
      List.length_nil,
      zero_add]


-- @@ L750-750 verbatim
end SourceFourFamilyBooleanPredicateTM


-- @@ L752-752 verbatim
namespace SourceFourFamilyInterpolationMembershipPredicateTM


-- @@ L754-754 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter

-- @@ L755-755 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceUnaryIntegerMultiplicationTM

-- @@ L756-756 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM


-- @@ L758-762 verbatim
/-- GapCVP reduction support. -/
def fourFamilyComputedUnarySumOutput
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  first input ++ second input


-- @@ L764-771 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyComputedUnarySumComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fourFamilyComputedUnarySumOutput first second) :=
  pointwiseAppendComputable hfirst hsecond


-- @@ L773-780 verbatim
theorem fourFamilyComputedUnarySumOutput_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (left right : ℕ)
    (hfirst : first input = List.replicate left true)
    (hsecond : second input = List.replicate right true) :
    fourFamilyComputedUnarySumOutput first second input =
      List.replicate (left + right) true := by
  simp only [fourFamilyComputedUnarySumOutput, hfirst, hsecond, List.replicate_append_replicate]


-- @@ L782-785 verbatim
private def fourFamilyComputedUnaryProductQuery
    (left right : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  left input ++ false :: right input


-- @@ L787-799 verbatim
private noncomputable def sourceFourFamilyComputedUnaryProductQueryComputable
    {left right : List Bool → List Bool}
    (hleft : BitTM left)
    (hright : BitTM right) :
    BitTM
      (fourFamilyComputedUnaryProductQuery left right) := by
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hright (prependBitComputable false)
  have hpair := pointwiseAppendComputable
    hleft hdelimited
  change BitTM
    (fun input => left input ++ false :: right input)
  simpa only [Function.comp_apply] using hpair


-- @@ L801-806 verbatim
/-- GapCVP reduction support. -/
def fourFamilyComputedUnaryProductOutput
    (left right : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceUnaryIntegerMultiplicationOutput
    (fourFamilyComputedUnaryProductQuery left right input)


-- @@ L808-822 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyComputedUnaryProductComputable
    {left right : List Bool → List Bool}
    (hleft : BitTM left)
    (hright : BitTM right) :
    BitTM
      (fourFamilyComputedUnaryProductOutput left right) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourceFourFamilyComputedUnaryProductQueryComputable
      hleft hright)
    sourceUnaryIntegerMultiplicationComputable
  change BitTM
    (fun input => sourceUnaryIntegerMultiplicationOutput
      (fourFamilyComputedUnaryProductQuery left right input))
  simpa only [Function.comp_def] using hphysical


-- @@ L824-837 verbatim
theorem fourFamilyComputedUnaryProductOutput_valid
    (left right : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : left input = List.replicate first true)
    (hsecond : right input = List.replicate second true) :
    fourFamilyComputedUnaryProductOutput left right input =
      List.replicate (first * second) true := by
  unfold fourFamilyComputedUnaryProductOutput
    fourFamilyComputedUnaryProductQuery
  rw [hfirst, hsecond]
  change sourceUnaryIntegerMultiplicationOutput
    (sourceUnaryIntegerMultiplicationQuery first second) = _
  exact sourceUnaryIntegerMultiplicationOutput_query
    first second


-- @@ L839-845 verbatim
/-- GapCVP reduction support. -/
def fourFamilyComputedUnaryLessBitOutput
    (left right : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceFourFamilyUnaryLessBitOutput
    (lengthPrefixedWord (left input) ++
      lengthPrefixedWord (right input))


-- @@ L847-866 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyComputedUnaryLessBitComputable
    {left right : List Bool → List Bool}
    (hleft : BitTM left)
    (hright : BitTM right) :
    BitTM
      (fourFamilyComputedUnaryLessBitOutput left right) := by
  have hleftRecord := GapCVP.TMComposition.computableInPolyTime
    hleft structuralPrefixWriterComputable
  have hrightRecord := GapCVP.TMComposition.computableInPolyTime
    hright structuralPrefixWriterComputable
  have hpair := pointwiseAppendComputable
    hleftRecord hrightRecord
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpair sourceFourFamilyUnaryLessBitComputable
  change BitTM
    (fun input => sourceFourFamilyUnaryLessBitOutput
      (lengthPrefixedWord (left input) ++
        lengthPrefixedWord (right input)))
  simpa only [Function.comp_apply, Function.comp_def] using hphysical


-- @@ L868-879 verbatim
theorem fourFamilyComputedUnaryLessBitOutput_valid
    (left right : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hfirst : left input = List.replicate first true)
    (hsecond : right input = List.replicate second true) :
    fourFamilyComputedUnaryLessBitOutput left right input =
      [decide (first < second)] := by
  unfold fourFamilyComputedUnaryLessBitOutput
  rw [hfirst, hsecond]
  simpa only [List.append_nil] using
    sourceFourFamilyUnaryLessBitOutput_valid
      first second []


-- @@ L881-885 verbatim
theorem fourFamilyComputedUnaryLessBitOutput_length
    (left right : List Bool → List Bool) (input : List Bool) :
    (fourFamilyComputedUnaryLessBitOutput
      left right input).length = 1 := by
  exact sourceFourFamilyUnaryLessBitOutput_length _


-- @@ L887-893 verbatim
/-- GapCVP reduction support. -/
def sourceFourFamilyBooleanOrOutput
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (sourceFourFamilyBooleanAndOutput
      (sourceFourFamilyBooleanNotOutput first)
      (sourceFourFamilyBooleanNotOutput second))


-- @@ L895-905 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceFourFamilyBooleanOrComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (sourceFourFamilyBooleanOrOutput first second) :=
  fourFamilyBooleanNotOutputComputable
    (fourFamilyBooleanAndComputable
      (fourFamilyBooleanNotOutputComputable hfirst)
      (fourFamilyBooleanNotOutputComputable hsecond))


-- @@ L907-918 verbatim
theorem fourFamilyBooleanOrOutput_bits
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    sourceFourFamilyBooleanOrOutput first second input =
      [firstBit || secondBit] := by
  cases firstBit <;> cases secondBit <;>
    simp [sourceFourFamilyBooleanOrOutput,
      sourceFourFamilyBooleanNotOutput,
      sourceFourFamilyBooleanAndOutput,
      Function.comp_apply, hfirst, hsecond]


-- @@ L920-920 verbatim
end SourceFourFamilyInterpolationMembershipPredicateTM


-- @@ L922-922 verbatim
namespace SourceFourFamilyDiagonalMembershipPredicateTM


-- @@ L924-924 verbatim
open Turing GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L925-925 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM


-- @@ L927-929 verbatim
private def sourceFourFamilyFixedUnaryOutput
    (value : ℕ) (_input : List Bool) : List Bool :=
  List.replicate value true


-- @@ L931-935 verbatim
private noncomputable def fourFamilyFixedUnaryComputable
    (value : ℕ) :
    BitTM
      (sourceFourFamilyFixedUnaryOutput value) :=
  sourceFixedWordComputable (List.replicate value true)


-- @@ L937-941 verbatim
private def fourFamilyComputedUnaryNeBitOutput
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanOrOutput
    (fourFamilyComputedUnaryLessBitOutput first second)
    (fourFamilyComputedUnaryLessBitOutput second first)


-- @@ L943-953 verbatim
private noncomputable def sourceFourFamilyComputedUnaryNeBitComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fourFamilyComputedUnaryNeBitOutput first second) :=
  sourceFourFamilyBooleanOrComputable
    (fourFamilyComputedUnaryLessBitComputable
      hfirst hsecond)
    (fourFamilyComputedUnaryLessBitComputable
      hsecond hfirst)


-- @@ L955-984 verbatim
private theorem sourceFourFamilyComputedUnaryNeBitOutput_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (left right : ℕ)
    (hleft : first input = List.replicate left true)
    (hright : second input = List.replicate right true) :
    fourFamilyComputedUnaryNeBitOutput first second input =
      [decide (left ≠ right)] := by
  have hforward := fourFamilyComputedUnaryLessBitOutput_valid
    first second input left right hleft hright
  have hbackward := fourFamilyComputedUnaryLessBitOutput_valid
    second first input right left hright hleft
  have hpair := fourFamilyBooleanOrOutput_bits
    (fourFamilyComputedUnaryLessBitOutput first second)
    (fourFamilyComputedUnaryLessBitOutput second first)
    input (decide (left < right)) (decide (right < left))
    hforward hbackward
  change sourceFourFamilyBooleanOrOutput
    (fourFamilyComputedUnaryLessBitOutput first second)
    (fourFamilyComputedUnaryLessBitOutput second first)
    input = _
  by_cases hlt : left < right
  · have hne : left ≠ right := by omega
    simpa only [ne_eq, hne, not_false_eq_true, decide_true, hlt, Bool.true_or] using hpair
  · by_cases hgt : right < left
    · have hne : left ≠ right := by omega
      simpa only [ne_eq, hne, not_false_eq_true, decide_true, hlt, decide_false, hgt, Bool.or_true]
          using hpair
    · have heq : left = right := by omega
      simpa only [heq, ne_eq, not_true_eq_false, decide_false, lt_self_iff_false, Bool.or_self]
          using hpair


-- @@ L986-990 verbatim
/-- GapCVP reduction support. -/
def fourFamilyComputedUnaryEqBitOutput
    (first second : List Bool → List Bool) : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryNeBitOutput first second)


-- @@ L992-1001 verbatim
/-- GapCVP reduction support. -/
noncomputable def fourFamilyComputedUnaryEqBitComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (fourFamilyComputedUnaryEqBitOutput first second) :=
  fourFamilyBooleanNotOutputComputable
    (sourceFourFamilyComputedUnaryNeBitComputable
      hfirst hsecond)


-- @@ L1003-1019 verbatim
theorem fourFamilyComputedUnaryEqBitOutput_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (left right : ℕ)
    (hleft : first input = List.replicate left true)
    (hright : second input = List.replicate right true) :
    fourFamilyComputedUnaryEqBitOutput first second input =
      [decide (left = right)] := by
  have hne := sourceFourFamilyComputedUnaryNeBitOutput_valid
    first second input left right hleft hright
  have hnot := fourFamilyBooleanNotOutput_bit
    (fourFamilyComputedUnaryNeBitOutput first second)
    input (decide (left ≠ right)) hne
  change sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryNeBitOutput first second)
    input = _
  by_cases heq : left = right <;>
    simpa [heq] using hnot


-- @@ L1021-1021 verbatim
end SourceFourFamilyDiagonalMembershipPredicateTM


-- @@ L1023-1023 verbatim
namespace CNFFiveFamilyPackedInitialOffsetFeatureTM


-- @@ L1025-1025 verbatim
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM

-- @@ L1026-1026 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

-- @@ L1027-1027 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM

-- @@ L1028-1028 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L1029-1029 verbatim
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM


-- @@ L1031-1037 verbatim
private def fiveFamilyPackedOffsetIndexWord
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    (fourFamilyComputedUnaryProductOutput
      position (sourceFourFamilyFixedUnaryOutput block))
    (sourceFourFamilyFixedUnaryOutput offset)


-- @@ L1039-1048 verbatim
private noncomputable def fivePackedOffsetIndexComputable
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetIndexWord position block offset) :=
  fourFamilyComputedUnarySumComputable
    (fourFamilyComputedUnaryProductComputable
      computer (fourFamilyFixedUnaryComputable block))
    (fourFamilyFixedUnaryComputable offset)


-- @@ L1050-1066 verbatim
private theorem fiveFamilyPackedOffsetIndexWord_valid
    (position : List Bool → List Bool)
    (input : List Bool) (value block offset : ℕ)
    (hposition : position input = List.replicate value true) :
    fiveFamilyPackedOffsetIndexWord position block offset input =
      List.replicate (value * block + offset) true := by
  unfold fiveFamilyPackedOffsetIndexWord
  apply fourFamilyComputedUnarySumOutput_valid
    (fourFamilyComputedUnaryProductOutput
      position (sourceFourFamilyFixedUnaryOutput block))
    (sourceFourFamilyFixedUnaryOutput offset)
    input (value * block) offset
  · apply fourFamilyComputedUnaryProductOutput_valid
      position (sourceFourFamilyFixedUnaryOutput block)
      input value block hposition
    rfl
  · rfl


-- @@ L1068-1074 verbatim
private def fiveFamilyPackedOffsetWithinBitWord
    (grid : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (fiveFamilyPackedOffsetIndexWord position block offset)
    (fiveFlatIndexedOriginalPolynomialUnary grid)


-- @@ L1076-1086 verbatim
private noncomputable def fiveFamilyPackedOffsetWithinBitComputable
    (grid : Polynomial ℕ)
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetWithinBitWord
        grid position block offset) :=
  fourFamilyComputedUnaryLessBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    (fiveFlatIndexedOriginalPolynomialUnaryComputable grid)


-- @@ L1088-1093 verbatim
private def fivePackedOffsetBeforeInputBitWord
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (fiveFamilyPackedOffsetIndexWord position block offset)
    (fiveFlatIndexedOriginalPolynomialUnary Polynomial.X)


-- @@ L1095-1105 verbatim
private noncomputable def fiveFamilyPackedOffsetBeforeInputBitComputable
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fivePackedOffsetBeforeInputBitWord
        position block offset) :=
  fourFamilyComputedUnaryLessBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    (fiveFlatIndexedOriginalPolynomialUnaryComputable
      Polynomial.X)


-- @@ L1107-1112 verbatim
private def fivePackedOffsetInputMarkerBitWord
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    (fiveFamilyPackedOffsetIndexWord position block offset)
    (fiveFlatIndexedOriginalPolynomialUnary Polynomial.X)


-- @@ L1114-1124 verbatim
private noncomputable def fiveFamilyPackedOffsetInputMarkerBitComputable
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fivePackedOffsetInputMarkerBitWord
        position block offset) :=
  fourFamilyComputedUnaryEqBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    (fiveFlatIndexedOriginalPolynomialUnaryComputable
      Polynomial.X)


-- @@ L1126-1131 verbatim
private def fiveFamilyPackedOffsetSourceBitWord
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    (fiveFamilyPackedOffsetIndexWord position block offset)
    fiveFlatIndexedPhysicalOriginal


-- @@ L1133-1142 verbatim
private noncomputable def fiveFamilyPackedOffsetSourceBitComputable
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetSourceBitWord
        position block offset) :=
  fiveOriginalDynamicBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    fiveFamilyFlatIndexedPhysicalOriginalComputable


-- @@ L1144-1149 verbatim
private def fiveFamilyPackedOffsetZeroBitWord
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    (fiveFamilyPackedOffsetIndexWord position block offset)
    (sourceFourFamilyFixedUnaryOutput 0)


-- @@ L1151-1160 verbatim
private noncomputable def fiveFamilyPackedOffsetZeroBitComputable
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetZeroBitWord
        position block offset) :=
  fourFamilyComputedUnaryEqBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    (fourFamilyFixedUnaryComputable 0)


-- @@ L1162-1169 verbatim
private def fiveFamilyPackedOffsetBudgetBitWord
    (bound : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block offset : ℕ) : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    (fiveFamilyPackedOffsetIndexWord position block offset)
    (fiveFlatIndexedOriginalPolynomialUnary
      (Polynomial.X + bound))


-- @@ L1171-1182 verbatim
private noncomputable def fiveFamilyPackedOffsetBudgetBitComputable
    (bound : Polynomial ℕ)
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetBudgetBitWord
        bound position block offset) :=
  fourFamilyComputedUnaryLessBitComputable
    (fivePackedOffsetIndexComputable computer block offset)
    (fiveFlatIndexedOriginalPolynomialUnaryComputable
      (Polynomial.X + bound))


-- @@ L1184-1199 verbatim
private def fiveFamilyPackedOffsetFeatureWord
    (bound grid : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block offset : ℕ) (input : List Bool) : List Bool :=
  fiveFamilyPackedOffsetWithinBitWord
      grid position block offset input ++
    fivePackedOffsetBeforeInputBitWord
      position block offset input ++
    fivePackedOffsetInputMarkerBitWord
      position block offset input ++
    fiveFamilyPackedOffsetSourceBitWord
      position block offset input ++
    fiveFamilyPackedOffsetZeroBitWord
      position block offset input ++
    fiveFamilyPackedOffsetBudgetBitWord
      bound position block offset input


-- @@ L1201-1247 verbatim
private noncomputable def fiveFamilyPackedOffsetFeatureComputable
    (bound grid : Polynomial ℕ)
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block offset : ℕ) :
    BitTM
      (fiveFamilyPackedOffsetFeatureWord
        bound grid position block offset) := by
  have withinBefore := pointwiseAppendComputable
    (fiveFamilyPackedOffsetWithinBitComputable
      grid computer block offset)
    (fiveFamilyPackedOffsetBeforeInputBitComputable
      computer block offset)
  have markerSource := pointwiseAppendComputable
    (fiveFamilyPackedOffsetInputMarkerBitComputable
      computer block offset)
    (fiveFamilyPackedOffsetSourceBitComputable
      computer block offset)
  have zeroBudget := pointwiseAppendComputable
    (fiveFamilyPackedOffsetZeroBitComputable
      computer block offset)
    (fiveFamilyPackedOffsetBudgetBitComputable
      bound computer block offset)
  have markerSourceZeroBudget := pointwiseAppendComputable
    markerSource zeroBudget
  have physical := pointwiseAppendComputable
    withinBefore markerSourceZeroBudget
  have hequality :
      (fun input =>
        (fiveFamilyPackedOffsetWithinBitWord
            grid position block offset input ++
          fivePackedOffsetBeforeInputBitWord
            position block offset input) ++
        ((fivePackedOffsetInputMarkerBitWord
            position block offset input ++
          fiveFamilyPackedOffsetSourceBitWord
            position block offset input) ++
          (fiveFamilyPackedOffsetZeroBitWord
            position block offset input ++
          fiveFamilyPackedOffsetBudgetBitWord
            bound position block offset input))) =
        fiveFamilyPackedOffsetFeatureWord
          bound grid position block offset := by
    funext input
    simp only [List.append_assoc, fiveFamilyPackedOffsetFeatureWord]
  rw [← hequality]
  exact physical


-- @@ L1249-1381 verbatim
private theorem fiveFamilyPackedOffsetFeatureWord_valid
    (bound grid : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block offset rank value : ℕ)
    (original suffix : List Bool)
    (hposition : position
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate value true) :
    fiveFamilyPackedOffsetFeatureWord
      bound grid position block offset
        (lengthPrefixedWord (List.replicate rank true) ++
          lengthPrefixedWord original ++ suffix) =
      [decide (value * block + offset <
          grid.eval original.length),
        decide (value * block + offset < original.length),
        decide (value * block + offset = original.length),
        (original.drop (value * block + offset)).headD false,
        decide (value * block + offset = 0),
        decide (value * block + offset <
          original.length + bound.eval original.length)] := by
  let query := lengthPrefixedWord (List.replicate rank true) ++
    lengthPrefixedWord original ++ suffix
  let coordinate := value * block + offset
  have hindex :
      fiveFamilyPackedOffsetIndexWord
        position block offset query =
        List.replicate coordinate true := by
    exact fiveFamilyPackedOffsetIndexWord_valid
      position query value block offset hposition
  have hgrid :
      fiveFlatIndexedOriginalPolynomialUnary grid query =
        List.replicate (grid.eval original.length) true :=
    fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
      grid rank original suffix
  have hlength :
      fiveFlatIndexedOriginalPolynomialUnary
        Polynomial.X query =
        List.replicate original.length true := by
    simpa [query, List.append_assoc] using
      fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
        Polynomial.X rank original suffix
  have hbudget :
      fiveFlatIndexedOriginalPolynomialUnary
        (Polynomial.X + bound) query =
        List.replicate
          (original.length + bound.eval original.length) true := by
    have hpolynomial :
        (Polynomial.X + bound).eval original.length =
          original.length + bound.eval original.length := by
      simp
    have hevaluated :=
      fiveFamilyFlatIndexedOriginalPolynomialUnary_valid
        (Polynomial.X + bound) rank original suffix
    rw [hpolynomial] at hevaluated
    exact hevaluated
  have hbit :
      fiveFamilyOriginalDynamicBitWord
          (fiveFamilyPackedOffsetIndexWord
            position block offset)
          fiveFlatIndexedPhysicalOriginal query =
        [(original.drop coordinate).headD false] := by
    rw [fiveOriginalDynamicBitWord_valid
      (fiveFamilyPackedOffsetIndexWord
        position block offset)
      fiveFlatIndexedPhysicalOriginal
      query coordinate hindex]
    rw [fiveFamilyFlatIndexedPhysicalOriginal_valid
      rank original suffix]
  unfold fiveFamilyPackedOffsetFeatureWord
    fiveFamilyPackedOffsetWithinBitWord
    fivePackedOffsetBeforeInputBitWord
    fivePackedOffsetInputMarkerBitWord
    fiveFamilyPackedOffsetSourceBitWord
    fiveFamilyPackedOffsetZeroBitWord
    fiveFamilyPackedOffsetBudgetBitWord
  change
    fourFamilyComputedUnaryLessBitOutput
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        (fiveFlatIndexedOriginalPolynomialUnary grid)
        query ++
      fourFamilyComputedUnaryLessBitOutput
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        (fiveFlatIndexedOriginalPolynomialUnary
          Polynomial.X)
        query ++
      fourFamilyComputedUnaryEqBitOutput
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        (fiveFlatIndexedOriginalPolynomialUnary
          Polynomial.X)
        query ++
      fiveFamilyOriginalDynamicBitWord
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        fiveFlatIndexedPhysicalOriginal query ++
      fourFamilyComputedUnaryEqBitOutput
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        (sourceFourFamilyFixedUnaryOutput 0)
        query ++
      fourFamilyComputedUnaryLessBitOutput
        (fiveFamilyPackedOffsetIndexWord
          position block offset)
        (fiveFlatIndexedOriginalPolynomialUnary
          (Polynomial.X + bound)) query = _
  rw [fourFamilyComputedUnaryLessBitOutput_valid
      (fiveFamilyPackedOffsetIndexWord position block offset)
      (fiveFlatIndexedOriginalPolynomialUnary grid)
      query coordinate (grid.eval original.length) hindex hgrid,
    fourFamilyComputedUnaryLessBitOutput_valid
      (fiveFamilyPackedOffsetIndexWord position block offset)
      (fiveFlatIndexedOriginalPolynomialUnary Polynomial.X)
      query coordinate original.length hindex hlength,
    fourFamilyComputedUnaryEqBitOutput_valid
      (fiveFamilyPackedOffsetIndexWord position block offset)
      (fiveFlatIndexedOriginalPolynomialUnary Polynomial.X)
      query coordinate original.length hindex hlength,
    hbit,
    fourFamilyComputedUnaryEqBitOutput_valid
      (fiveFamilyPackedOffsetIndexWord position block offset)
      (sourceFourFamilyFixedUnaryOutput 0)
      query coordinate 0 hindex rfl,
    fourFamilyComputedUnaryLessBitOutput_valid
      (fiveFamilyPackedOffsetIndexWord position block offset)
      (fiveFlatIndexedOriginalPolynomialUnary
        (Polynomial.X + bound))
      query coordinate
      (original.length + bound.eval original.length)
      hindex hbudget]
  simp [coordinate]


-- @@ L1383-1390 verbatim
private def fiveFamilyPackedOffsetFeatureStream
    (bound grid : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block : ℕ) (offsets : List ℕ)
    (input : List Bool) : List Bool :=
  offsets.flatMap fun offset =>
    fiveFamilyPackedOffsetFeatureWord
      bound grid position block offset input


-- @@ L1392-1405 verbatim
private noncomputable def fiveFamilyPackedOffsetFeatureStreamComputable
    (bound grid : Polynomial ℕ)
    {position : List Bool → List Bool}
    (computer : BitTM position)
    (block : ℕ) (offsets : List ℕ) :
    BitTM
      (fiveFamilyPackedOffsetFeatureStream
        bound grid position block offsets) := by
  induction offsets with
  | nil => exact constantWordComputable []
  | cons offset remaining ih =>
      exact pointwiseAppendComputable
        (fiveFamilyPackedOffsetFeatureComputable
          bound grid computer block offset) ih


-- @@ L1407-1435 verbatim
private theorem fiveFamilyPackedOffsetFeatureStream_valid
    (bound grid : Polynomial ℕ)
    (position : List Bool → List Bool)
    (block rank value : ℕ)
    (offsets : List ℕ)
    (original suffix : List Bool)
    (hposition : position
      (lengthPrefixedWord (List.replicate rank true) ++
        lengthPrefixedWord original ++ suffix) =
      List.replicate value true) :
    fiveFamilyPackedOffsetFeatureStream
      bound grid position block offsets
        (lengthPrefixedWord (List.replicate rank true) ++
          lengthPrefixedWord original ++ suffix) =
      offsets.flatMap fun offset =>
        [decide (value * block + offset <
            grid.eval original.length),
          decide (value * block + offset < original.length),
          decide (value * block + offset = original.length),
          (original.drop (value * block + offset)).headD false,
          decide (value * block + offset = 0),
          decide (value * block + offset <
            original.length + bound.eval original.length)] := by
  unfold fiveFamilyPackedOffsetFeatureStream
  apply List.flatMap_congr
  intro offset _
  exact fiveFamilyPackedOffsetFeatureWord_valid
    bound grid position block offset rank value
      original suffix hposition


-- @@ L1437-1437 verbatim
end CNFFiveFamilyPackedInitialOffsetFeatureTM


-- @@ L1439-1439 verbatim
namespace CNFFiveFamilyPackedInitialCellDecoderTM


-- @@ L1441-1441 verbatim
open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates GapCVP.CLCellRows

-- @@ L1442-1442 verbatim
open GapCVP.CLLocalWindows GapCVP.CLCellRowBounds GapCVP.CLFullTableauEmitter

-- @@ L1443-1443 verbatim
open GapCVP.CLCompleteVerifierSimulation GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding

-- @@ L1444-1444 verbatim
open GapCVP.SourceUniformTuringTM GapCVP.SourceMachineCert

-- @@ L1445-1445 verbatim
open GapCVP.OutputPolynomialCompositionClosure GapCVP.CLEmittedCNFTM GapCVP.CLWindowTruthTable

-- @@ L1446-1446 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFUnaryPairIndexTM

-- @@ L1447-1447 verbatim
open GapCVP.CNFUnaryPairIndexTotalRuntimeCert GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

-- @@ L1448-1448 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

-- @@ L1449-1449 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM

-- @@ L1450-1450 verbatim
open GapCVP.CNFFiveFamilyPackedInitialOffsetFeatureTM

-- @@ L1451-1451 verbatim
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM


-- @@ L1453-1455 verbatim
private def fiveFamilyPackedSixTrackChunk
    (features : List Bool) (offset : ℕ) : List Bool :=
  (features.drop (6 * offset)).take 6


-- @@ L1457-1484 verbatim
private theorem fiveFamilyPackedSixTrackChunk_flatMap
    {α : Type} (records : List α) (observation : α → List Bool)
    (hlength : ∀ record : α, (observation record).length = 6)
    (index : ℕ) (hindex : index < records.length) :
    fiveFamilyPackedSixTrackChunk
      (records.flatMap observation) index =
      observation records[index] := by
  have hfront :
      ((records.take index).flatMap observation).length =
        6 * index := by
    simp only [List.length_flatMap, hlength, List.map_take, List.map_const', List.take_replicate,
        Nat.min_eq_left (Nat.le_of_lt hindex), List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  unfold fiveFamilyPackedSixTrackChunk
  calc
    ((records.flatMap observation).drop (6 * index)).take 6 =
        ((((records.take index).flatMap observation ++
          (records.drop index).flatMap observation).drop
            (6 * index))).take 6 := by
              rw [← List.flatMap_append,
                List.take_append_drop]
    _ = ((records.drop index).flatMap observation).take 6 := by
      rw [← hfront, List.drop_append_length]
    _ = observation records[index] := by
      rw [List.drop_eq_getElem_cons hindex,
        List.flatMap_cons,
        List.take_append_of_le_length (by
          rw [hlength])]
      exact List.take_of_length_le (by rw [hlength])


-- @@ L1486-1497 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def fivePackedActualOffsetObservation
    (bound grid : Polynomial ℕ)
    (original : List Bool) (position block offset : ℕ) : List Bool :=
  [decide (position * block + offset <
      grid.eval original.length),
    decide (position * block + offset < original.length),
    decide (position * block + offset = original.length),
    (original.drop (position * block + offset)).headD false,
    decide (position * block + offset = 0),
    decide (position * block + offset <
      original.length + bound.eval original.length)]


-- @@ L1499-1508 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem fiveFamilyPackedActualOffsetObservation_length
    (bound grid : Polynomial ℕ)
    (original : List Bool) (position block offset : ℕ) :
    (fivePackedActualOffsetObservation
      bound grid original position block offset).length = 6 := by
  simp only [fivePackedActualOffsetObservation, List.headD_eq_head?_getD, List.head?_drop,
      Nat.add_eq_zero_iff,
      mul_eq_zero, Bool.decide_and, Bool.decide_or, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd]


-- @@ L1510-1525 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def fivePackedInitialWholeFeatureWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (input : List Bool) : List Bool :=
  fiveFamilyPackedOffsetFeatureStream
      bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
      fiveFamilyFlatIndexedPhysicalRank
      (blockSize machine.tm)
      (List.range (blockSize machine.tm)) input ++
    fiveFamilyPackedOffsetFeatureStream
      bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (sourceFourFamilyFixedUnaryOutput 0)
      (blockSize machine.tm)
      (List.range (blockSize machine.tm)) input


-- @@ L1527-1542 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveFamilyPackedInitialWholeFeatureComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fivePackedInitialWholeFeatureWord bound machine) := by
  have center := fiveFamilyPackedOffsetFeatureStreamComputable
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    fiveFlatIndexedPhysicalRankComputable
    (blockSize machine.tm) (List.range (blockSize machine.tm))
  have head := fiveFamilyPackedOffsetFeatureStreamComputable
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    (fourFamilyFixedUnaryComputable 0)
    (blockSize machine.tm) (List.range (blockSize machine.tm))
  exact pointwiseAppendComputable center head


-- @@ L1544-1575 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyPackedInitialWholeFeatureWord_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fivePackedInitialWholeFeatureWord bound machine
      (lengthPrefixedWord (List.replicate position.val true) ++
        lengthPrefixedWord original ++ suffix) =
      (List.range (blockSize machine.tm)).flatMap
          (fivePackedActualOffsetObservation
            bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
            original position.val (blockSize machine.tm)) ++
        (List.range (blockSize machine.tm)).flatMap
          (fivePackedActualOffsetObservation
            bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
            original 0 (blockSize machine.tm)) := by
  unfold fivePackedInitialWholeFeatureWord
  rw [fiveFamilyPackedOffsetFeatureStream_valid
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    fiveFamilyFlatIndexedPhysicalRank
    (blockSize machine.tm) position.val position.val
    (List.range (blockSize machine.tm)) original suffix
    (fiveFamilyFlatIndexedPhysicalRank_valid
      position.val original suffix)]
  rw [fiveFamilyPackedOffsetFeatureStream_valid
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    (sourceFourFamilyFixedUnaryOutput 0)
    (blockSize machine.tm) position.val 0
    (List.range (blockSize machine.tm)) original suffix rfl]
  rfl


-- @@ L1577-1587 verbatim
private def fiveFamilyPackedObservationPayload
    (observation : List Bool) : PairedInputTag :=
  if observation.getD 0 false then
    if observation.getD 1 false then
      .bit (.inl (observation.getD 3 false))
    else if observation.getD 2 false then
      .marker
    else
      .blank
  else
    .blank


-- @@ L1589-1591 verbatim
private def fiveFamilyPackedObservationRange
    (observation : List Bool) : Bool :=
  observation.getD 0 false


-- @@ L1593-1595 verbatim
private def fiveFamilyPackedObservationZero
    (observation : List Bool) : Bool :=
  observation.getD 4 false


-- @@ L1597-1599 verbatim
private def fiveFamilyPackedObservationBudget
    (observation : List Bool) : Bool :=
  observation.getD 5 false


-- @@ L1601-1609 verbatim
private def fivePackedObservationScriptCell
    (tm : Turing.FinTM2) (observation : List Bool) :
    LocalCellSymbol tm :=
  if fiveFamilyPackedObservationRange observation then
    (if fiveFamilyPackedObservationZero observation then
       .accepting else .guessing,
      none, fun _ => none, false)
  else
    blankCell tm


-- @@ L1611-1645 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def fiveFamilyPackedInitialDecodedCell
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (features : List Bool) : CompletePhaseCell machine.tm :=
  let block := blockSize machine.tm
  let center := features.take (6 * block)
  let head := features.drop (6 * block)
  { mode := .guessing
    script :=
      ((fun offset =>
          fivePackedObservationScriptCell machine.tm
            (fiveFamilyPackedSixTrackChunk center offset.val),
        fun offset =>
          fivePackedObservationScriptCell machine.tm
            (fiveFamilyPackedSixTrackChunk head offset.val)),
        defaultVerifierHint machine.tm,
        fiveFamilyPackedObservationZero
          (fiveFamilyPackedSixTrackChunk center 0))
    payload := fun offset =>
      fiveFamilyPackedObservationPayload
        (fiveFamilyPackedSixTrackChunk center offset.val)
    payloadHead := fun offset =>
      fiveFamilyPackedObservationPayload
        (fiveFamilyPackedSixTrackChunk head offset.val)
    range := fun offset =>
      fiveFamilyPackedObservationRange
        (fiveFamilyPackedSixTrackChunk center offset.val)
    rangeHead := fun offset =>
      fiveFamilyPackedObservationRange
        (fiveFamilyPackedSixTrackChunk head offset.val)
    budget := fun offset =>
      fiveFamilyPackedObservationBudget
        (fiveFamilyPackedSixTrackChunk center offset.val)
    guessBit := false }


-- @@ L1647-1666 verbatim
private theorem fivePackedActualOffsetObservation_chunk
    (bound grid : Polynomial ℕ)
    (original : List Bool) (position block : ℕ)
    (offset : Fin block) :
    fiveFamilyPackedSixTrackChunk
      ((List.range block).flatMap
        (fivePackedActualOffsetObservation
          bound grid original position block)) offset.val =
      fivePackedActualOffsetObservation
        bound grid original position block offset.val := by
  have recovered := fiveFamilyPackedSixTrackChunk_flatMap
    (List.range block)
    (fivePackedActualOffsetObservation
      bound grid original position block)
    (fun index =>
      fiveFamilyPackedActualOffsetObservation_length
        bound grid original position block index)
    offset.val (by
      simpa only [List.length_range] using offset.isLt)
  simpa only [List.getElem_range] using recovered


-- @@ L1668-1681 verbatim
private theorem fiveFamilyPairedInputTagAt_empty
    (original : List Bool) (index : ℕ) :
    pairedInputTagAt original [] index =
      if index < original.length then
        .bit (.inl ((original.drop index).headD false))
      else if index = original.length then
        .marker
      else
        .blank := by
  unfold pairedInputTagAt
  simp only [pairBitEncoding_apply, List.map_nil,
    List.append_nil, List.length_map, List.getElem?_map]
  by_cases hindex : index < original.length <;>
    simp [hindex]


-- @@ L1683-1706 verbatim
private theorem fiveFamilyPackedObservationPayload_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original))
    (offset : Fin (blockSize machine.tm)) :
    fiveFamilyPackedObservationPayload
      (fivePackedActualOffsetObservation
        bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
        original position.val (blockSize machine.tm) offset.val) =
      pairedInputBlockAt machine.tm
        (rowWidth bound machine original) original []
        position offset := by
  simp only [fiveFamilyPackedObservationPayload, fivePackedActualOffsetObservation,
      fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff, List.headD_eq_head?_getD,
          List.head?_drop,
      Nat.add_eq_zero_iff, mul_eq_zero, Fin.val_eq_zero_iff, Bool.decide_and, Bool.decide_or,
          List.getD_eq_getElem?_getD,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
          List.getElem_cons_zero,
      Option.getD_some, decide_eq_true_eq, Nat.one_lt_ofNat, List.getElem_cons_succ, Nat.reduceLT,
          pairedInputBlockAt,
      fiveFamilyPairedInputTagAt_empty]


-- @@ L1708-1728 verbatim
private theorem fiveFamilyPackedObservationRange_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original))
    (offset : Fin (blockSize machine.tm)) :
    fiveFamilyPackedObservationRange
      (fivePackedActualOffsetObservation
        bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
        original position.val (blockSize machine.tm) offset.val) =
      phaseRangeBlockAt machine.tm
        (rowWidth bound machine original) position offset := by
  simp only [fiveFamilyPackedObservationRange, fivePackedActualOffsetObservation,
      fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff, List.headD_eq_head?_getD,
          List.head?_drop,
      Nat.add_eq_zero_iff, mul_eq_zero, Fin.val_eq_zero_iff, Bool.decide_and, Bool.decide_or,
          List.getD_eq_getElem?_getD,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
          List.getElem_cons_zero,
      Option.getD_some, phaseRangeBlockAt]


-- @@ L1730-1749 verbatim
private theorem fiveFamilyPackedObservationBudget_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original))
    (offset : Fin (blockSize machine.tm)) :
    fiveFamilyPackedObservationBudget
      (fivePackedActualOffsetObservation
        bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
        original position.val (blockSize machine.tm) offset.val) =
      phaseBudgetBlockAt bound machine original position offset := by
  simp only [fiveFamilyPackedObservationBudget, fivePackedActualOffsetObservation,
      fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff, List.headD_eq_head?_getD,
          List.head?_drop,
      Nat.add_eq_zero_iff, mul_eq_zero, Fin.val_eq_zero_iff, Bool.decide_and, Bool.decide_or,
          List.getD_eq_getElem?_getD,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos,
          List.getElem_cons_succ,
      List.getElem_cons_zero, Option.getD_some, phaseBudgetBlockAt]


-- @@ L1751-1780 verbatim
private theorem fiveFamilyPackedObservationScriptCell_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original))
    (offset : Fin (blockSize machine.tm)) :
    fivePackedObservationScriptCell machine.tm
      (fivePackedActualOffsetObservation
        bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
        original position.val (blockSize machine.tm) offset.val) =
      packRow machine.tm
        (rowWidth bound machine original)
        (guessingRow machine.tm
          (rowWidth bound machine original) [])
        position offset := by
  unfold fivePackedObservationScriptCell
    fiveFamilyPackedObservationRange
    fiveFamilyPackedObservationZero
    fivePackedActualOffsetObservation
    packRow guessingRow certificatePhase
  simp only [fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff,
      List.headD_eq_head?_getD,
      List.head?_drop, Nat.add_eq_zero_iff, mul_eq_zero, Fin.val_eq_zero_iff, Bool.decide_and,
          Bool.decide_or,
      List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
          Nat.ofNat_pos, getElem?_pos,
      List.getElem_cons_zero, Option.getD_some, decide_eq_true_eq, Nat.reduceLT,
          List.getElem_cons_succ, Bool.and_eq_true,
      Bool.or_eq_true, not_lt_zero, ↓reduceDIte, dite_eq_ite]


-- @@ L1782-1800 verbatim
private theorem fiveFamilyPackedObservationFirstBlock_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveFamilyPackedObservationZero
      (fivePackedActualOffsetObservation
        bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
        original position.val (blockSize machine.tm) 0) =
      decide (position.val = 0) := by
  simp only [fiveFamilyPackedObservationZero, fivePackedActualOffsetObservation, add_zero,
      fiveFamilyFlatIndexedGridPolynomial_eval, Order.lt_add_one_iff, List.headD_eq_head?_getD,
          List.head?_drop,
      mul_eq_zero, Fin.val_eq_zero_iff, ne_of_gt (blockSize_pos machine.tm), or_false,
          List.getD_eq_getElem?_getD,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos,
          List.getElem_cons_succ,
      List.getElem_cons_zero, Option.getD_some]


-- @@ L1802-1816 verbatim
private theorem fiveFamilyCompletePhaseCell_ext
    (tm : Turing.FinTM2)
    (first second : CompletePhaseCell tm)
    (hmode : first.mode = second.mode)
    (hscript : first.script = second.script)
    (hpayload : first.payload = second.payload)
    (hhead : first.payloadHead = second.payloadHead)
    (hrange : first.range = second.range)
    (hrangeHead : first.rangeHead = second.rangeHead)
    (hbudget : first.budget = second.budget)
    (hguess : first.guessBit = second.guessBit) :
    first = second := by
  cases first
  cases second
  simp_all


-- @@ L1818-1978 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem fiveFamilyPackedInitialDecodedCell_valid
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original suffix : List Bool)
    (position : Position (rowWidth bound machine original)) :
    fiveFamilyPackedInitialDecodedCell machine
      (fivePackedInitialWholeFeatureWord bound machine
        (lengthPrefixedWord (List.replicate position.val true) ++
          lengthPrefixedWord original ++ suffix)) =
      initialPhaseCell bound machine original position := by
  rw [fiveFamilyPackedInitialWholeFeatureWord_valid
    bound machine original suffix position]
  let block := blockSize machine.tm
  let grid := fiveFamilyFlatIndexedGridPolynomial bound machine
  let center := (List.range block).flatMap
    (fivePackedActualOffsetObservation
      bound grid original position.val block)
  let head := (List.range block).flatMap
    (fivePackedActualOffsetObservation
      bound grid original 0 block)
  have hcenterLength : center.length = 6 * block := by
    simp only [List.length_flatMap, fiveFamilyPackedActualOffsetObservation_length,
        List.map_const',
        List.length_range, List.sum_replicate, smul_eq_mul, Nat.mul_comm, center]
  have htake : (center ++ head).take (6 * block) = center := by
    rw [← hcenterLength, List.take_append_of_le_length
      (Nat.le_refl center.length)]
    simp only [List.take_length]
  have hdrop : (center ++ head).drop (6 * block) = head := by
    rw [← hcenterLength, List.drop_append_length]
  have htake' :
      (center ++ head).take (6 * blockSize machine.tm) = center := by
    simpa only [block] using htake
  have hdrop' :
      (center ++ head).drop (6 * blockSize machine.tm) = head := by
    simpa only [block] using hdrop
  change fiveFamilyPackedInitialDecodedCell machine
    (center ++ head) = initialPhaseCell bound machine original position
  unfold fiveFamilyPackedInitialDecodedCell
  simp only [htake', hdrop']
  apply fiveFamilyCompletePhaseCell_ext machine.tm
  · rfl
  · unfold initialPhaseCell canonicalGuessingScriptRow
    apply Prod.ext
    · apply Prod.ext
      · funext offset
        change
          fivePackedObservationScriptCell machine.tm
            (fiveFamilyPackedSixTrackChunk center offset.val) =
          packRow machine.tm
            (rowWidth bound machine original)
            (guessingRow machine.tm
              (rowWidth bound machine original) [])
            position offset
        rw [show fiveFamilyPackedSixTrackChunk center offset.val =
          fivePackedActualOffsetObservation
            bound grid original position.val block offset.val from
          fivePackedActualOffsetObservation_chunk
            bound grid original position.val block offset]
        exact fiveFamilyPackedObservationScriptCell_valid
          bound machine original position offset
      · funext offset
        change
          fivePackedObservationScriptCell machine.tm
            (fiveFamilyPackedSixTrackChunk head offset.val) =
          packRow machine.tm
            (rowWidth bound machine original)
            (guessingRow machine.tm
              (rowWidth bound machine original) [])
            (0 : Position (rowWidth bound machine original))
            offset
        rw [show fiveFamilyPackedSixTrackChunk head offset.val =
          fivePackedActualOffsetObservation
            bound grid original 0 block offset.val from
          fivePackedActualOffsetObservation_chunk
            bound grid original 0 block offset]
        exact fiveFamilyPackedObservationScriptCell_valid
          bound machine original (0 : Position
            (rowWidth bound machine original)) offset
    · apply Prod.ext
      · rfl
      · rw [show fiveFamilyPackedSixTrackChunk center 0 =
          fivePackedActualOffsetObservation
            bound grid original position.val block 0 from
          fivePackedActualOffsetObservation_chunk
            bound grid original position.val block
            ⟨0, blockSize_pos machine.tm⟩]
        exact fiveFamilyPackedObservationFirstBlock_valid
          bound machine original position
  · funext offset
    change
      fiveFamilyPackedObservationPayload
        (fiveFamilyPackedSixTrackChunk center offset.val) =
      pairedInputBlockAt machine.tm
        (rowWidth bound machine original) original []
        position offset
    rw [show fiveFamilyPackedSixTrackChunk center offset.val =
      fivePackedActualOffsetObservation
        bound grid original position.val block offset.val from
      fivePackedActualOffsetObservation_chunk
        bound grid original position.val block offset]
    exact fiveFamilyPackedObservationPayload_valid
      bound machine original position offset
  · funext offset
    change
      fiveFamilyPackedObservationPayload
        (fiveFamilyPackedSixTrackChunk head offset.val) =
      pairedInputBlockAt machine.tm
        (rowWidth bound machine original) original []
        (0 : Position (rowWidth bound machine original)) offset
    rw [show fiveFamilyPackedSixTrackChunk head offset.val =
      fivePackedActualOffsetObservation
        bound grid original 0 block offset.val from
      fivePackedActualOffsetObservation_chunk
        bound grid original 0 block offset]
    exact fiveFamilyPackedObservationPayload_valid
      bound machine original (0 : Position
        (rowWidth bound machine original)) offset
  · funext offset
    change
      fiveFamilyPackedObservationRange
        (fiveFamilyPackedSixTrackChunk center offset.val) =
      phaseRangeBlockAt machine.tm
        (rowWidth bound machine original) position offset
    rw [show fiveFamilyPackedSixTrackChunk center offset.val =
      fivePackedActualOffsetObservation
        bound grid original position.val block offset.val from
      fivePackedActualOffsetObservation_chunk
        bound grid original position.val block offset]
    exact fiveFamilyPackedObservationRange_valid
      bound machine original position offset
  · funext offset
    change
      fiveFamilyPackedObservationRange
        (fiveFamilyPackedSixTrackChunk head offset.val) =
      phaseRangeBlockAt machine.tm
        (rowWidth bound machine original)
        (0 : Position (rowWidth bound machine original)) offset
    rw [show fiveFamilyPackedSixTrackChunk head offset.val =
      fivePackedActualOffsetObservation
        bound grid original 0 block offset.val from
      fivePackedActualOffsetObservation_chunk
        bound grid original 0 block offset]
    exact fiveFamilyPackedObservationRange_valid
      bound machine original (0 : Position
        (rowWidth bound machine original)) offset
  · funext offset
    change
      fiveFamilyPackedObservationBudget
        (fiveFamilyPackedSixTrackChunk center offset.val) =
      phaseBudgetBlockAt bound machine original position offset
    rw [show fiveFamilyPackedSixTrackChunk center offset.val =
      fivePackedActualOffsetObservation
        bound grid original position.val block offset.val from
      fivePackedActualOffsetObservation_chunk
        bound grid original position.val block offset]
    exact fiveFamilyPackedObservationBudget_valid
      bound machine original position offset
  · rfl


-- @@ L1980-1980 verbatim
end CNFFiveFamilyPackedInitialCellDecoderTM


-- @@ L1982-1982 verbatim
end GapCVP


-- @@ L1984-1984 verbatim
end
