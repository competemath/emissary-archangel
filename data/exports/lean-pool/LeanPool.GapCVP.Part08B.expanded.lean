/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part08A


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 08, continuation 02 -/


-- @@ L13-13 verbatim
public section


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open StateTransition (EvalsToInTime)


-- @@ L19-19 verbatim
open scoped BigOperators


-- @@ L21-21 verbatim
namespace GapCVP


-- @@ L23-23 verbatim
open GapCVP.TraceGolf (oneStep rebound)


-- @@ L25-25 verbatim
namespace CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity


-- @@ L27-27 verbatim
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation


-- @@ L29-29 verbatim
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding


-- @@ L31-31 verbatim
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM


-- @@ L33-33 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM


-- @@ L35-35 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM


-- @@ L37-37 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM


-- @@ L39-39 verbatim
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM


-- @@ L41-41 verbatim
open GapCVP.CNFFiveFamilyForbiddenWindowCoordinateTM


-- @@ L43-43 verbatim
open GapCVP.CNFFiveFamilyForbiddenWholeClauseValidity


-- @@ L45-45 verbatim
open GapCVP.CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM


-- @@ L47-47 verbatim
end CNFFiveFamilyIndependentFiveFamilyCatalogueSourceValidity


-- @@ L49-49 verbatim
namespace CNFAnnotatedSourceCompleteBubbleSortTM


-- @@ L51-51 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L52-52 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold

-- @@ L53-53 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L54-54 verbatim
open GapCVP.CNFTypedRecordWorkerTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM

-- @@ L55-55 verbatim
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM

-- @@ L56-56 verbatim
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert


-- @@ L58-62 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def annotatedCompleteBubbleSortState
    (pending count sorted : List Bool) : List Bool :=
  lengthPrefixedWord pending ++
    lengthPrefixedWord count ++ lengthPrefixedWord sorted


-- @@ L64-66 verbatim
private def flatAnnotatedCompleteBubblePending
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceFieldAt 0 input


-- @@ L68-71 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def flatAnnotatedCompleteBubbleCount
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceFieldAt 1 input


-- @@ L73-75 verbatim
private def flatAnnotatedCompleteBubbleSorted
    (input : List Bool) : List Bool :=
  flatAnnotatedSourceFieldAt 2 input


-- @@ L77-79 verbatim
private def annotatedCompleteBubbleNextCount
    (input : List Bool) : List Bool :=
  List.tail (flatAnnotatedCompleteBubbleCount input)


-- @@ L81-90 verbatim
private noncomputable def flatAnnotatedCompleteBubbleNextCountComputable :
    BitTM
      annotatedCompleteBubbleNextCount := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 1)
    dropHeadComputable
  change BitTM
    (fun input : List Bool =>
      List.tail (flatAnnotatedSourceFieldAt 1 input))
  exact physical


-- @@ L92-95 verbatim
private def annotatedCompleteBubbleInnerSeed
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (flatAnnotatedCompleteBubblePending input) ++
    lengthPrefixedWord []


-- @@ L97-109 verbatim
private noncomputable def flatAnnotatedCompleteBubbleInnerSeedComputable :
    BitTM
      annotatedCompleteBubbleInnerSeed := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    (annotatedSourceFieldAtComputable 0)
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable hpending
    (sourceFixedWordComputable (lengthPrefixedWord []))
  change BitTM
    (fun input : List Bool =>
      lengthPrefixedWord (flatAnnotatedSourceFieldAt 0 input) ++
        lengthPrefixedWord [])
  simpa only [Function.comp_def] using physical


-- @@ L111-114 verbatim
private def annotatedCompleteBubbleInnerInput
    (input : List Bool) : List Bool :=
  annotatedCompleteBubbleNextCount input ++
    false :: annotatedCompleteBubbleInnerSeed input


-- @@ L116-128 verbatim
private noncomputable def flatAnnotatedCompleteBubbleInnerInputComputable :
    BitTM
      annotatedCompleteBubbleInnerInput := by
  have htail := pointwiseAppendComputable
    (sourceFixedWordComputable [false])
    flatAnnotatedCompleteBubbleInnerSeedComputable
  have physical := pointwiseAppendComputable
    flatAnnotatedCompleteBubbleNextCountComputable htail
  change BitTM
    (fun input : List Bool =>
      annotatedCompleteBubbleNextCount input ++
        ([false] ++ annotatedCompleteBubbleInnerSeed input))
  simpa only [List.cons_append, List.nil_append] using physical


-- @@ L130-134 verbatim
private def annotatedCompleteBubbleInnerOutput : List Bool → List Bool :=
  boundedRecordFoldOutput
      (flatAnnotatedBubblePassStep
        annotatedCompleteTotalSourceComparison) ∘
    annotatedCompleteBubbleInnerInput


-- @@ L136-142 verbatim
private noncomputable def flatAnnotatedCompleteBubbleInnerOutputComputable :
    BitTM
      annotatedCompleteBubbleInnerOutput := by
  exact GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleInnerInputComputable
    (flatAnnotatedBubblePassFoldComputable
      flatAnnotatedCompleteTotalSourceComparisonComputable)


-- @@ L144-147 verbatim
private def annotatedCompleteBubbleNextPending
    (input : List Bool) : List Bool :=
  firstFieldContents
    (firstFieldSuffix (annotatedCompleteBubbleInnerOutput input))


-- @@ L149-161 verbatim
private noncomputable def flatAnnotatedCompleteBubbleNextPendingComputable :
    BitTM
      annotatedCompleteBubbleNextPending := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleInnerOutputComputable
    firstFieldSuffixComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    htail firstFieldContentsComputable
  change BitTM
    (fun input : List Bool =>
      firstFieldContents
        (firstFieldSuffix (annotatedCompleteBubbleInnerOutput input)))
  simpa only [Function.comp_def] using physical


-- @@ L163-166 verbatim
private def annotatedCompleteBubbleNextSorted
    (input : List Bool) : List Bool :=
  firstFieldContents (annotatedCompleteBubbleInnerOutput input) ++
    flatAnnotatedCompleteBubbleSorted input


-- @@ L168-181 verbatim
private noncomputable def flatAnnotatedCompleteBubbleNextSortedComputable :
    BitTM
      annotatedCompleteBubbleNextSorted := by
  have hselected := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleInnerOutputComputable
    firstFieldContentsComputable
  have physical := pointwiseAppendComputable hselected
    (annotatedSourceFieldAtComputable 2)
  change BitTM
    (fun input : List Bool =>
      firstFieldContents
        (annotatedCompleteBubbleInnerOutput input) ++
        flatAnnotatedSourceFieldAt 2 input)
  simpa only [Function.comp_def] using physical


-- @@ L183-188 verbatim
private def flatAnnotatedCompleteBubbleSortStep
    (input : List Bool) : List Bool :=
  annotatedCompleteBubbleSortState
    (annotatedCompleteBubbleNextPending input)
    (annotatedCompleteBubbleNextCount input)
    (annotatedCompleteBubbleNextSorted input)


-- @@ L190-217 verbatim
private noncomputable def flatAnnotatedCompleteBubbleSortStepComputable :
    BitTM
      flatAnnotatedCompleteBubbleSortStep := by
  have hpending := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleNextPendingComputable
    structuralPrefixWriterComputable
  have hcount := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleNextCountComputable
    structuralPrefixWriterComputable
  have hsorted := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleNextSortedComputable
    structuralPrefixWriterComputable
  have physical := pointwiseAppendComputable hpending
    (pointwiseAppendComputable hcount hsorted)
  have hequality :
      (fun input : List Bool =>
        lengthPrefixedWord
            (annotatedCompleteBubbleNextPending input) ++
          (lengthPrefixedWord
              (annotatedCompleteBubbleNextCount input) ++
            lengthPrefixedWord
              (annotatedCompleteBubbleNextSorted input))) =
        flatAnnotatedCompleteBubbleSortStep := by
    funext input
    simp only [flatAnnotatedCompleteBubbleSortStep, annotatedCompleteBubbleSortState,
        List.append_assoc]
  rw [← hequality]
  exact physical


-- @@ L219-227 verbatim
@[simp] private theorem flatAnnotatedCompleteBubbleSortState_pending
    (pending count sorted : List Bool) :
    flatAnnotatedCompleteBubblePending
        (annotatedCompleteBubbleSortState pending count sorted) =
      pending := by
  simp only [flatAnnotatedCompleteBubblePending, flatAnnotatedSourceFieldAt,
      flatAnnotatedSourceFieldTail,
      annotatedCompleteBubbleSortState, List.append_assoc, Function.iterate_zero, id_eq,
          firstFieldContents_valid]


-- @@ L229-239 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem flatAnnotatedCompleteBubbleSortState_count
    (pending count sorted : List Bool) :
    flatAnnotatedCompleteBubbleCount
        (annotatedCompleteBubbleSortState pending count sorted) =
      count := by
  simp only [flatAnnotatedCompleteBubbleCount, flatAnnotatedSourceFieldAt,
      flatAnnotatedSourceFieldTail,
      annotatedCompleteBubbleSortState, List.append_assoc, Function.iterate_one,
          firstFieldSuffix_valid,
      firstFieldContents_valid]


-- @@ L241-250 verbatim
@[simp] private theorem flatAnnotatedCompleteBubbleSortState_sorted
    (pending count sorted : List Bool) :
    flatAnnotatedCompleteBubbleSorted
        (annotatedCompleteBubbleSortState pending count sorted) =
      sorted := by
  simpa [flatAnnotatedCompleteBubbleSorted,
    annotatedCompleteBubbleSortState,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', List.append_assoc] using
    (firstFieldContents_valid sorted [])


-- @@ L252-269 verbatim
private theorem flatAnnotatedCompleteBubbleThreeFieldAccounting
    (input : List Bool) :
    2 * (flatAnnotatedCompleteBubblePending input).length +
      2 * (flatAnnotatedCompleteBubbleCount input).length +
      2 * (flatAnnotatedCompleteBubbleSorted input).length ≤
        input.length := by
  have hfirst := annotatedStructuralFieldAccounting input
  have hsecond := annotatedStructuralFieldAccounting
    (firstFieldSuffix input)
  have hthird := annotatedStructuralFieldAccounting
    (firstFieldSuffix (firstFieldSuffix input))
  simp only [flatAnnotatedCompleteBubblePending,
    flatAnnotatedCompleteBubbleCount,
    flatAnnotatedCompleteBubbleSorted,
    flatAnnotatedSourceFieldAt, flatAnnotatedSourceFieldTail,
    Function.iterate_succ_apply', Function.iterate_zero,
    id_eq] at *
  omega


-- @@ L271-303 verbatim
private theorem flatAnnotatedCompleteBubbleParsedPrefix_count_le
    (markers suffix : List Bool)
    (count : ℕ) (seed : List Bool)
    (hparse :
      parseUnaryBoundedFold (markers ++ false :: suffix) =
        some (count, seed)) :
    count ≤ markers.length := by
  induction markers generalizing count seed with
  | nil =>
      simp only [List.nil_append, parseUnaryBoundedFold, Option.some.injEq, Prod.mk.injEq]
          at hparse
      omega
  | cons bit remaining ih =>
      cases bit with
      | false =>
          simp only [List.cons_append, parseUnaryBoundedFold, Option.some.injEq, Prod.mk.injEq]
              at hparse
          omega
      | true =>
          cases hremaining :
              parseUnaryBoundedFold (remaining ++ false :: suffix) with
          | none =>
              simp only [List.cons_append, parseUnaryBoundedFold, hremaining, Option.map_none,
                  reduceCtorEq] at hparse
          | some parsed =>
              obtain ⟨remainingCount, remainingSeed⟩ := parsed
              have hbound :=
                ih remainingCount remainingSeed hremaining
              simp only [List.cons_append, parseUnaryBoundedFold, hremaining, Option.map_some,
                  Option.some.injEq,
                  Prod.mk.injEq] at hparse
              simp only [List.length_cons] at hbound ⊢
              omega


-- @@ L305-313 verbatim
private theorem flatAnnotatedCompleteBubbleInnerInput_length
    (input : List Bool) :
    (annotatedCompleteBubbleInnerInput input).length =
      (annotatedCompleteBubbleNextCount input).length +
        2 * (flatAnnotatedCompleteBubblePending input).length + 3 := by
  simp only [annotatedCompleteBubbleInnerInput, annotatedCompleteBubbleInnerSeed,
      List.length_append,
      List.length_cons, lengthPrefixedWord_length, List.length_nil, mul_zero, zero_add]
  omega


-- @@ L315-345 verbatim
private theorem flatAnnotatedCompleteBubbleInnerOutput_length_le
    (input : List Bool) :
    (annotatedCompleteBubbleInnerOutput input).length ≤
      (annotatedCompleteBubbleInnerInput input).length +
        4 * (flatAnnotatedCompleteBubbleCount input).length := by
  unfold annotatedCompleteBubbleInnerOutput
  rw [Function.comp_apply]
  cases hparse :
      parseUnaryBoundedFold
        (annotatedCompleteBubbleInnerInput input) with
  | none => simp only [boundedRecordFoldOutput, hparse, List.length_nil, zero_le]
  | some parsed =>
      obtain ⟨count, seed⟩ := parsed
      have hseed := parsedUnaryFold_seed_length_le
        (annotatedCompleteBubbleInnerInput input)
        count seed hparse
      have hprefix := flatAnnotatedCompleteBubbleParsedPrefix_count_le
        (annotatedCompleteBubbleNextCount input)
        (annotatedCompleteBubbleInnerSeed input)
        count seed (by
          simpa only [annotatedCompleteBubbleInnerInput] using hparse)
      have htail :
          (annotatedCompleteBubbleNextCount input).length ≤
            (flatAnnotatedCompleteBubbleCount input).length := by
        simp only [annotatedCompleteBubbleNextCount, List.length_tail, tsub_le_iff_right,
            le_add_iff_nonneg_right,
            zero_le]
      have hpass := flatAnnotatedBubblePassStep_iterate_length_le
        annotatedCompleteTotalSourceComparison seed count
      simp only [boundedRecordFoldOutput, hparse]
      omega


-- @@ L347-377 verbatim
private theorem flatAnnotatedCompleteBubbleSortStep_length_le
    (input : List Bool) :
    (flatAnnotatedCompleteBubbleSortStep input).length ≤
      input.length +
        5 * (flatAnnotatedCompleteBubbleCount input).length + 6 := by
  have hsource :=
    flatAnnotatedCompleteBubbleThreeFieldAccounting input
  change
    2 * (flatAnnotatedCompleteBubblePending input).length +
        2 * (flatAnnotatedCompleteBubbleCount input).length +
        2 * (flatAnnotatedSourceFieldAt 2 input).length ≤
      input.length at hsource
  have hinner :=
    flatAnnotatedCompleteBubbleInnerOutput_length_le input
  have hinnerLength :=
    flatAnnotatedCompleteBubbleInnerInput_length input
  have hfields := annotatedStructuralTwoFieldAccounting
    (annotatedCompleteBubbleInnerOutput input)
  have htail :
      (annotatedCompleteBubbleNextCount input).length ≤
        (flatAnnotatedCompleteBubbleCount input).length := by
    simp only [annotatedCompleteBubbleNextCount, List.length_tail, tsub_le_iff_right,
        le_add_iff_nonneg_right,
        zero_le]
  simp only [flatAnnotatedCompleteBubbleSortStep,
    annotatedCompleteBubbleSortState,
    annotatedCompleteBubbleNextPending,
    annotatedCompleteBubbleNextSorted,
    flatAnnotatedCompleteBubbleSorted,
    List.length_append, lengthPrefixedWord_length]
  omega


-- @@ L379-386 verbatim
@[simp] private theorem flatAnnotatedCompleteBubbleSortStep_count
    (input : List Bool) :
    flatAnnotatedCompleteBubbleCount
        (flatAnnotatedCompleteBubbleSortStep input) =
      List.tail (flatAnnotatedCompleteBubbleCount input) := by
  unfold flatAnnotatedCompleteBubbleSortStep
  rw [flatAnnotatedCompleteBubbleSortState_count]
  rfl


-- @@ L388-399 verbatim
private theorem flatAnnotatedCompleteBubbleSortStep_iterate_count_le
    (input : List Bool) (stage : ℕ) :
    (flatAnnotatedCompleteBubbleCount
      (((flatAnnotatedCompleteBubbleSortStep)^[stage]) input)).length ≤
      (flatAnnotatedCompleteBubbleCount input).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      rw [flatAnnotatedCompleteBubbleSortStep_count]
      simp only [List.length_tail]
      omega


-- @@ L401-423 verbatim
private theorem flatAnnotatedCompleteBubbleSortStep_iterate_length_le
    (input : List Bool) (stage : ℕ) :
    (((flatAnnotatedCompleteBubbleSortStep)^[stage]) input).length ≤
      input.length +
        stage * (5 * (flatAnnotatedCompleteBubbleCount input).length + 6) := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, zero_mul, add_zero, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := flatAnnotatedCompleteBubbleSortStep_length_le
        (((flatAnnotatedCompleteBubbleSortStep)^[stage]) input)
      have hcount :=
        flatAnnotatedCompleteBubbleSortStep_iterate_count_le input stage
      have hsuccessor :
          (stage + 1) *
              (5 * (flatAnnotatedCompleteBubbleCount input).length + 6) =
            stage *
                (5 * (flatAnnotatedCompleteBubbleCount input).length + 6) +
              (5 * (flatAnnotatedCompleteBubbleCount input).length + 6) :=
        Nat.succ_mul stage
          (5 * (flatAnnotatedCompleteBubbleCount input).length + 6)
      rw [hsuccessor]
      omega


-- @@ L425-442 verbatim
private theorem flatAnnotatedCompleteBubbleSort_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      flatAnnotatedCompleteBubbleSortStep
      (5 * Polynomial.X ^ 2 + 7 * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate :=
    flatAnnotatedCompleteBubbleSortStep_iterate_length_le seed stage
  have hfield :=
    flatAnnotatedCompleteBubbleThreeFieldAccounting seed
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
  nlinarith


-- @@ L444-450 verbatim
private noncomputable def flatAnnotatedCompleteBubbleSortFoldComputable :
    BitTM
      (boundedRecordFoldOutput flatAnnotatedCompleteBubbleSortStep) :=
  boundedDependentRecordFoldComputable
    flatAnnotatedCompleteBubbleSortStepComputable
    (5 * Polynomial.X ^ 2 + 7 * Polynomial.X)
    flatAnnotatedCompleteBubbleSort_polynomiallyBoundedFoldStates


-- @@ L452-452 verbatim
end CNFAnnotatedSourceCompleteBubbleSortTM


-- @@ L454-454 verbatim
namespace CNFAnnotatedSourceCompleteBubbleSortSourceCert


-- @@ L456-456 verbatim
open Turing GapCVP.CL GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L457-457 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold

-- @@ L458-458 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFAnnotatedSourceClausePairPreparationTM

-- @@ L459-459 verbatim
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM

-- @@ L460-460 verbatim
open GapCVP.CNFAnnotatedSourceCompleteFiniteSetComparatorSourceCert

-- @@ L461-461 verbatim
open GapCVP.CNFAnnotatedSourceCompleteBubbleSortTM


-- @@ L463-476 verbatim
private def flatAnnotatedOriginalBubblePass
    {T S : ℕ} (champion : Clause T S)
    (remaining emitted : List (Clause T S)) :
    Clause T S × List (Clause T S) :=
  match remaining with
  | [] => (champion, emitted)
  | next :: tail =>
      if Encodable.encode next < Encodable.encode champion then
        flatAnnotatedOriginalBubblePass champion tail
          (emitted ++ [next])
      else
        flatAnnotatedOriginalBubblePass next tail
          (emitted ++ [champion])
termination_by remaining.length


-- @@ L478-503 verbatim
private theorem flatAnnotatedBubblePassStep_iterate_originalClauseState
    {T S : ℕ} (champion : Clause T S)
    (remaining emitted : List (Clause T S)) :
    (((flatAnnotatedBubblePassStep
        annotatedCompleteTotalSourceComparison)^[remaining.length])
      (flatAnnotatedBubbleClauseState
        (champion :: remaining) emitted)) =
      flatAnnotatedBubbleClauseState
        [(flatAnnotatedOriginalBubblePass
          champion remaining emitted).1]
        (flatAnnotatedOriginalBubblePass
          champion remaining emitted).2 := by
  induction remaining generalizing champion emitted with
  | nil => simp only [List.length_nil, Function.iterate_zero, id_eq,
      flatAnnotatedOriginalBubblePass]
  | cons next tail ih =>
      simp only [List.length_cons, Function.iterate_succ_apply]
      rw [flatAnnotatedBubblePassStep_clauseState
        flatAnnotatedCompleteTotalSourceComparison_correct]
      by_cases horder : Encodable.encode next < Encodable.encode champion
      · simp only [horder, ↓reduceIte,
          flatAnnotatedOriginalBubblePass]
        exact ih champion (emitted ++ [next])
      · simp only [horder, ↓reduceIte,
          flatAnnotatedOriginalBubblePass]
        exact ih next (emitted ++ [champion])


-- @@ L505-524 verbatim
@[simp] private theorem flatAnnotatedOriginalBubblePass_emitted_length
    {T S : ℕ} (champion : Clause T S)
    (remaining emitted : List (Clause T S)) :
    (flatAnnotatedOriginalBubblePass
      champion remaining emitted).2.length =
      remaining.length + emitted.length := by
  induction remaining generalizing champion emitted with
  | nil => simp only [flatAnnotatedOriginalBubblePass, List.length_nil, zero_add]
  | cons next tail ih =>
      by_cases horder : Encodable.encode next < Encodable.encode champion
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        rw [ih]
        simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
        omega
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        rw [ih]
        simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
        omega


-- @@ L526-543 verbatim
private theorem flatAnnotatedCompleteBubbleInnerInput_originalClauseState
    {T S : ℕ} (champion : Clause T S)
    (remaining sorted : List (Clause T S)) :
    annotatedCompleteBubbleInnerInput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream
            (champion :: remaining))
          (List.replicate (champion :: remaining).length true)
          (flatAnnotatedBundledClauseStream sorted)) =
      unaryBoundedFoldWord remaining.length
        (flatAnnotatedBubbleClauseState
          (champion :: remaining) []) := by
  simp only [annotatedCompleteBubbleInnerInput, annotatedCompleteBubbleNextCount,
      flatAnnotatedBundledClauseStream, List.flatMap_cons, List.length_cons, List.replicate_succ,
      flatAnnotatedCompleteBubbleSortState_count, List.tail_cons, annotatedCompleteBubbleInnerSeed,
      flatAnnotatedCompleteBubbleSortState_pending, unaryBoundedFoldWord,
          flatAnnotatedBubbleClauseState,
      flatAnnotatedBubblePassState, List.flatMap_nil]


-- @@ L545-564 verbatim
private theorem flatAnnotatedCompleteBubbleInnerOutput_originalClauseState
    {T S : ℕ} (champion : Clause T S)
    (remaining sorted : List (Clause T S)) :
    annotatedCompleteBubbleInnerOutput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream
            (champion :: remaining))
          (List.replicate (champion :: remaining).length true)
          (flatAnnotatedBundledClauseStream sorted)) =
      flatAnnotatedBubbleClauseState
        [(flatAnnotatedOriginalBubblePass
          champion remaining []).1]
        (flatAnnotatedOriginalBubblePass
          champion remaining []).2 := by
  unfold annotatedCompleteBubbleInnerOutput
  rw [Function.comp_apply,
    flatAnnotatedCompleteBubbleInnerInput_originalClauseState]
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  exact flatAnnotatedBubblePassStep_iterate_originalClauseState
    champion remaining []


-- @@ L566-609 verbatim
private theorem flatAnnotatedCompleteBubbleSortStep_originalClauseState
    {T S : ℕ} (champion : Clause T S)
    (remaining sorted : List (Clause T S)) :
    flatAnnotatedCompleteBubbleSortStep
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream
            (champion :: remaining))
          (List.replicate (champion :: remaining).length true)
          (flatAnnotatedBundledClauseStream sorted)) =
      annotatedCompleteBubbleSortState
        (flatAnnotatedBundledClauseStream
          (flatAnnotatedOriginalBubblePass
            champion remaining []).2)
        (List.replicate remaining.length true)
        (flatAnnotatedBundledClauseStream
          ((flatAnnotatedOriginalBubblePass
            champion remaining []).1 :: sorted)) := by
  unfold flatAnnotatedCompleteBubbleSortStep
  simp only [annotatedCompleteBubbleNextPending,
    annotatedCompleteBubbleNextCount,
    annotatedCompleteBubbleNextSorted,
    flatAnnotatedCompleteBubbleSortState_count,
    flatAnnotatedCompleteBubbleSortState_sorted,
    flatAnnotatedCompleteBubbleInnerOutput_originalClauseState]
  have hpending :
      firstFieldContents
          (lengthPrefixedWord
            (flatAnnotatedBundledClauseStream
              (flatAnnotatedOriginalBubblePass
                champion remaining []).2)) =
        flatAnnotatedBundledClauseStream
          (flatAnnotatedOriginalBubblePass
            champion remaining []).2 := by
    simpa only [List.append_nil] using
        firstFieldContents_valid
          (flatAnnotatedBundledClauseStream (flatAnnotatedOriginalBubblePass champion remaining
              []).2) []
  simp only [flatAnnotatedBubbleClauseState,
    flatAnnotatedBubblePassState,
    firstFieldContents_valid, firstFieldSuffix_valid]
  rw [hpending]
  simp only [flatAnnotatedBundledClauseStream, List.length_cons, List.replicate_succ,
      List.tail_cons,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]


-- @@ L611-626 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def flatAnnotatedOriginalBubbleSortAux
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    List (Clause T S) :=
  match pending with
  | [] => sorted
  | champion :: remaining =>
      let result := flatAnnotatedOriginalBubblePass
        champion remaining []
      flatAnnotatedOriginalBubbleSortAux
        result.2 (result.1 :: sorted)
termination_by pending.length
decreasing_by
  simp only [flatAnnotatedOriginalBubblePass_emitted_length,
    List.length_nil, Nat.add_zero, List.length_cons]
  omega


-- @@ L628-669 verbatim
private theorem flatAnnotatedCompleteBubbleSortStep_iterate_originalClauseState
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    (((flatAnnotatedCompleteBubbleSortStep)^[pending.length])
      (annotatedCompleteBubbleSortState
        (flatAnnotatedBundledClauseStream pending)
        (List.replicate pending.length true)
        (flatAnnotatedBundledClauseStream sorted))) =
      annotatedCompleteBubbleSortState
        [] []
        (flatAnnotatedBundledClauseStream
          (flatAnnotatedOriginalBubbleSortAux pending sorted)) := by
  cases pending with
  | nil =>
      simp only [List.length_nil, flatAnnotatedBundledClauseStream, List.flatMap_nil,
          List.replicate_zero,
          Function.iterate_zero, id_eq, flatAnnotatedOriginalBubbleSortAux]
  | cons champion remaining =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have hfirst :=
        flatAnnotatedCompleteBubbleSortStep_originalClauseState
          champion remaining sorted
      rw [List.length_cons] at hfirst
      rw [hfirst]
      have hlength :
          (flatAnnotatedOriginalBubblePass
              champion remaining []).2.length = remaining.length := by
        simpa only [List.length_nil, Nat.add_zero] using
          flatAnnotatedOriginalBubblePass_emitted_length
            champion remaining []
      rw [← hlength]
      have hrecursive :=
        flatAnnotatedCompleteBubbleSortStep_iterate_originalClauseState
          (flatAnnotatedOriginalBubblePass
            champion remaining []).2
          ((flatAnnotatedOriginalBubblePass
            champion remaining []).1 :: sorted)
      simpa only [flatAnnotatedOriginalBubbleSortAux] using hrecursive
termination_by pending.length
decreasing_by
  simp only [flatAnnotatedOriginalBubblePass_emitted_length,
    List.length_nil, Nat.add_zero, List.length_cons]
  omega


-- @@ L671-685 verbatim
private theorem boundedRecordFoldOutput_flatAnnotatedCompleteBubbleSort
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    boundedRecordFoldOutput flatAnnotatedCompleteBubbleSortStep
        (unaryBoundedFoldWord pending.length
          (annotatedCompleteBubbleSortState
            (flatAnnotatedBundledClauseStream pending)
            (List.replicate pending.length true)
            (flatAnnotatedBundledClauseStream sorted))) =
      annotatedCompleteBubbleSortState
        [] []
        (flatAnnotatedBundledClauseStream
          (flatAnnotatedOriginalBubbleSortAux pending sorted)) := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  exact flatAnnotatedCompleteBubbleSortStep_iterate_originalClauseState
    pending sorted


-- @@ L687-716 verbatim
private theorem flatAnnotatedOriginalBubblePass_perm
    {T S : ℕ} (champion : Clause T S)
    (remaining emitted : List (Clause T S)) :
    ((flatAnnotatedOriginalBubblePass
          champion remaining emitted).1 ::
      (flatAnnotatedOriginalBubblePass
        champion remaining emitted).2).Perm
      (champion :: (remaining ++ emitted)) := by
  induction remaining generalizing champion emitted with
  | nil => simp only [flatAnnotatedOriginalBubblePass, List.nil_append, List.Perm.refl]
  | cons next tail ih =>
      by_cases horder : Encodable.encode next < Encodable.encode champion
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        have hpass := ih champion (emitted ++ [next])
        have hmove :
            (champion :: (tail ++ (emitted ++ [next]))).Perm
              (champion :: (next :: tail ++ emitted)) := by
          simpa only [List.cons_append, List.perm_cons, List.append_assoc] using
              (List.perm_append_singleton next (tail ++ emitted)).cons champion
        exact hpass.trans hmove
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        have hpass := ih next (emitted ++ [champion])
        have hmove :
            (next :: (tail ++ (emitted ++ [champion]))).Perm
              (champion :: (next :: tail ++ emitted)) := by
          simpa only [List.cons_append, List.append_assoc] using
              List.perm_append_singleton champion (next :: (tail ++ emitted))
        exact hpass.trans hmove


-- @@ L718-758 verbatim
private theorem flatAnnotatedOriginalBubblePass_champion_le
    {T S : ℕ} (champion : Clause T S)
    (remaining emitted : List (Clause T S))
    (record : Clause T S)
    (hrecord : record ∈ champion :: remaining) :
    Encodable.encode record ≤
      Encodable.encode
        (flatAnnotatedOriginalBubblePass
          champion remaining emitted).1 := by
  induction remaining generalizing champion emitted record with
  | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, flatAnnotatedOriginalBubblePass]
          at hrecord ⊢
      exact hrecord ▸ Nat.le_refl _
  | cons next tail ih =>
      by_cases horder : Encodable.encode next < Encodable.encode champion
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        simp only [List.mem_cons] at hrecord
        rcases hrecord with hchampion | hrest
        · subst record
          exact ih champion (emitted ++ [next]) champion
            (by simp only [List.mem_cons, true_or])
        · rcases hrest with hnext | htail
          · subst record
            exact Nat.le_trans (Nat.le_of_lt horder)
              (ih champion (emitted ++ [next]) champion (by simp only [List.mem_cons, true_or]))
          · exact ih champion (emitted ++ [next]) record
              (by simp only [List.mem_cons, htail, or_true])
      · simp only [flatAnnotatedOriginalBubblePass, horder,
          ↓reduceIte]
        simp only [List.mem_cons] at hrecord
        rcases hrecord with hchampion | hrest
        · subst record
          exact Nat.le_trans (Nat.le_of_not_gt horder)
            (ih next (emitted ++ [champion]) next (by simp only [List.mem_cons, true_or]))
        · rcases hrest with hnext | htail
          · subst record
            exact ih next (emitted ++ [champion]) next (by simp only [List.mem_cons, true_or])
          · exact ih next (emitted ++ [champion]) record
              (by simp only [List.mem_cons, htail, or_true])


-- @@ L760-794 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedOriginalBubbleSortAux_perm
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    (flatAnnotatedOriginalBubbleSortAux pending sorted).Perm
      (pending ++ sorted) := by
  cases pending with
  | nil => simp only [flatAnnotatedOriginalBubbleSortAux, List.nil_append, List.Perm.refl]
  | cons champion remaining =>
      have hpass :=
        flatAnnotatedOriginalBubblePass_perm
          champion remaining []
      simp only [List.append_nil] at hpass
      have hrecursive := flatAnnotatedOriginalBubbleSortAux_perm
        (flatAnnotatedOriginalBubblePass
          champion remaining []).2
        ((flatAnnotatedOriginalBubblePass
          champion remaining []).1 :: sorted)
      have hmiddle :
          ((flatAnnotatedOriginalBubblePass
              champion remaining []).2 ++
            (flatAnnotatedOriginalBubblePass
              champion remaining []).1 :: sorted).Perm
            (((flatAnnotatedOriginalBubblePass
              champion remaining []).1 ::
              (flatAnnotatedOriginalBubblePass
                champion remaining []).2) ++ sorted) := by
        exact List.perm_middle
      have hsource := hpass.append_right sorted
      simp only [flatAnnotatedOriginalBubbleSortAux]
      exact hrecursive.trans (hmiddle.trans hsource)
termination_by pending.length
decreasing_by
  simp only [flatAnnotatedOriginalBubblePass_emitted_length,
    List.length_nil, Nat.add_zero, List.length_cons]
  omega


-- @@ L796-854 verbatim
private theorem flatAnnotatedOriginalBubbleSortAux_pairwise
    {T S : ℕ} (pending sorted : List (Clause T S))
    (hsorted : sorted.Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second))
    (hbounded :
      ∀ first ∈ pending, ∀ second ∈ sorted,
        Encodable.encode first ≤ Encodable.encode second) :
    (flatAnnotatedOriginalBubbleSortAux pending sorted).Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second) := by
  cases pending with
  | nil => simpa only [flatAnnotatedOriginalBubbleSortAux] using hsorted
  | cons champion remaining =>
      have hpass :=
        flatAnnotatedOriginalBubblePass_perm
          champion remaining []
      simp only [List.append_nil] at hpass
      have hchampion :
          (flatAnnotatedOriginalBubblePass
            champion remaining []).1 ∈ champion :: remaining :=
        hpass.subset (by simp only [List.mem_cons, true_or])
      have hnewSorted :
          ((flatAnnotatedOriginalBubblePass
            champion remaining []).1 :: sorted).Pairwise
              (fun first second =>
                Encodable.encode first ≤ Encodable.encode second) := by
        apply List.pairwise_cons.mpr
        refine ⟨?_, hsorted⟩
        intro second hsecond
        exact hbounded _ hchampion second hsecond
      have hnewBounded :
          ∀ first ∈
            (flatAnnotatedOriginalBubblePass
              champion remaining []).2,
          ∀ second ∈
            (flatAnnotatedOriginalBubblePass
              champion remaining []).1 :: sorted,
            Encodable.encode first ≤ Encodable.encode second := by
        intro first hfirst second hsecond
        have horiginal : first ∈ champion :: remaining :=
          hpass.subset (List.mem_cons_of_mem _ hfirst)
        rcases List.mem_cons.mp hsecond with hselected | hsortedSecond
        · subst second
          exact flatAnnotatedOriginalBubblePass_champion_le
            champion remaining [] first horiginal
        · exact hbounded first horiginal second hsortedSecond
      simp only [flatAnnotatedOriginalBubbleSortAux]
      exact flatAnnotatedOriginalBubbleSortAux_pairwise
        (flatAnnotatedOriginalBubblePass
          champion remaining []).2
        ((flatAnnotatedOriginalBubblePass
          champion remaining []).1 :: sorted)
        hnewSorted hnewBounded
termination_by pending.length
decreasing_by
  simp_all only [flatAnnotatedOriginalBubblePass_emitted_length,
    List.length_nil, Nat.add_zero, List.length_cons]
  omega


-- @@ L856-864 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedOriginalBubbleSort_pairwise
    {T S : ℕ} (pending : List (Clause T S)) :
    (flatAnnotatedOriginalBubbleSortAux pending []).Pairwise
      (fun first second =>
        Encodable.encode first ≤ Encodable.encode second) := by
  apply flatAnnotatedOriginalBubbleSortAux_pairwise
  · simp only [List.Pairwise.nil]
  · simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]


-- @@ L866-868 verbatim
private def annotatedCompleteBubbleSortPreparedInput
    (input : List Bool) : List Bool :=
  flatAnnotatedCompleteBubbleCount input ++ false :: input


-- @@ L870-881 verbatim
private noncomputable def flatAnnotatedCompleteBubbleSortPreparedInputComputable :
    BitTM
      annotatedCompleteBubbleSortPreparedInput := by
  have htail := pointwiseAppendComputable
    (sourceFixedWordComputable [false])
    (Turing.idComputableInPolyTime bitEncoding)
  have physical := pointwiseAppendComputable
    (annotatedSourceFieldAtComputable 1) htail
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceFieldAt 1 input ++ false :: input)
  simpa only [id_eq, List.cons_append, List.nil_append] using physical


-- @@ L883-888 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def annotatedCompleteBubbleSortedSourceOutput :
    List Bool → List Bool :=
  flatAnnotatedCompleteBubbleSorted ∘
    boundedRecordFoldOutput flatAnnotatedCompleteBubbleSortStep ∘
      annotatedCompleteBubbleSortPreparedInput


-- @@ L890-904 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def flatAnnotatedCompleteBubbleSortedSourceComputable :
    BitTM
      annotatedCompleteBubbleSortedSourceOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    flatAnnotatedCompleteBubbleSortPreparedInputComputable
    flatAnnotatedCompleteBubbleSortFoldComputable
  have physical := GapCVP.TMComposition.computableInPolyTime
    hfold (annotatedSourceFieldAtComputable 2)
  change BitTM
    (fun input : List Bool =>
      flatAnnotatedSourceFieldAt 2
        (boundedRecordFoldOutput flatAnnotatedCompleteBubbleSortStep
          (annotatedCompleteBubbleSortPreparedInput input)))
  simpa only [Function.comp_def] using physical


-- @@ L906-919 verbatim
@[simp] private theorem flatAnnotatedCompleteBubbleSortPreparedInput_originalClauseState
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    annotatedCompleteBubbleSortPreparedInput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true)
          (flatAnnotatedBundledClauseStream sorted)) =
      unaryBoundedFoldWord pending.length
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true)
          (flatAnnotatedBundledClauseStream sorted)) := by
  simp only [annotatedCompleteBubbleSortPreparedInput, flatAnnotatedCompleteBubbleSortState_count,
      unaryBoundedFoldWord]


-- @@ L921-935 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem flatAnnotatedCompleteBubbleSortedSourceOutput_valid
    {T S : ℕ} (pending sorted : List (Clause T S)) :
    annotatedCompleteBubbleSortedSourceOutput
        (annotatedCompleteBubbleSortState
          (flatAnnotatedBundledClauseStream pending)
          (List.replicate pending.length true)
          (flatAnnotatedBundledClauseStream sorted)) =
      flatAnnotatedBundledClauseStream
        (flatAnnotatedOriginalBubbleSortAux pending sorted) := by
  unfold annotatedCompleteBubbleSortedSourceOutput
  rw [Function.comp_apply, Function.comp_apply,
    flatAnnotatedCompleteBubbleSortPreparedInput_originalClauseState,
    boundedRecordFoldOutput_flatAnnotatedCompleteBubbleSort,
    flatAnnotatedCompleteBubbleSortState_sorted]


-- @@ L937-937 verbatim
end CNFAnnotatedSourceCompleteBubbleSortSourceCert


-- @@ L939-939 verbatim
end GapCVP


-- @@ L941-941 verbatim
end
