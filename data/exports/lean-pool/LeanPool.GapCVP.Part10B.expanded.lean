/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part10A


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 10, continuation 02 -/


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
namespace SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM


-- @@ L27-27 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM


-- @@ L29-29 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L31-31 verbatim
end SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM


-- @@ L33-33 verbatim
namespace SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM


-- @@ L35-35 verbatim
open Turing GapCVP.SourceOriginalSourcePreservingTM

-- @@ L36-36 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

-- @@ L37-37 verbatim
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM


-- @@ L39-44 verbatim
/-- Prepend the equality marker for two computed words to the original input. -/
def sourceQaryMaskRankTaggedLowerLeftEqualitySelection
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (maskComputedWordEquality first second input).headD
      false :: input


-- @@ L46-75 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    sourceQaryMaskRankTaggedLowerLeftEqualitySelectionComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (sourceQaryMaskRankTaggedLowerLeftEqualitySelection
        first second) := by
  have hmarker := maskComputedWordEqualityComputable
    hfirst hsecond
  have hpreserved := originalSourcePreservingComputable hmarker
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved keepFirstDropSecondComputable
  have hequality :
      (fun input : List Bool => keepFirstDropSecondWord
        (originalSourcePreservingOutput
          (maskComputedWordEquality first second)
          input)) =
        sourceQaryMaskRankTaggedLowerLeftEqualitySelection
          first second := by
    funext input
    unfold originalSourcePreservingOutput
    rw [sourceQaryMaskSquareComputedWordEquality_valid]
    simp only [keepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons,
        sourceQaryMaskRankTaggedLowerLeftEqualitySelection,
            sourceQaryMaskSquareComputedWordEquality_valid,
        List.headD_eq_head?_getD, List.head?_cons, Option.getD_some]
  rw [← hequality]
  exact hphysical


-- @@ L77-77 verbatim
end SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM


-- @@ L79-79 verbatim
namespace SourceNormalizedVariableRankScanTM


-- @@ L81-81 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.FormulaSemanticCert

-- @@ L82-82 verbatim
open GapCVP.SourceTotalStructuralDecoder GapCVP.SourceFormulaStructuralDecoder

-- @@ L83-83 verbatim
open GapCVP.SourceVariableFormulaDecoder GapCVP.OutputPolynomialCompositionClosure

-- @@ L84-84 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM

-- @@ L85-85 verbatim
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L86-86 verbatim
open GapCVP.SourceIndexedClauseLookupTM GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L87-87 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

-- @@ L88-88 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM

-- @@ L89-89 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFGuardedFiveFamilyTagDispatchTM

-- @@ L90-90 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L92-93 verbatim
private def sourceNormalizedVariableScanTargetWord : List Bool → List Bool :=
  firstFieldContents


-- @@ L95-98 verbatim
private noncomputable def sourceNormalizedVariableScanTargetWordComputable :
    BitTM
      sourceNormalizedVariableScanTargetWord :=
  firstFieldContentsComputable


-- @@ L100-101 verbatim
private def sourceNormalizedVariableScanCounterWord : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix


-- @@ L103-107 verbatim
private noncomputable def sourceNormalizedVariableScanCounterWordComputable :
    BitTM
      sourceNormalizedVariableScanCounterWord :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L109-110 verbatim
private def sourceNormalizedVariableScanPending : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L112-116 verbatim
private noncomputable def sourceNormalizedVariableScanPendingComputable :
    BitTM
      sourceNormalizedVariableScanPending :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable


-- @@ L118-119 verbatim
private def sourceNormalizedVariableScanCurrentWord : List Bool → List Bool :=
  firstFieldContents ∘ sourceNormalizedVariableScanPending


-- @@ L121-126 verbatim
private noncomputable def sourceNormalizedVariableScanCurrentWordComputable :
    BitTM
      sourceNormalizedVariableScanCurrentWord :=
  GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableScanPendingComputable
    firstFieldContentsComputable


-- @@ L128-131 verbatim
private def sourceNormalizedVariableScanEquality : List Bool → List Bool :=
  maskComputedWordEquality
    sourceNormalizedVariableScanTargetWord
    sourceNormalizedVariableScanCurrentWord


-- @@ L133-138 verbatim
private noncomputable def sourceNormalizedVariableScanEqualityComputable :
    BitTM
      sourceNormalizedVariableScanEquality :=
  maskComputedWordEqualityComputable
    sourceNormalizedVariableScanTargetWordComputable
    sourceNormalizedVariableScanCurrentWordComputable


-- @@ L140-146 verbatim
private def sourceNormalizedVariableScanAdvance
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (sourceNormalizedVariableScanTargetWord input) ++
    (lengthPrefixedWord
      (true :: sourceNormalizedVariableScanCounterWord input) ++
      literalSuffix (sourceNormalizedVariableScanPending input))


-- @@ L148-162 verbatim
private noncomputable def sourceNormalizedVariableScanAdvanceComputable :
    BitTM
      sourceNormalizedVariableScanAdvance := by
  have htarget := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableScanTargetWordComputable
    structuralPrefixWriterComputable
  have hcounterBit := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableScanCounterWordComputable
    (prependBitComputable true)
  have hcounter := GapCVP.TMComposition.computableInPolyTime
    hcounterBit structuralPrefixWriterComputable
  have hpending := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableScanPendingComputable literalSuffixComputable
  exact pointwiseAppendComputable htarget
    (pointwiseAppendComputable hcounter hpending)


-- @@ L164-166 verbatim
private def sourceNormalizedVariableScanEqualitySelection
    (input : List Bool) : List Bool :=
  (sourceNormalizedVariableScanEquality input).headD false :: input


-- @@ L168-173 verbatim
private noncomputable def sourceNormalizedVariableScanEqualitySelectionComputable :
    BitTM
      sourceNormalizedVariableScanEqualitySelection :=
  sourceQaryMaskRankTaggedLowerLeftEqualitySelectionComputable
    sourceNormalizedVariableScanTargetWordComputable
    sourceNormalizedVariableScanCurrentWordComputable


-- @@ L175-176 verbatim
private def sourceNormalizedVariableScanMismatchMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput sourceNormalizedVariableScanEquality


-- @@ L178-182 verbatim
private noncomputable def sourceNormalizedVariableScanMismatchMarkerComputable :
    BitTM
      sourceNormalizedVariableScanMismatchMarker :=
  fourFamilyBooleanNotOutputComputable
    sourceNormalizedVariableScanEqualityComputable


-- @@ L184-186 verbatim
private def sourceNormalizedVariableScanMismatchSelection
    (input : List Bool) : List Bool :=
  (sourceNormalizedVariableScanMismatchMarker input).headD false :: input


-- @@ L188-222 verbatim
private noncomputable def sourceNormalizedVariableScanMismatchSelectionComputable :
    BitTM
      sourceNormalizedVariableScanMismatchSelection := by
  have hpreserved := originalSourcePreservingComputable
    sourceNormalizedVariableScanMismatchMarkerComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved keepFirstDropSecondComputable
  have hequality :
      (fun input : List Bool => keepFirstDropSecondWord
        (originalSourcePreservingOutput
          sourceNormalizedVariableScanMismatchMarker input)) =
        sourceNormalizedVariableScanMismatchSelection := by
    funext input
    unfold originalSourcePreservingOutput
      sourceNormalizedVariableScanMismatchMarker
      sourceNormalizedVariableScanEquality
    rw [fourFamilyBooleanNotOutput_bit
      (maskComputedWordEquality
        sourceNormalizedVariableScanTargetWord
        sourceNormalizedVariableScanCurrentWord)
      input
      (decide (sourceNormalizedVariableScanTargetWord input =
        sourceNormalizedVariableScanCurrentWord input))
      (sourceQaryMaskSquareComputedWordEquality_valid
        sourceNormalizedVariableScanTargetWord
        sourceNormalizedVariableScanCurrentWord input)]
    simp only [keepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons,
        sourceNormalizedVariableScanMismatchSelection, sourceNormalizedVariableScanMismatchMarker,
        sourceFourFamilyBooleanNotOutput, sourceNormalizedVariableScanEquality,
            Function.comp_apply,
        sourceQaryMaskSquareComputedWordEquality_valid, sourceFourFamilyBooleanNotWord_bit,
            List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some]
  rw [← hequality]
  exact hphysical


-- @@ L224-228 verbatim
private def sourceNormalizedVariableScanFoundBranch
    (input : List Bool) : List Bool :=
  if (sourceNormalizedVariableScanEquality input).headD false then
    input
  else []


-- @@ L230-235 verbatim
private noncomputable def sourceNormalizedVariableScanFoundBranchComputable :
    BitTM
      sourceNormalizedVariableScanFoundBranch :=
  sourcePreservingConditionalComputable
    sourceNormalizedVariableScanEqualitySelectionComputable
    (Turing.idComputableInPolyTime bitEncoding) []


-- @@ L237-241 verbatim
private def sourceNormalizedVariableScanAdvanceBranch
    (input : List Bool) : List Bool :=
  if (sourceNormalizedVariableScanMismatchMarker input).headD false then
    sourceNormalizedVariableScanAdvance input
  else []


-- @@ L243-248 verbatim
private noncomputable def sourceNormalizedVariableScanAdvanceBranchComputable :
    BitTM
      sourceNormalizedVariableScanAdvanceBranch :=
  sourcePreservingConditionalComputable
    sourceNormalizedVariableScanMismatchSelectionComputable
    sourceNormalizedVariableScanAdvanceComputable []


-- @@ L250-253 verbatim
private def sourceNormalizedVariableScanStep
    (input : List Bool) : List Bool :=
  sourceNormalizedVariableScanFoundBranch input ++
    sourceNormalizedVariableScanAdvanceBranch input


-- @@ L255-260 verbatim
private noncomputable def sourceNormalizedVariableScanStepComputable :
    BitTM
      sourceNormalizedVariableScanStep :=
  pointwiseAppendComputable
    sourceNormalizedVariableScanFoundBranchComputable
    sourceNormalizedVariableScanAdvanceBranchComputable


-- @@ L262-286 verbatim
private theorem sourceNormalizedVariableScanStep_eq
    (input : List Bool) :
    sourceNormalizedVariableScanStep input =
      if sourceNormalizedVariableScanTargetWord input =
          sourceNormalizedVariableScanCurrentWord input then
        input
      else sourceNormalizedVariableScanAdvance input := by
  unfold sourceNormalizedVariableScanStep
    sourceNormalizedVariableScanFoundBranch
    sourceNormalizedVariableScanAdvanceBranch
    sourceNormalizedVariableScanMismatchMarker
    sourceNormalizedVariableScanEquality
  rw [sourceQaryMaskSquareComputedWordEquality_valid]
  by_cases hequality : sourceNormalizedVariableScanTargetWord input =
      sourceNormalizedVariableScanCurrentWord input
  · simp only [hequality, decide_true, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      ↓reduceIte,
        sourceFourFamilyBooleanNotOutput, Function.comp_apply,
            sourceQaryMaskSquareComputedWordEquality_valid,
        sourceFourFamilyBooleanNotWord_bit, Bool.not_true, Bool.false_eq_true, List.append_nil]
  · simp only [hequality, decide_false, List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some,
        Bool.false_eq_true, ↓reduceIte, sourceFourFamilyBooleanNotOutput, Function.comp_apply,
        sourceQaryMaskSquareComputedWordEquality_valid, sourceFourFamilyBooleanNotWord_bit,
            Bool.not_false, List.nil_append]


-- @@ L288-292 verbatim
theorem sourceNormalizedVariableScanStructuralFieldAccounting
    (input : List Bool) :
    2 * (firstFieldContents input).length +
      (firstFieldSuffix input).length ≤ input.length := by
  exact GapCVP.CNFAnnotatedSourceClauseBubblePassTM.annotatedStructuralFieldAccounting input


-- @@ L294-309 verbatim
private theorem sourceNormalizedVariableScanAdvance_length_le
    (input : List Bool) :
    (sourceNormalizedVariableScanAdvance input).length ≤
      input.length + 4 := by
  have htarget := sourceNormalizedVariableScanStructuralFieldAccounting input
  have hcounter := sourceNormalizedVariableScanStructuralFieldAccounting
    (firstFieldSuffix input)
  have hpending := sourceOriginalIndexedLiteralSuffix_length_le
    (firstFieldSuffix (firstFieldSuffix input))
  unfold sourceNormalizedVariableScanAdvance
    sourceNormalizedVariableScanTargetWord
    sourceNormalizedVariableScanCounterWord
    sourceNormalizedVariableScanPending
  simp only [Function.comp_apply, List.length_append,
    lengthPrefixedWord_length, List.length_cons]
  omega


-- @@ L311-318 verbatim
private theorem sourceNormalizedVariableScanStep_length_le
    (input : List Bool) :
    (sourceNormalizedVariableScanStep input).length ≤
      input.length + 4 := by
  rw [sourceNormalizedVariableScanStep_eq]
  split_ifs
  · omega
  · exact sourceNormalizedVariableScanAdvance_length_le input


-- @@ L320-344 verbatim
private theorem sourceNormalizedVariableScanStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      sourceNormalizedVariableScanStep (5 * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate : ∀ number : ℕ,
      ((sourceNormalizedVariableScanStep^[number]) seed).length ≤
        seed.length + 4 * number := by
    intro number
    induction number with
    | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
    | succ number ih =>
        rw [Function.iterate_succ_apply']
        have hnext := sourceNormalizedVariableScanStep_length_le
          ((sourceNormalizedVariableScanStep^[number]) seed)
        omega
  have hstate := hiterate stage
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega


-- @@ L346-352 verbatim
private noncomputable def sourceNormalizedVariableScanFoldComputable :
    BitTM
      (boundedRecordFoldOutput sourceNormalizedVariableScanStep) :=
  boundedDependentRecordFoldComputable
    sourceNormalizedVariableScanStepComputable
    (5 * Polynomial.X)
    sourceNormalizedVariableScanStep_polynomiallyBoundedFoldStates


-- @@ L354-358 verbatim
private def sourceNormalizedVariableScanState
    (target : List Bool) (counter : ℕ)
    (pending : List Bool) : List Bool :=
  lengthPrefixedWord target ++
    (lengthPrefixedWord (List.replicate counter true) ++ pending)


-- @@ L360-385 verbatim
private theorem sourceNormalizedVariableScanStep_literal
    (target : List Bool) (counter : ℕ)
    (literal : Literal) (pending : List Bool) :
    sourceNormalizedVariableScanStep
        (sourceNormalizedVariableScanState target counter
          (encodeLiteral literal ++ pending)) =
      if target = Computability.encodeNat literal.1 then
        sourceNormalizedVariableScanState target counter
          (encodeLiteral literal ++ pending)
      else
        sourceNormalizedVariableScanState target (counter + 1)
          pending := by
  have hcurrent :
      firstFieldContents (encodeLiteral literal ++ pending) =
        Computability.encodeNat literal.1 := by
    simp only [encodeLiteral, List.append_assoc, List.cons_append, List.nil_append,
        firstFieldContents_valid]
  have hskip :
      literalSuffix (encodeLiteral literal ++ pending) = pending :=
    literalSuffix_valid literal pending
  rw [sourceNormalizedVariableScanStep_eq]
  simp only [sourceNormalizedVariableScanTargetWord, sourceNormalizedVariableScanState,
      firstFieldContents_valid, sourceNormalizedVariableScanCurrentWord,
          sourceNormalizedVariableScanPending,
      Function.comp_apply, firstFieldSuffix_valid, hcurrent, sourceNormalizedVariableScanAdvance,
      sourceNormalizedVariableScanCounterWord, hskip, List.replicate_succ]


-- @@ L387-395 verbatim
private theorem sourceNormalizedVariableScanStep_iterate_fixed
    (state : List Bool)
    (hfixed : sourceNormalizedVariableScanStep state = state)
    (count : ℕ) :
    ((sourceNormalizedVariableScanStep^[count]) state) = state := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, hfixed, ih]


-- @@ L397-447 verbatim
private theorem sourceNormalizedVariableScanLiteralCounter_valid
    (target counter : ℕ) (literals : List Literal) :
    sourceNormalizedVariableScanCounterWord
        (((sourceNormalizedVariableScanStep^[literals.length])
          (sourceNormalizedVariableScanState
            (Computability.encodeNat target) counter
            (literals.flatMap encodeLiteral)))) =
      List.replicate
        (counter + (literals.map Prod.fst).idxOf target) true := by
  induction literals generalizing counter with
  | nil =>
      simp only [List.length_nil, List.flatMap_nil,
        Function.iterate_zero, id_eq, List.map_nil,
        List.idxOf_nil, Nat.add_zero]
      change firstFieldContents
        (firstFieldSuffix
          (lengthPrefixedWord (Computability.encodeNat target) ++
            (lengthPrefixedWord (List.replicate counter true) ++ []))) =
        List.replicate counter true
      rw [firstFieldSuffix_valid]
      simpa only [List.append_nil] using (firstFieldContents_valid (List.replicate counter true)
          [])
  | cons literal remaining ih =>
      simp only [List.length_cons, List.flatMap_cons]
      rw [Function.iterate_succ_apply,
        sourceNormalizedVariableScanStep_literal]
      by_cases hequality :
          Computability.encodeNat target =
            Computability.encodeNat literal.1
      · have hvalue : target = literal.1 := by
          simpa only [Computability.decode_encodeNat] using congrArg Computability.decodeNat
              hequality
        rw [ite_eq_left hequality]
        have hfixed := sourceNormalizedVariableScanStep_literal
          (Computability.encodeNat target) counter literal
          (remaining.flatMap encodeLiteral)
        rw [ite_eq_left hequality] at hfixed
        rw [sourceNormalizedVariableScanStep_iterate_fixed _ hfixed]
        simp only [sourceNormalizedVariableScanCounterWord, sourceNormalizedVariableScanState,
            hvalue,
            Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid, List.map_cons,
                List.idxOf_cons_self,
            add_zero]
      · have hvalue : target ≠ literal.1 := by
          intro hequal
          exact hequality (congrArg Computability.encodeNat hequal)
        have hreverse : literal.1 ≠ target := Ne.symm hvalue
        rw [ite_eq_right hequality, ih]
        rw [List.map_cons, List.idxOf_cons_ne _ hreverse]
        congr 1
        omega


-- @@ L449-453 verbatim
/-- GapCVP reduction support. -/
def sourceNormalizedVariableLiteralList
    (formula : ThreeCNF) : List Literal :=
  formula.flatMap (fun clause =>
    [clause 0, clause 1, clause 2])


-- @@ L455-470 verbatim
private theorem sourceNormalizedVariableLiteralList_stream
    (formula : ThreeCNF) :
    (sourceNormalizedVariableLiteralList formula).flatMap
        encodeLiteral =
      formula.flatMap encodeThreeClause := by
  induction formula with
  | nil => rfl
  | cons clause remaining ih =>
      simpa only [sourceNormalizedVariableLiteralList, Fin.isValue, List.flatMap_cons,
          List.cons_append,
          List.nil_append, encodeThreeClause, List.append_assoc, List.append_cancel_left_eq] using
          congrArg
            (fun suffix : List Bool =>
              encodeLiteral (clause 0) ++ encodeLiteral (clause 1) ++ encodeLiteral (clause 2) ++
                  suffix)
            ih


-- @@ L472-484 verbatim
private theorem sourceNormalizedVariableLiteralList_length
    (formula : ThreeCNF) :
    (sourceNormalizedVariableLiteralList formula).length =
      3 * formula.length := by
  induction formula with
  | nil => rfl
  | cons clause remaining ih =>
      simp only [sourceNormalizedVariableLiteralList, Fin.isValue, List.length_flatMap,
          List.length_cons,
          List.length_nil, zero_add, Nat.reduceAdd, List.map_const', List.sum_replicate,
              smul_eq_mul, List.flatMap_cons,
          List.cons_append, List.nil_append] at ih ⊢
      omega


-- @@ L486-492 verbatim
theorem sourceNormalizedVariableLiteralList_variables
    (formula : ThreeCNF) :
    (sourceNormalizedVariableLiteralList formula).map Prod.fst =
      formulaVariables formula := by
  simp only [sourceNormalizedVariableLiteralList, Fin.isValue, List.map_flatMap, List.map_cons,
      List.map_nil,
      formulaVariables]


-- @@ L494-498 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourceNormalizedVariableRankQuery
    (variableIndex : ℕ) (formula : ThreeCNF) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat variableIndex) ++
    encodeThreeCNF formula


-- @@ L500-501 verbatim
private def sourceNormalizedVariableRankOriginalSource : List Bool → List Bool :=
  firstFieldSuffix


-- @@ L503-506 verbatim
private noncomputable def sourceNormalizedVariableRankOriginalSourceComputable :
    BitTM
      sourceNormalizedVariableRankOriginalSource :=
  firstFieldSuffixComputable


-- @@ L508-509 verbatim
private def sourceNormalizedVariableRankFormulaBody : List Bool → List Bool :=
  firstFieldSuffix ∘ sourceNormalizedVariableRankOriginalSource


-- @@ L511-516 verbatim
private noncomputable def sourceNormalizedVariableRankFormulaBodyComputable :
    BitTM
      sourceNormalizedVariableRankFormulaBody :=
  GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableRankOriginalSourceComputable
    firstFieldSuffixComputable


-- @@ L518-521 verbatim
private def sourceNormalizedVariableRankClauseCount
    (input : List Bool) : List Bool :=
  (variableClauseBodyOutput
    (sourceNormalizedVariableRankFormulaBody input)).tail


-- @@ L523-530 verbatim
private noncomputable def sourceNormalizedVariableRankClauseCountComputable :
    BitTM
      sourceNormalizedVariableRankClauseCount := by
  have hbody := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableRankFormulaBodyComputable
    variableClauseBodyComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hbody dropHeadComputable


-- @@ L532-536 verbatim
private def sourceNormalizedVariableRankLiteralCount
    (input : List Bool) : List Bool :=
  sourceNormalizedVariableRankClauseCount input ++
    (sourceNormalizedVariableRankClauseCount input ++
      sourceNormalizedVariableRankClauseCount input)


-- @@ L538-545 verbatim
private noncomputable def sourceNormalizedVariableRankLiteralCountComputable :
    BitTM
      sourceNormalizedVariableRankLiteralCount :=
  pointwiseAppendComputable
    sourceNormalizedVariableRankClauseCountComputable
    (pointwiseAppendComputable
      sourceNormalizedVariableRankClauseCountComputable
      sourceNormalizedVariableRankClauseCountComputable)


-- @@ L547-551 verbatim
private def sourceNormalizedVariableRankSeed
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input) ++
    (lengthPrefixedWord [] ++
      sourceNormalizedVariableRankFormulaBody input)


-- @@ L553-561 verbatim
private noncomputable def sourceNormalizedVariableRankSeedComputable :
    BitTM
      sourceNormalizedVariableRankSeed := by
  have htarget := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  have hpending := pointwiseAppendComputable
    (sourceFixedWordComputable (lengthPrefixedWord []))
    sourceNormalizedVariableRankFormulaBodyComputable
  exact pointwiseAppendComputable htarget hpending


-- @@ L563-566 verbatim
private def sourceNormalizedVariableRankScanPreparation
    (input : List Bool) : List Bool :=
  sourceNormalizedVariableRankLiteralCount input ++
    false :: sourceNormalizedVariableRankSeed input


-- @@ L568-575 verbatim
private noncomputable def sourceNormalizedVariableRankScanPreparationComputable :
    BitTM
      sourceNormalizedVariableRankScanPreparation := by
  have hseed := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableRankSeedComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    sourceNormalizedVariableRankLiteralCountComputable hseed


-- @@ L577-581 verbatim
/-- GapCVP reduction support. -/
def sourceNormalizedVariableRankOutput : List Bool → List Bool :=
  sourceNormalizedVariableScanCounterWord ∘
    boundedRecordFoldOutput sourceNormalizedVariableScanStep ∘
      sourceNormalizedVariableRankScanPreparation


-- @@ L583-591 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceNormalizedVariableRankComputable :
    BitTM
      sourceNormalizedVariableRankOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    sourceNormalizedVariableRankScanPreparationComputable
    sourceNormalizedVariableScanFoldComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hfold sourceNormalizedVariableScanCounterWordComputable


-- @@ L593-612 verbatim
private theorem sourceNormalizedVariableRankScanPreparation_valid
    (variableIndex : ℕ) (formula : ThreeCNF) :
    sourceNormalizedVariableRankScanPreparation
        (sourceNormalizedVariableRankQuery variableIndex formula) =
      unaryBoundedFoldWord (3 * formula.length)
        (sourceNormalizedVariableScanState
          (Computability.encodeNat variableIndex) 0
          (formula.flatMap encodeThreeClause)) := by
  simp only [sourceNormalizedVariableRankScanPreparation, sourceNormalizedVariableRankLiteralCount,
      sourceNormalizedVariableRankClauseCount, sourceNormalizedVariableRankFormulaBody,
      sourceNormalizedVariableRankOriginalSource, sourceNormalizedVariableRankQuery,
          Function.comp_apply,
      firstFieldSuffix_valid, firstFieldSuffix_encodeThreeCNF, variableClauseBodyOutput_valid,
          List.tail_cons,
      List.replicate_append_replicate, sourceNormalizedVariableRankSeed, firstFieldContents_valid,
          unaryBoundedFoldWord,
      sourceNormalizedVariableScanState, List.replicate_zero, List.append_cancel_right_eq,
          List.replicate_inj,
      Nat.add_eq_zero_iff, List.length_eq_zero_iff, and_self, or_true, and_true]
  omega


-- @@ L614-627 verbatim
theorem sourceNormalizedVariableRankOutput_valid
    (variableIndex : ℕ) (formula : ThreeCNF) :
    sourceNormalizedVariableRankOutput
        (sourceNormalizedVariableRankQuery variableIndex formula) =
      List.replicate (variableRank formula variableIndex) true := by
  unfold sourceNormalizedVariableRankOutput
  rw [Function.comp_apply, Function.comp_apply,
    sourceNormalizedVariableRankScanPreparation_valid]
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [← sourceNormalizedVariableLiteralList_stream formula]
  rw [← sourceNormalizedVariableLiteralList_length formula]
  rw [sourceNormalizedVariableScanLiteralCounter_valid]
  rw [sourceNormalizedVariableLiteralList_variables]
  simp only [zero_add, variableRank]


-- @@ L629-629 verbatim
end SourceNormalizedVariableRankScanTM


-- @@ L631-631 verbatim
namespace BinaryCompactSourceFirstOccurrenceTM


-- @@ L633-633 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder

-- @@ L634-634 verbatim
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold

-- @@ L635-635 verbatim
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceIndexedClauseLookupTM

-- @@ L636-636 verbatim
open GapCVP.SourceNormalizedVariableRankScanTM

-- @@ L637-637 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

-- @@ L638-638 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedLowerLeftSourceTM

-- @@ L639-639 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CLStructuralPrefixWriter

-- @@ L640-640 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryDimensionTM


-- @@ L642-644 verbatim
/-- GapCVP reduction support. -/
def compactFirstOccurrenceCounter : List Bool → List Bool :=
  firstFieldContents


-- @@ L646-650 verbatim
/-- GapCVP reduction support. -/
noncomputable def compactFirstOccurrenceCounterComputable :
    BitTM
      compactFirstOccurrenceCounter :=
  firstFieldContentsComputable


-- @@ L652-653 verbatim
private def compactFirstOccurrenceOrdinalSuffix : List Bool → List Bool :=
  firstFieldSuffix


-- @@ L655-658 verbatim
private noncomputable def compactFirstOccurrenceOrdinalSuffixComputable :
    BitTM
      compactFirstOccurrenceOrdinalSuffix :=
  firstFieldSuffixComputable


-- @@ L660-661 verbatim
private def compactFirstOccurrenceOrdinal : List Bool → List Bool :=
  firstFieldContents ∘ compactFirstOccurrenceOrdinalSuffix


-- @@ L663-668 verbatim
private noncomputable def compactFirstOccurrenceOrdinalComputable :
    BitTM
      compactFirstOccurrenceOrdinal :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceOrdinalSuffixComputable
    firstFieldContentsComputable


-- @@ L670-671 verbatim
private def compactFirstOccurrencePendingSuffix : List Bool → List Bool :=
  firstFieldSuffix ∘ compactFirstOccurrenceOrdinalSuffix


-- @@ L673-678 verbatim
private noncomputable def compactFirstOccurrencePendingSuffixComputable :
    BitTM
      compactFirstOccurrencePendingSuffix :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceOrdinalSuffixComputable
    firstFieldSuffixComputable


-- @@ L680-681 verbatim
private def compactFirstOccurrencePending : List Bool → List Bool :=
  firstFieldContents ∘ compactFirstOccurrencePendingSuffix


-- @@ L683-688 verbatim
private noncomputable def compactFirstOccurrencePendingComputable :
    BitTM
      compactFirstOccurrencePending :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrencePendingSuffixComputable
    firstFieldContentsComputable


-- @@ L690-691 verbatim
private def compactFirstOccurrenceOriginalSource : List Bool → List Bool :=
  firstFieldSuffix ∘ compactFirstOccurrencePendingSuffix


-- @@ L693-698 verbatim
private noncomputable def compactFirstOccurrenceOriginalSourceComputable :
    BitTM
      compactFirstOccurrenceOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrencePendingSuffixComputable
    firstFieldSuffixComputable


-- @@ L700-701 verbatim
private def compactFirstOccurrenceCurrentVariable : List Bool → List Bool :=
  firstFieldContents ∘ compactFirstOccurrencePending


-- @@ L703-708 verbatim
private noncomputable def compactFirstOccurrenceCurrentVariableComputable :
    BitTM
      compactFirstOccurrenceCurrentVariable :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrencePendingComputable
    firstFieldContentsComputable


-- @@ L710-713 verbatim
private def compactFirstOccurrenceCurrentRankQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (compactFirstOccurrenceCurrentVariable input) ++
    compactFirstOccurrenceOriginalSource input


-- @@ L715-722 verbatim
private noncomputable def compactFirstOccurrenceCurrentRankQueryComputable :
    BitTM
      compactFirstOccurrenceCurrentRankQuery := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceCurrentVariableComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable hprefix
    compactFirstOccurrenceOriginalSourceComputable


-- @@ L724-726 verbatim
private def compactFirstOccurrenceCurrentRawRank : List Bool → List Bool :=
  sourceNormalizedVariableRankOutput ∘
    compactFirstOccurrenceCurrentRankQuery


-- @@ L728-733 verbatim
private noncomputable def compactFirstOccurrenceCurrentRawRankComputable :
    BitTM
      compactFirstOccurrenceCurrentRawRank :=
  GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceCurrentRankQueryComputable
    sourceNormalizedVariableRankComputable


-- @@ L735-738 verbatim
private def compactFirstOccurrenceNewMarker : List Bool → List Bool :=
  maskComputedWordEquality
    compactFirstOccurrenceCurrentRawRank
    compactFirstOccurrenceOrdinal


-- @@ L740-742 verbatim
private def compactFirstOccurrenceNewSelection
    (input : List Bool) : List Bool :=
  (compactFirstOccurrenceNewMarker input).headD false :: input


-- @@ L744-749 verbatim
private noncomputable def compactFirstOccurrenceNewSelectionComputable :
    BitTM
      compactFirstOccurrenceNewSelection := by
  exact sourceQaryMaskRankTaggedLowerLeftEqualitySelectionComputable
    compactFirstOccurrenceCurrentRawRankComputable
    compactFirstOccurrenceOrdinalComputable


-- @@ L751-755 verbatim
private def compactFirstOccurrenceIncrementBranch
    (input : List Bool) : List Bool :=
  if (compactFirstOccurrenceNewMarker input).headD false then
    [true]
  else []


-- @@ L757-762 verbatim
private noncomputable def compactFirstOccurrenceIncrementBranchComputable :
    BitTM
      compactFirstOccurrenceIncrementBranch := by
  exact sourcePreservingConditionalComputable
    compactFirstOccurrenceNewSelectionComputable
    (sourceFixedWordComputable [true]) []


-- @@ L764-767 verbatim
private def compactFirstOccurrenceNextCounter
    (input : List Bool) : List Bool :=
  compactFirstOccurrenceCounter input ++
    compactFirstOccurrenceIncrementBranch input


-- @@ L769-774 verbatim
private noncomputable def compactFirstOccurrenceNextCounterComputable :
    BitTM
      compactFirstOccurrenceNextCounter :=
  pointwiseAppendComputable
    compactFirstOccurrenceCounterComputable
    compactFirstOccurrenceIncrementBranchComputable


-- @@ L776-793 verbatim
private theorem compactFirstOccurrenceNextCounter_eq
    (input : List Bool) :
    compactFirstOccurrenceNextCounter input =
      if compactFirstOccurrenceCurrentRawRank input =
          compactFirstOccurrenceOrdinal input then
        compactFirstOccurrenceCounter input ++ [true]
      else compactFirstOccurrenceCounter input := by
  unfold compactFirstOccurrenceNextCounter
    compactFirstOccurrenceIncrementBranch
    compactFirstOccurrenceNewMarker
  rw [sourceQaryMaskSquareComputedWordEquality_valid]
  by_cases h : compactFirstOccurrenceCurrentRawRank input =
      compactFirstOccurrenceOrdinal input
  · simp only [h, decide_true, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      ↓reduceIte]
  · simp only [h, decide_false, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      Bool.false_eq_true,
        ↓reduceIte, List.append_nil]


-- @@ L795-803 verbatim
/-- GapCVP reduction support. -/
def compactFirstOccurrenceScanStep
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (compactFirstOccurrenceNextCounter input) ++
    (lengthPrefixedWord
      (true :: compactFirstOccurrenceOrdinal input) ++
    (lengthPrefixedWord
      (literalSuffix (compactFirstOccurrencePending input)) ++
      compactFirstOccurrenceOriginalSource input))


-- @@ L805-823 verbatim
private noncomputable def compactFirstOccurrenceScanStepComputable :
    BitTM
      compactFirstOccurrenceScanStep := by
  have hcounter := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceNextCounterComputable
    structuralPrefixWriterComputable
  have hordinalBit := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceOrdinalComputable
    (prependBitComputable true)
  have hordinal := GapCVP.TMComposition.computableInPolyTime
    hordinalBit structuralPrefixWriterComputable
  have hpendingTail := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrencePendingComputable literalSuffixComputable
  have hpending := GapCVP.TMComposition.computableInPolyTime
    hpendingTail structuralPrefixWriterComputable
  exact pointwiseAppendComputable hcounter
    (pointwiseAppendComputable hordinal
      (pointwiseAppendComputable hpending
        compactFirstOccurrenceOriginalSourceComputable))


-- @@ L825-830 verbatim
private theorem compactFirstOccurrenceNextCounter_length_le
    (input : List Bool) :
    (compactFirstOccurrenceNextCounter input).length ≤
      (compactFirstOccurrenceCounter input).length + 1 := by
  rw [compactFirstOccurrenceNextCounter_eq]
  split_ifs <;> simp


-- @@ L832-855 verbatim
private theorem compactFirstOccurrenceScanStep_length_le
    (input : List Bool) :
    (compactFirstOccurrenceScanStep input).length ≤ input.length + 7 := by
  have hcounter :=
    sourceNormalizedVariableScanStructuralFieldAccounting input
  have hordinal :=
    sourceNormalizedVariableScanStructuralFieldAccounting
      (firstFieldSuffix input)
  have hpending :=
    sourceNormalizedVariableScanStructuralFieldAccounting
      (firstFieldSuffix (firstFieldSuffix input))
  have htail := sourceOriginalIndexedLiteralSuffix_length_le
    (firstFieldContents (firstFieldSuffix (firstFieldSuffix input)))
  have hnext := compactFirstOccurrenceNextCounter_length_le input
  simp only [compactFirstOccurrenceScanStep,
    compactFirstOccurrenceCounter,
    compactFirstOccurrenceOrdinal,
    compactFirstOccurrenceOrdinalSuffix,
    compactFirstOccurrencePending,
    compactFirstOccurrencePendingSuffix,
    compactFirstOccurrenceOriginalSource,
    Function.comp_apply, List.length_append,
    lengthPrefixedWord_length, List.length_cons] at *
  omega


-- @@ L857-881 verbatim
private theorem compactFirstOccurrenceScanStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      compactFirstOccurrenceScanStep (9 * Polynomial.X) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage hstage
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hcount := parsedUnaryFold_count_le_length
    input count seed hparse
  have hiterate : ∀ number : ℕ,
      ((compactFirstOccurrenceScanStep^[number]) seed).length ≤
        seed.length + 7 * number := by
    intro number
    induction number with
    | zero => simp only [Function.iterate_zero, id_eq, mul_zero, add_zero, Std.le_refl]
    | succ number ih =>
        rw [Function.iterate_succ_apply']
        have hnext := compactFirstOccurrenceScanStep_length_le
          ((compactFirstOccurrenceScanStep^[number]) seed)
        omega
  have hstageBound := hiterate stage
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega


-- @@ L883-890 verbatim
/-- GapCVP reduction support. -/
noncomputable def compactFirstOccurrenceScanFoldComputable :
    BitTM
      (boundedRecordFoldOutput compactFirstOccurrenceScanStep) :=
  boundedDependentRecordFoldComputable
    compactFirstOccurrenceScanStepComputable
    (9 * Polynomial.X)
    compactFirstOccurrenceScanStep_polynomiallyBoundedFoldStates


-- @@ L892-895 verbatim
private def compactFirstOccurrenceLiteralCount
    (input : List Bool) : List Bool :=
  sourceClauseCountUnary input ++
    (sourceClauseCountUnary input ++ sourceClauseCountUnary input)


-- @@ L897-903 verbatim
private noncomputable def compactFirstOccurrenceLiteralCountComputable :
    BitTM
      compactFirstOccurrenceLiteralCount :=
  pointwiseAppendComputable sourceClauseCountUnaryComputable
    (pointwiseAppendComputable
      sourceClauseCountUnaryComputable
      sourceClauseCountUnaryComputable)


-- @@ L905-910 verbatim
/-- GapCVP reduction support. -/
def compactFirstOccurrenceScanSeed
    (input : List Bool) : List Bool :=
  lengthPrefixedWord [] ++
    (lengthPrefixedWord [] ++
    (lengthPrefixedWord (firstFieldSuffix input) ++ input))


-- @@ L912-928 verbatim
/-- GapCVP reduction support. -/
noncomputable def compactFirstOccurrenceScanSeedComputable :
    BitTM
      compactFirstOccurrenceScanSeed := by
  have hbody := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable structuralPrefixWriterComputable
  have hrecord := pointwiseAppendComputable hbody
    (Turing.idComputableInPolyTime bitEncoding)
  have hprefix := prependWordComputable
    (lengthPrefixedWord [] ++ lengthPrefixedWord [])
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hrecord hprefix
  change BitTM
    (fun input => lengthPrefixedWord [] ++
      (lengthPrefixedWord [] ++
        (lengthPrefixedWord (firstFieldSuffix input) ++ input)))
  simpa only [List.append_assoc, Function.comp_apply, id_eq, Function.comp_def] using hphysical


-- @@ L930-933 verbatim
private def compactFirstOccurrenceScanPreparation
    (input : List Bool) : List Bool :=
  compactFirstOccurrenceLiteralCount input ++
    false :: compactFirstOccurrenceScanSeed input


-- @@ L935-942 verbatim
private noncomputable def compactFirstOccurrenceScanPreparationComputable :
    BitTM
      compactFirstOccurrenceScanPreparation := by
  have hseed := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceScanSeedComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    compactFirstOccurrenceLiteralCountComputable hseed


-- @@ L944-948 verbatim
/-- GapCVP reduction support. -/
def compactSourceOccurringVariableCountUnary : List Bool → List Bool :=
  compactFirstOccurrenceCounter ∘
    boundedRecordFoldOutput compactFirstOccurrenceScanStep ∘
    compactFirstOccurrenceScanPreparation


-- @@ L950-958 verbatim
/-- GapCVP reduction support. -/
noncomputable def compactSourceOccurringVariableCountUnaryComputable :
    BitTM
      compactSourceOccurringVariableCountUnary := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    compactFirstOccurrenceScanPreparationComputable
    compactFirstOccurrenceScanFoldComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hfold compactFirstOccurrenceCounterComputable


-- @@ L960-960 verbatim
end BinaryCompactSourceFirstOccurrenceTM


-- @@ L962-962 verbatim
namespace BinaryCompactRankPrefixIdentity


-- @@ L964-964 verbatim
open GapCVP.SourceMachineCert GapCVP.BinarySourceVariableCompaction


-- @@ L966-969 verbatim
private def firstOccurrenceAt (names : List ℕ) (index : ℕ) : Bool :=
  match names[index]? with
  | none => false
  | some name => decide (names.idxOf name = index)


-- @@ L971-973 verbatim
/-- GapCVP reduction support. -/
def firstOccurrencePrefixCount (names : List ℕ) (bound : ℕ) : ℕ :=
  ((List.range bound).filter (firstOccurrenceAt names)).length


-- @@ L975-982 verbatim
private theorem firstOccurrencePrefixCount_succ
    (names : List ℕ) (bound : ℕ) :
    firstOccurrencePrefixCount names (bound + 1) =
      firstOccurrencePrefixCount names bound +
        if firstOccurrenceAt names bound then 1 else 0 := by
  cases hfirst : firstOccurrenceAt names bound <;>
    simp [firstOccurrencePrefixCount, List.range_succ,
      List.filter_append, hfirst]


-- @@ L984-987 verbatim
private theorem firstOccurrenceAt_of_length_le
    (names : List ℕ) (index : ℕ) (hindex : names.length ≤ index) :
    firstOccurrenceAt names index = false := by
  simp only [firstOccurrenceAt, List.getElem?_eq_none hindex]


-- @@ L989-993 verbatim
private theorem firstOccurrenceAt_of_lt
    (names : List ℕ) (index : ℕ) (hindex : index < names.length) :
    firstOccurrenceAt names index =
      decide (names.idxOf (names[index]'hindex) = index) := by
  simp only [firstOccurrenceAt, List.getElem?_eq_getElem hindex]


-- @@ L995-1004 verbatim
private theorem not_mem_take_idxOf
    (names : List ℕ) (name : ℕ) :
    name ∉ names.take (names.idxOf name) := by
  by_cases hname : name ∈ names
  · intro hprefix
    have hlt :=
      (List.mem_take_iff_idxOf_lt hname).mp hprefix
    exact (Nat.lt_irrefl (names.idxOf name)) hlt
  · intro hprefix
    exact hname (List.mem_of_mem_take hprefix)


-- @@ L1006-1016 verbatim
private theorem idxOf_getElem_le
    (names : List ℕ) (index : ℕ) (hindex : index < names.length) :
    names.idxOf (names[index]'hindex) ≤ index := by
  have hmem : (names[index]'hindex) ∈ names := List.getElem_mem hindex
  have hprefix :
      (names[index]'hindex) ∈ names.take (index + 1) := by
    rw [List.take_succ_eq_append_getElem hindex]
    exact List.mem_append_right _ (by simp only [List.mem_cons, List.not_mem_nil, or_false])
  have hlt :=
    (List.mem_take_iff_idxOf_lt hmem).mp hprefix
  omega


-- @@ L1018-1025 verbatim
private theorem idxOf_getElem_eq_iff_not_mem_take
    (names : List ℕ) (index : ℕ) (hindex : index < names.length) :
    names.idxOf (names[index]'hindex) = index ↔
      (names[index]'hindex) ∉ names.take index := by
  have hmem : (names[index]'hindex) ∈ names := List.getElem_mem hindex
  have hle := idxOf_getElem_le names index hindex
  rw [List.mem_take_iff_idxOf_lt hmem]
  omega


-- @@ L1027-1065 verbatim
private theorem firstOccurrencePrefixCount_eq_eraseDups_take_length
    (names : List ℕ) (bound : ℕ) :
    firstOccurrencePrefixCount names bound =
      (names.take bound).eraseDups.length := by
  induction bound with
  | zero => simp only [firstOccurrencePrefixCount, List.range_zero, List.filter_nil,
      List.length_nil, List.take_zero,
                List.eraseDups_nil]
  | succ index ih =>
    rw [firstOccurrencePrefixCount_succ, ih]
    by_cases hindex : index < names.length
    · rw [List.take_succ_eq_append_getElem hindex,
        List.eraseDups_append, List.length_append,
        firstOccurrenceAt_of_lt names index hindex]
      by_cases hseen : (names[index]'hindex) ∈ names.take index
      · have hnotfirst :
            names.idxOf (names[index]'hindex) ≠ index := by
          intro hfirst
          exact ((idxOf_getElem_eq_iff_not_mem_take
            names index hindex).mp hfirst) hseen
        simp only [hnotfirst, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero,
            List.removeAll,
            List.elem_eq_contains, List.contains_eq_mem, hseen, decide_true, Bool.not_true,
                not_false_eq_true,
            List.filter_cons_of_neg, List.filter_nil, List.eraseDups_nil, List.length_nil]
      · have hfirst :
            names.idxOf (names[index]'hindex) = index :=
          (idxOf_getElem_eq_iff_not_mem_take
            names index hindex).mpr hseen
        simp only [hfirst, decide_true, ↓reduceIte, List.removeAll, List.elem_eq_contains,
          List.contains_eq_mem, hseen, decide_false, Bool.not_false, List.filter_cons_of_pos,
          List.filter_nil, List.eraseDups_cons, List.eraseDups_nil, List.length_cons,
          List.length_nil, zero_add]
    · have hlength : names.length ≤ index := Nat.le_of_not_gt hindex
      rw [firstOccurrenceAt_of_length_le names index hlength]
      have htake : names.take index = names := List.take_of_length_le hlength
      have htakesucc : names.take (index + 1) = names :=
        List.take_of_length_le (Nat.le_trans hlength (Nat.le_add_right _ _))
      simp only [htake, Bool.false_eq_true, ↓reduceIte, add_zero, htakesucc]


-- @@ L1067-1095 verbatim
private theorem eraseDups_idxOf_eq_eraseDups_take_length
    (names : List ℕ) (name : ℕ) :
    names.eraseDups.idxOf name =
      (names.take (names.idxOf name)).eraseDups.length := by
  by_cases hname : name ∈ names
  · have hindex : names.idxOf name < names.length :=
      List.idxOf_lt_length_of_mem hname
    have hprefix : name ∉ names.take (names.idxOf name) :=
      not_mem_take_idxOf names name
    have hsplit :
        names = names.take (names.idxOf name) ++
          name :: names.drop (names.idxOf name + 1) := by
      calc
        names = names.take (names.idxOf name) ++
            names.drop (names.idxOf name) :=
          (List.take_append_drop (names.idxOf name) names).symm
        _ = names.take (names.idxOf name) ++
            name :: names.drop (names.idxOf name + 1) := by
          rw [List.drop_eq_getElem_cons hindex]
          simp only [List.getElem_idxOf]
    conv_lhs => rw [hsplit, List.eraseDups_append, List.idxOf_append]
    simp only [List.mem_eraseDups, hprefix, ↓reduceIte, List.removeAll, List.elem_eq_contains,
        List.contains_eq_mem, decide_false, Bool.not_false, List.filter_cons_of_pos,
            List.eraseDups_cons,
        List.filter_filter, List.idxOf_cons_self, zero_add]
  · have hnotdup : name ∉ names.eraseDups := by
      simpa only [List.mem_eraseDups] using hname
    rw [List.idxOf_eq_length hname, List.take_length,
      List.idxOf_eq_length hnotdup]


-- @@ L1097-1105 verbatim
theorem compactVariableRank_eq_firstOccurrencePrefixCount
    (formula : ThreeCNF) (name : ℕ) :
    compactVariableRank formula name =
      firstOccurrencePrefixCount
        (formulaVariables formula) (variableRank formula name) := by
  unfold compactVariableRank occurringVariables variableRank
  rw [firstOccurrencePrefixCount_eq_eraseDups_take_length]
  exact eraseDups_idxOf_eq_eraseDups_take_length
    (formulaVariables formula) name


-- @@ L1107-1107 verbatim
end BinaryCompactRankPrefixIdentity


-- @@ L1109-1109 verbatim
namespace BinaryCompactSourceFirstOccurrenceTM


-- @@ L1111-1111 verbatim
open GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.OutputBoundedDependentRecordFold

-- @@ L1112-1112 verbatim
open GapCVP.SourceNormalizedVariableRankScanTM GapCVP.BinaryDimensionTM

-- @@ L1113-1113 verbatim
open GapCVP.BinarySourceVariableCompaction GapCVP.BinaryCompactRankPrefixIdentity


-- @@ L1115-1122 verbatim
/-- GapCVP reduction support. -/
def compactFirstOccurrenceValidState
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (pending : List Literal) : List Bool :=
  lengthPrefixedWord (List.replicate counter true) ++
    (lengthPrefixedWord (List.replicate ordinal true) ++
      (lengthPrefixedWord (pending.flatMap encodeLiteral) ++
        encodeThreeCNF formula))


-- @@ L1124-1131 verbatim
@[simp] theorem compactFirstOccurrenceValidState_counter
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (pending : List Literal) :
    compactFirstOccurrenceCounter
      (compactFirstOccurrenceValidState formula counter ordinal pending) =
        List.replicate counter true := by
  simp only [compactFirstOccurrenceCounter, compactFirstOccurrenceValidState,
      SourceFormulaStructuralDecoder.firstFieldContents_valid]


-- @@ L1133-1142 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_ordinal
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (pending : List Literal) :
    compactFirstOccurrenceOrdinal
      (compactFirstOccurrenceValidState formula counter ordinal pending) =
        List.replicate ordinal true := by
  simp only [compactFirstOccurrenceOrdinal, compactFirstOccurrenceOrdinalSuffix,
      compactFirstOccurrenceValidState, Function.comp_apply,
          SourceFormulaStructuralDecoder.firstFieldSuffix_valid,
      SourceFormulaStructuralDecoder.firstFieldContents_valid]


-- @@ L1144-1153 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_pending
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (pending : List Literal) :
    compactFirstOccurrencePending
      (compactFirstOccurrenceValidState formula counter ordinal pending) =
        pending.flatMap encodeLiteral := by
  simp only [compactFirstOccurrencePending, compactFirstOccurrencePendingSuffix,
      compactFirstOccurrenceOrdinalSuffix, compactFirstOccurrenceValidState, Function.comp_apply,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid,
          SourceFormulaStructuralDecoder.firstFieldContents_valid]


-- @@ L1155-1163 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_originalSource
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (pending : List Literal) :
    compactFirstOccurrenceOriginalSource
      (compactFirstOccurrenceValidState formula counter ordinal pending) =
        encodeThreeCNF formula := by
  simp only [compactFirstOccurrenceOriginalSource, compactFirstOccurrencePendingSuffix,
      compactFirstOccurrenceOrdinalSuffix, compactFirstOccurrenceValidState, Function.comp_apply,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]


-- @@ L1165-1178 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_currentVariable
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (literal : Literal) (remaining : List Literal) :
    compactFirstOccurrenceCurrentVariable
        (compactFirstOccurrenceValidState
          formula counter ordinal (literal :: remaining)) =
      Computability.encodeNat literal.1 := by
  simp only [compactFirstOccurrenceCurrentVariable, compactFirstOccurrencePending,
      compactFirstOccurrencePendingSuffix, compactFirstOccurrenceOrdinalSuffix,
          compactFirstOccurrenceValidState,
      List.flatMap_cons, encodeLiteral, List.append_assoc, List.cons_append, List.nil_append,
          Function.comp_apply,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid,
          SourceFormulaStructuralDecoder.firstFieldContents_valid]


-- @@ L1180-1189 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_currentRankQuery
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (literal : Literal) (remaining : List Literal) :
    compactFirstOccurrenceCurrentRankQuery
        (compactFirstOccurrenceValidState
          formula counter ordinal (literal :: remaining)) =
      sourceNormalizedVariableRankQuery literal.1 formula := by
  simp only [compactFirstOccurrenceCurrentRankQuery,
      compactFirstOccurrenceValidState_currentVariable,
      compactFirstOccurrenceValidState_originalSource, sourceNormalizedVariableRankQuery]


-- @@ L1191-1199 verbatim
@[simp] private theorem compactFirstOccurrenceValidState_currentRawRank
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (literal : Literal) (remaining : List Literal) :
    compactFirstOccurrenceCurrentRawRank
        (compactFirstOccurrenceValidState
          formula counter ordinal (literal :: remaining)) =
      List.replicate (variableRank formula literal.1) true := by
  simp only [compactFirstOccurrenceCurrentRawRank, Function.comp_apply,
      compactFirstOccurrenceValidState_currentRankQuery, sourceNormalizedVariableRankOutput_valid]


-- @@ L1201-1224 verbatim
private theorem compactFirstOccurrenceValidState_nextCounter
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (literal : Literal) (remaining : List Literal) :
    compactFirstOccurrenceNextCounter
        (compactFirstOccurrenceValidState
          formula counter ordinal (literal :: remaining)) =
      List.replicate
        (if variableRank formula literal.1 = ordinal
          then counter + 1 else counter) true := by
  rw [compactFirstOccurrenceNextCounter_eq,
    compactFirstOccurrenceValidState_currentRawRank,
    compactFirstOccurrenceValidState_ordinal,
    compactFirstOccurrenceValidState_counter]
  by_cases hfirst : variableRank formula literal.1 = ordinal
  · simp only [hfirst, ↓reduceIte, SourceStructuralDecoder.replicate_true_append_cons,
      List.append_nil,
        List.replicate_succ]
  · have hwords :
        List.replicate (variableRank formula literal.1) true ≠
          List.replicate ordinal true := by
      intro hequal
      apply hfirst
      simpa only [List.length_replicate] using congrArg List.length hequal
    simp only [hwords, ↓reduceIte, hfirst]


-- @@ L1226-1242 verbatim
private theorem compactFirstOccurrenceValidState_step
    (formula : ThreeCNF) (counter ordinal : ℕ)
    (literal : Literal) (remaining : List Literal) :
    compactFirstOccurrenceScanStep
        (compactFirstOccurrenceValidState
          formula counter ordinal (literal :: remaining)) =
      compactFirstOccurrenceValidState formula
        (if variableRank formula literal.1 = ordinal
          then counter + 1 else counter)
        (ordinal + 1) remaining := by
  unfold compactFirstOccurrenceScanStep
  rw [compactFirstOccurrenceValidState_nextCounter,
    compactFirstOccurrenceValidState_ordinal,
    compactFirstOccurrenceValidState_pending,
    compactFirstOccurrenceValidState_originalSource]
  simp only [List.flatMap_cons, SourceFormulaStructuralDecoder.literalSuffix_valid,
      compactFirstOccurrenceValidState, List.replicate_succ]


-- @@ L1244-1254 verbatim
private theorem compactFirstOccurrenceLiteralCount_valid
    (formula : ThreeCNF) :
    compactFirstOccurrenceLiteralCount (encodeThreeCNF formula) =
      List.replicate
        (sourceNormalizedVariableLiteralList formula).length true := by
  simp only [compactFirstOccurrenceLiteralCount,
    sourceClauseCountUnary_valid]
  rw [← List.replicate_add, ← List.replicate_add,
    sourceNormalizedVariableLiteralList_length]
  congr 1
  omega


-- @@ L1256-1264 verbatim
theorem compactFirstOccurrenceScanSeed_valid
    (formula : ThreeCNF) :
    compactFirstOccurrenceScanSeed (encodeThreeCNF formula) =
      compactFirstOccurrenceValidState formula 0 0
        (sourceNormalizedVariableLiteralList formula) := by
  simp only [compactFirstOccurrenceScanSeed,
      SourceFormulaStructuralDecoder.firstFieldSuffix_encodeThreeCNF,
      compactFirstOccurrenceValidState, List.replicate_zero,
          sourceNormalizedVariableLiteralList_stream]


-- @@ L1266-1274 verbatim
private theorem compactFirstOccurrenceScanPreparation_valid
    (formula : ThreeCNF) :
    compactFirstOccurrenceScanPreparation (encodeThreeCNF formula) =
      unaryBoundedFoldWord
        (sourceNormalizedVariableLiteralList formula).length
        (compactFirstOccurrenceValidState formula 0 0
          (sourceNormalizedVariableLiteralList formula)) := by
  simp only [compactFirstOccurrenceScanPreparation, compactFirstOccurrenceLiteralCount_valid,
      compactFirstOccurrenceScanSeed_valid, unaryBoundedFoldWord]


-- @@ L1276-1322 verbatim
theorem compactFirstOccurrenceValidState_iterate
    (formula : ThreeCNF) (index : ℕ)
    (hindex : index ≤ (sourceNormalizedVariableLiteralList formula).length) :
    ((compactFirstOccurrenceScanStep^[index])
        (compactFirstOccurrenceValidState formula 0 0
          (sourceNormalizedVariableLiteralList formula))) =
      compactFirstOccurrenceValidState formula
        (firstOccurrencePrefixCount (formulaVariables formula) index)
        index ((sourceNormalizedVariableLiteralList formula).drop index) := by
  induction index with
  | zero => simp only [Function.iterate_zero, id_eq, firstOccurrencePrefixCount, List.range_zero,
      List.filter_nil,
                List.length_nil, List.drop_zero]
  | succ index ih =>
    have hlt : index < (sourceNormalizedVariableLiteralList formula).length :=
      Nat.lt_of_succ_le hindex
    have hprev : index ≤ (sourceNormalizedVariableLiteralList formula).length :=
      Nat.le_of_lt hlt
    have hnames : index < (formulaVariables formula).length := by
      rw [← sourceNormalizedVariableLiteralList_variables]
      simpa only [List.length_map] using hlt
    have hname :
        (formulaVariables formula)[index]'hnames =
          ((sourceNormalizedVariableLiteralList formula)[index]'hlt).1 := by
      have hget := congrArg
        (fun names : List ℕ => names[index]?)
        (sourceNormalizedVariableLiteralList_variables formula)
      rw [List.getElem?_map, List.getElem?_eq_getElem hlt,
        List.getElem?_eq_getElem hnames] at hget
      simpa only [Option.map_some, Option.some.injEq] using hget.symm
    have hcounter :
        firstOccurrencePrefixCount (formulaVariables formula) (index + 1) =
          firstOccurrencePrefixCount (formulaVariables formula) index +
            if variableRank formula
                ((sourceNormalizedVariableLiteralList formula)[index]'hlt).1 =
                  index then 1 else 0 := by
      rw [firstOccurrencePrefixCount_succ,
        firstOccurrenceAt_of_lt (formulaVariables formula) index hnames,
        hname]
      simp only [decide_eq_true_eq, variableRank, Nat.add_left_cancel_iff]
      rfl
    rw [Function.iterate_succ_apply']
    rw [ih hprev]
    rw [List.drop_eq_getElem_cons hlt,
      compactFirstOccurrenceValidState_step]
    rw [hcounter]
    split_ifs <;> simp


-- @@ L1324-1340 verbatim
theorem compactSourceOccurringVariableCountUnary_valid
    (formula : ThreeCNF) :
    compactSourceOccurringVariableCountUnary (encodeThreeCNF formula) =
      List.replicate (occurringVariableCount formula) true := by
  unfold compactSourceOccurringVariableCountUnary
  rw [Function.comp_apply, Function.comp_apply,
    compactFirstOccurrenceScanPreparation_valid]
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  rw [compactFirstOccurrenceValidState_iterate
    formula (sourceNormalizedVariableLiteralList formula).length
    (Nat.le_refl _)]
  rw [compactFirstOccurrenceValidState_counter]
  congr 1
  rw [firstOccurrencePrefixCount_eq_eraseDups_take_length,
    sourceNormalizedVariableLiteralList_length,
    ← formulaVariables_length, List.take_length]
  rfl


-- @@ L1342-1342 verbatim
end BinaryCompactSourceFirstOccurrenceTM


-- @@ L1344-1344 verbatim
namespace BinaryExplicitAffineRows


-- @@ L1346-1346 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.GaussianXorWorker

-- @@ L1347-1347 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L1349-1353 verbatim
/-- GapCVP reduction support. -/
@[expose] def affineCellQuery
    (row column : ℕ) (source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate row true) ++
    lengthPrefixedWord (List.replicate column true) ++ source


-- @@ L1355-1357 verbatim
/-- GapCVP reduction support. -/
def sourceExplicitAffineCellRow : List Bool → List Bool :=
  firstFieldContents


-- @@ L1359-1363 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceExplicitAffineCellRowComputable :
    BitTM
      sourceExplicitAffineCellRow :=
  firstFieldContentsComputable


-- @@ L1365-1367 verbatim
/-- GapCVP reduction support. -/
def sourceExplicitAffineCellColumn : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix


-- @@ L1369-1374 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceExplicitAffineCellColumnComputable :
    BitTM
      sourceExplicitAffineCellColumn :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L1376-1378 verbatim
/-- GapCVP reduction support. -/
def sourceExplicitAffineCellOriginalSource : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L1380-1385 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceExplicitAffineCellOriginalSourceComputable :
    BitTM
      sourceExplicitAffineCellOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable


-- @@ L1387-1393 verbatim
@[simp] theorem sourceExplicitAffineCellRow_query
    (row column : ℕ) (source : List Bool) :
    sourceExplicitAffineCellRow
        (affineCellQuery row column source) =
      List.replicate row true := by
  simp only [sourceExplicitAffineCellRow, affineCellQuery, List.append_assoc,
      firstFieldContents_valid]


-- @@ L1395-1402 verbatim
@[simp] theorem sourceExplicitAffineCellColumn_query
    (row column : ℕ) (source : List Bool) :
    sourceExplicitAffineCellColumn
        (affineCellQuery row column source) =
      List.replicate column true := by
  simp only [sourceExplicitAffineCellColumn, affineCellQuery, List.append_assoc,
      Function.comp_apply,
      firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L1404-1410 verbatim
@[simp] theorem sourceExplicitAffineCellOriginalSource_query
    (row column : ℕ) (source : List Bool) :
    sourceExplicitAffineCellOriginalSource
        (affineCellQuery row column source) = source := by
  simp only [sourceExplicitAffineCellOriginalSource, affineCellQuery, List.append_assoc,
      Function.comp_apply,
      firstFieldSuffix_valid]


-- @@ L1412-1416 verbatim
/-- GapCVP reduction support. -/
def sourceExplicitAffineXorBits
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  binaryGaussianXorHeadWord (first input ++ second input)


-- @@ L1418-1431 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourceExplicitAffineXorBitsComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (sourceExplicitAffineXorBits first second) := by
  have hpair := pointwiseAppendComputable hfirst hsecond
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpair binaryGaussianXorHeadComputable
  change BitTM
    (fun input => binaryGaussianXorHeadWord
      (first input ++ second input))
  simpa only [Function.comp_def] using hphysical


-- @@ L1433-1442 verbatim
theorem sourceExplicitAffineXorBits_valid
    (first second : List Bool → List Bool)
    (input : List Bool) (firstBit secondBit : Bool)
    (hfirst : first input = [firstBit])
    (hsecond : second input = [secondBit]) :
    sourceExplicitAffineXorBits first second input =
      [Bool.xor firstBit secondBit] := by
  simp only [sourceExplicitAffineXorBits, binaryGaussianXorHeadWord, hfirst, hsecond,
      List.cons_append,
      List.nil_append]


-- @@ L1444-1444 verbatim
end BinaryExplicitAffineRows


-- @@ L1446-1446 verbatim
namespace BinaryPhysicalWordRuntimeDegreeTM


-- @@ L1448-1448 verbatim
open Turing GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralNaturalBinaryWriter

-- @@ L1449-1449 verbatim
open GapCVP.BinaryExplicitAffineRows


-- @@ L1451-1460 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryPhysicalWordRuntimeCompositionComputer
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (second ∘ first) :=
  GapCVP.TMComposition.computableInPolyTime
    firstComputer secondComputer


-- @@ L1462-1467 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryPhysicalWordNaturalWriterComputer :
    BitTM
      (fun input : List Bool => Computability.encodeNat input.length) :=
  structuralNaturalBinaryWriterComputable


-- @@ L1469-1473 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryPhysicalWordDropHeadComputer :
    BitTM List.tail :=
  dropHeadComputable


-- @@ L1475-1480 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryPhysicalWordCellOriginalSourceComputer :
    BitTM
      sourceExplicitAffineCellOriginalSource :=
  sourceExplicitAffineCellOriginalSourceComputable


-- @@ L1482-1482 verbatim
end BinaryPhysicalWordRuntimeDegreeTM


-- @@ L1484-1484 verbatim
namespace BinaryPhysicalCellGridWordTM


-- @@ L1486-1486 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter

-- @@ L1487-1487 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L1489-1493 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def physicalCellGridPrefixComputer :
    BitTM
      lengthPrefixedWord :=
  structuralPrefixWriterComputable


-- @@ L1495-1502 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def physicalCellGridAppendComputer
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (fun input => first input ++ second input) :=
  pointwiseAppendComputable firstComputer secondComputer


-- @@ L1504-1504 verbatim
end BinaryPhysicalCellGridWordTM


-- @@ L1506-1506 verbatim
namespace BinaryRadiusTM


-- @@ L1508-1508 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder

-- @@ L1509-1509 verbatim
open GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold

-- @@ L1510-1510 verbatim
open GapCVP.SourceWholeOutputAssemblyTM

-- @@ L1511-1511 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L1512-1512 verbatim
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CNFBoundedRecordFoldTM

-- @@ L1513-1513 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CLStructuralAtomicNaturalWriter

-- @@ L1514-1514 verbatim
open GapCVP.SourceLatticeStructuralRadiusNumerator GapCVP.SourceLatticeStructuralRationalRadius

-- @@ L1515-1515 verbatim
open GapCVP.SourceLatticeStructuralRationalRadiusTM


-- @@ L1517-1519 verbatim
/-- GapCVP reduction support. -/
@[expose] def squareRootAccumulator (input : List Bool) : List Bool :=
  firstFieldContents input


-- @@ L1521-1525 verbatim
/-- GapCVP reduction support. -/
noncomputable def squareRootAccumulatorComputable :
    BitTM
      squareRootAccumulator :=
  firstFieldContentsComputable


-- @@ L1527-1529 verbatim
/-- GapCVP reduction support. -/
@[expose] def squareRootTarget (input : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix input)


-- @@ L1531-1536 verbatim
/-- GapCVP reduction support. -/
noncomputable def squareRootTargetComputable :
    BitTM
      squareRootTarget :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L1538-1539 verbatim
private def squareRootAccumulatorSquared (input : List Bool) : List Bool :=
  List.replicate ((squareRootAccumulator input).length ^ 2) true


-- @@ L1541-1551 verbatim
private noncomputable def squareRootAccumulatorSquaredComputable :
    BitTM
      squareRootAccumulatorSquared := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    squareRootAccumulatorComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 2))
  change
    BitTM
      (fun input : List Bool =>
        List.replicate ((squareRootAccumulator input).length ^ 2) true)
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Function.comp_def] using hphysical


-- @@ L1553-1555 verbatim
private def squareRootLessMarker (input : List Bool) : List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    squareRootAccumulatorSquared squareRootTarget input


-- @@ L1557-1561 verbatim
private noncomputable def squareRootLessMarkerComputable :
    BitTM
      squareRootLessMarker :=
  fourFamilyComputedUnaryLessBitComputable
    squareRootAccumulatorSquaredComputable squareRootTargetComputable


-- @@ L1563-1566 verbatim
@[simp] private theorem squareRootLessMarker_length (input : List Bool) :
    (squareRootLessMarker input).length = 1 :=
  fourFamilyComputedUnaryLessBitOutput_length
    squareRootAccumulatorSquared squareRootTarget input


-- @@ L1568-1569 verbatim
private def squareRootLessBit (input : List Bool) : Bool :=
  (squareRootLessMarker input).headD false


-- @@ L1571-1582 verbatim
private theorem squareRootLessMarker_eq (input : List Bool) :
    squareRootLessMarker input = [squareRootLessBit input] := by
  have hlength := squareRootLessMarker_length input
  cases hword : squareRootLessMarker input with
  | nil => simp only [hword, List.length_nil, zero_ne_one] at hlength
  | cons bit remaining =>
      cases remaining with
      | nil => simp only [squareRootLessBit, hword, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some]
      | cons next tail => simp only [hword, List.length_cons, Nat.add_eq_right,
          Nat.add_eq_zero_iff, List.length_eq_zero_iff,
                              one_ne_zero, and_false] at hlength


-- @@ L1584-1600 verbatim
private noncomputable def squareRootLessSelectionComputable :
    BitTM
      (fun input : List Bool => squareRootLessBit input :: input) := by
  have hphysical := pointwiseAppendComputable
    squareRootLessMarkerComputable
    (Turing.idComputableInPolyTime bitEncoding)
  have heq :
      (fun input : List Bool =>
        squareRootLessMarker input ++ input) =
        (fun input : List Bool => squareRootLessBit input :: input) := by
    funext input
    simp only [squareRootLessMarker_eq, List.cons_append, List.nil_append]
  change
    BitTM
      (fun input : List Bool => squareRootLessMarker input ++ input)
    at hphysical
  rwa [heq] at hphysical


-- @@ L1602-1603 verbatim
private def squareRootIncrement (input : List Bool) : List Bool :=
  if squareRootLessBit input then [true] else []


-- @@ L1605-1611 verbatim
private noncomputable def squareRootIncrementComputable :
    BitTM
      squareRootIncrement :=
  sourcePreservingConditionalComputable
    squareRootLessSelectionComputable
    (SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      [true]) []


-- @@ L1613-1614 verbatim
private def squareRootCandidate (input : List Bool) : List Bool :=
  squareRootAccumulator input ++ squareRootIncrement input


-- @@ L1616-1620 verbatim
private noncomputable def squareRootCandidateComputable :
    BitTM
      squareRootCandidate :=
  pointwiseAppendComputable
    squareRootAccumulatorComputable squareRootIncrementComputable


-- @@ L1622-1623 verbatim
private def squareRootStep (target current : ℕ) : ℕ :=
  if current ^ 2 < target then current + 1 else current


-- @@ L1625-1634 verbatim
private theorem squareRootStep_le_target
    (target current : ℕ) (hcurrent : current ≤ target) :
    squareRootStep target current ≤ target := by
  unfold squareRootStep
  split
  next hlt =>
    have hsq : current ≤ current * current := Nat.le_mul_self current
    simp only [pow_two] at hlt
    omega
  next => exact hcurrent


-- @@ L1636-1671 verbatim
private theorem squareRootCandidate_valid
    (current target : ℕ) (padding : List Bool) :
    squareRootCandidate
      (lengthPrefixedWord (List.replicate current true) ++
        lengthPrefixedWord (List.replicate target true) ++ padding) =
      List.replicate (squareRootStep target current) true := by
  let input :=
    lengthPrefixedWord (List.replicate current true) ++
      lengthPrefixedWord (List.replicate target true) ++ padding
  have hacc : squareRootAccumulator input =
      List.replicate current true := by
    simp only [squareRootAccumulator, List.append_assoc, firstFieldContents_valid, input]
  have htarget : squareRootTarget input =
      List.replicate target true := by
    simp only [squareRootTarget, List.append_assoc, firstFieldSuffix_valid,
        firstFieldContents_valid, input]
  have hsq : squareRootAccumulatorSquared input =
      List.replicate (current ^ 2) true := by
    simp only [squareRootAccumulatorSquared, hacc, List.length_replicate]
  have hmarker : squareRootLessMarker input =
      [decide (current ^ 2 < target)] :=
    fourFamilyComputedUnaryLessBitOutput_valid
      squareRootAccumulatorSquared squareRootTarget input
      (current ^ 2) target hsq htarget
  have hbit : squareRootLessBit input =
      decide (current ^ 2 < target) := by
    simp only [squareRootLessBit, hmarker, List.headD_eq_head?_getD, List.head?_cons,
        Option.getD_some]
  change squareRootCandidate input = _
  unfold squareRootCandidate squareRootIncrement
  rw [hacc, hbit]
  by_cases hlt : current ^ 2 < target
  · simp only [hlt, decide_true, ↓reduceIte, SourceStructuralDecoder.replicate_true_append_cons,
      List.append_nil,
        ← List.replicate_succ, squareRootStep]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, squareRootStep]


-- @@ L1673-1675 verbatim
/-- GapCVP reduction support. -/
@[expose] def squareRootAnchor (target : List Bool) : List Bool :=
  lengthPrefixedWord target ++ target


-- @@ L1677-1689 verbatim
private noncomputable def squareRootAnchorComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (fun input => squareRootAnchor (target input)) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    computer CLStructuralPrefixWriter.structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hprefix computer
  change
    BitTM
      (fun input : List Bool =>
        lengthPrefixedWord (target input) ++ target input)
  exact hphysical


-- @@ L1691-1745 verbatim
private theorem squareRootRotation_step
    (target current : ℕ)
    (hcurrent : current ≤ target) :
    sourceAnchoredGridRecordRotationOutput squareRootCandidate
      (lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate (squareRootStep target current) true) := by
  let anchor := squareRootAnchor (List.replicate target true)
  let state :=
    lengthPrefixedWord anchor ++
      lengthPrefixedWord (List.replicate current true)
  have hraw :
      sourceAnchoredGridRawCandidate squareRootCandidate state =
        List.replicate (squareRootStep target current) true := by
    change squareRootCandidate
      (sourceAnchoredGridRankSourcePair state) = _
    have hpair :
        sourceAnchoredGridRankSourcePair state =
          lengthPrefixedWord (List.replicate current true) ++ anchor := by
      have hcontents :
          firstFieldContents
            (lengthPrefixedWord (List.replicate current true)) =
              List.replicate current true := by
        simpa only [List.append_nil] using
          firstFieldContents_valid (List.replicate current true) []
      simp [state, sourceAnchoredGridRankSourcePair, hcontents]
    rw [hpair]
    simpa [anchor, squareRootAnchor, List.append_assoc] using
      (squareRootCandidate_valid current target
        (List.replicate target true))
  have hfit :
      (List.replicate (squareRootStep target current) true).length ≤
        anchor.length := by
    have hstep := squareRootStep_le_target target current hcurrent
    simp [anchor, squareRootAnchor, lengthPrefixedWord_length]
    omega
  have hselector :
      sourceAnchoredGridCandidateSelector
        squareRootCandidate state = true := by
    rw [sourceAnchoredGridCandidateSelector_eq, hraw]
    have hcontents : firstFieldContents state = anchor := by
      simp [state]
    rw [hcontents]
    exact decide_eq_true hfit
  have hguard :
      sourceAnchoredGridGuardedCandidate squareRootCandidate state =
        List.replicate (squareRootStep target current) true := by
    simp [sourceAnchoredGridGuardedCandidate, hselector, hraw]
  have hrotation := sourceAnchoredGridRecordRotationOutput_records
    squareRootCandidate anchor (List.replicate current true) []
  simpa [state, anchor, hguard] using hrotation


-- @@ L1747-1767 verbatim
private theorem squareRootRotation_iterate
    (target current stages : ℕ)
    (hcurrent : current ≤ target) :
    ((sourceAnchoredGridRecordRotationOutput
      squareRootCandidate)^[stages])
        (lengthPrefixedWord
            (squareRootAnchor (List.replicate target true)) ++
          lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (squareRootAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate
            (((squareRootStep target)^[stages]) current) true) := by
  induction stages generalizing current with
  | zero => simp
  | succ stages ih =>
      rw [Function.iterate_succ_apply,
        squareRootRotation_step target current hcurrent,
        ih (squareRootStep target current)
          (squareRootStep_le_target target current hcurrent),
        Function.iterate_succ_apply]


-- @@ L1769-1781 verbatim
private theorem square_lt_iff_lt_ceil_sqrt
    (target current : ℕ) :
    current ^ 2 < target ↔
      current < Nat.ceil (Real.sqrt (target : ℝ)) := by
  constructor
  · intro hsq
    apply Nat.lt_ceil.mpr
    apply (Real.lt_sqrt (by positivity)).mpr
    exact_mod_cast hsq
  · intro hroot
    have hreal := Nat.lt_ceil.mp hroot
    have hsq := (Real.lt_sqrt (by positivity)).mp hreal
    exact_mod_cast hsq


-- @@ L1783-1816 verbatim
private theorem squareRootStep_iterate
    (target stages : ℕ) :
    ((squareRootStep target)^[stages]) 0 =
      min stages (Nat.ceil (Real.sqrt (target : ℝ))) := by
  induction stages with
  | zero => simp only [Function.iterate_zero, id_eq, zero_le, inf_of_le_left]
  | succ stages ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases hlt : stages < Nat.ceil (Real.sqrt (target : ℝ))
      · have hmin :
            min stages (Nat.ceil (Real.sqrt (target : ℝ))) = stages :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        have hnext :
            min (stages + 1) (Nat.ceil (Real.sqrt (target : ℝ))) =
              stages + 1 :=
          Nat.min_eq_left (by omega)
        have hsq : stages ^ 2 < target :=
          (square_lt_iff_lt_ceil_sqrt target stages).mpr hlt
        simp only [squareRootStep, hmin, hsq, ↓reduceIte, hnext]
      · have hle : Nat.ceil (Real.sqrt (target : ℝ)) ≤ stages := by
          omega
        have hmin :
            min stages (Nat.ceil (Real.sqrt (target : ℝ))) =
              Nat.ceil (Real.sqrt (target : ℝ)) :=
          Nat.min_eq_right hle
        have hnext :
            min (stages + 1) (Nat.ceil (Real.sqrt (target : ℝ))) =
              Nat.ceil (Real.sqrt (target : ℝ)) :=
          Nat.min_eq_right (by omega)
        have hsquare :
            ¬ (Nat.ceil (Real.sqrt (target : ℝ))) ^ 2 < target := by
          rw [square_lt_iff_lt_ceil_sqrt]
          exact Nat.lt_irrefl _
        simp only [squareRootStep, hmin, hsquare, ↓reduceIte, hnext]


-- @@ L1818-1824 verbatim
private theorem ceil_sqrt_le_target (target : ℕ) :
    Nat.ceil (Real.sqrt (target : ℝ)) ≤ target := by
  apply Nat.ceil_le.mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hsq : target ≤ target ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self target
  exact_mod_cast hsq


-- @@ L1826-1830 verbatim
private theorem squareRootStep_iterate_target (target : ℕ) :
    ((squareRootStep target)^[target]) 0 =
      Nat.ceil (Real.sqrt (target : ℝ)) := by
  rw [squareRootStep_iterate,
    Nat.min_eq_right (ceil_sqrt_le_target target)]


-- @@ L1832-1838 verbatim
/-- GapCVP reduction support. -/
@[expose] def squareRootFoldPreparation
    (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  target input ++ false ::
    (lengthPrefixedWord (squareRootAnchor (target input)) ++
      lengthPrefixedWord [])


-- @@ L1840-1861 verbatim
/-- GapCVP reduction support. -/
noncomputable def squareRootFoldPreparationComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (squareRootFoldPreparation target) := by
  have hanchor := GapCVP.TMComposition.computableInPolyTime
    (squareRootAnchorComputable computer)
    CLStructuralPrefixWriter.structuralPrefixWriterComputable
  have hseed := pointwiseAppendComputable hanchor
    (SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      (lengthPrefixedWord []))
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hseed (prependBitComputable false)
  have hphysical := pointwiseAppendComputable computer hdelimited
  change
    BitTM
      (fun input : List Bool =>
        target input ++ false ::
          (lengthPrefixedWord (squareRootAnchor (target input)) ++
            lengthPrefixedWord []))
  exact hphysical


-- @@ L1863-1870 verbatim
private def ceilSquareRootUnaryOutput
    (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldContents
    (firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput squareRootCandidate)
        (squareRootFoldPreparation target input)))


-- @@ L1872-1893 verbatim
private noncomputable def ceilSquareRootUnaryComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (ceilSquareRootUnaryOutput target) := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    (squareRootFoldPreparationComputable computer)
    (sourceAnchoredGridRecordFoldComputable
      squareRootCandidateComputable)
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    hfold firstFieldSuffixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hsuffix firstFieldContentsComputable
  change
    BitTM
      (fun input : List Bool =>
        firstFieldContents
          (firstFieldSuffix
            (boundedRecordFoldOutput
              (sourceAnchoredGridRecordRotationOutput squareRootCandidate)
              (squareRootFoldPreparation target input))))
  exact hphysical


-- @@ L1895-1926 verbatim
private theorem ceilSquareRootUnaryOutput_valid
    (target : List Bool → List Bool)
    (input : List Bool) (weight : ℕ)
    (hweight : target input = List.replicate weight true) :
    ceilSquareRootUnaryOutput target input =
      List.replicate (Nat.ceil (Real.sqrt (weight : ℝ))) true := by
  unfold ceilSquareRootUnaryOutput squareRootFoldPreparation
  rw [hweight]
  change
    firstFieldContents
      (firstFieldSuffix
        (boundedRecordFoldOutput
          (sourceAnchoredGridRecordRotationOutput squareRootCandidate)
          (unaryBoundedFoldWord weight
            (lengthPrefixedWord
                (squareRootAnchor (List.replicate weight true)) ++
              lengthPrefixedWord [])))) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  change
    firstFieldContents
      (firstFieldSuffix
        (((sourceAnchoredGridRecordRotationOutput
          squareRootCandidate)^[weight])
          (lengthPrefixedWord
              (squareRootAnchor (List.replicate weight true)) ++
            lengthPrefixedWord (List.replicate 0 true)))) = _
  rw [squareRootRotation_iterate weight 0 weight (Nat.zero_le _),
    squareRootStep_iterate_target]
  rw [firstFieldSuffix_valid]
  simpa only [List.append_nil] using
    firstFieldContents_valid
      (List.replicate (Nat.ceil (Real.sqrt (weight : ℝ))) true) []


-- @@ L1928-1934 verbatim
/-- GapCVP reduction support. -/
def ceilSquareRootAtomicRationalOutput
    (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  structuralAtomicNaturalWord
    ((rationalRadiusUnaryOutput
      (true :: ceilSquareRootUnaryOutput target input)).tail)


-- @@ L1936-1957 verbatim
/-- GapCVP reduction support. -/
noncomputable def ceilSquareRootAtomicRationalComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (ceilSquareRootAtomicRationalOutput target) := by
  have hmarked := GapCVP.TMComposition.computableInPolyTime
    (ceilSquareRootUnaryComputable computer)
    (prependBitComputable true)
  have hrational := GapCVP.TMComposition.computableInPolyTime
    hmarked rationalRadiusUnaryComputable
  have htail := GapCVP.TMComposition.computableInPolyTime
    hrational radiusMarkerTailComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    htail structuralAtomicNaturalWriterComputable
  change
    BitTM
      (fun input : List Bool =>
        structuralAtomicNaturalWord
          ((rationalRadiusUnaryOutput
            (true :: ceilSquareRootUnaryOutput target input)).tail))
  simpa only [Function.comp_def] using hphysical


-- @@ L1959-1972 verbatim
theorem ceilSquareRootAtomicRationalOutput_valid
    (target : List Bool → List Bool)
    (input : List Bool) (weight : ℕ)
    (hweight : target input = List.replicate weight true) :
    ceilSquareRootAtomicRationalOutput target input =
      BinaryEncoding.encodeAtomic
        (Nat.ceil (Real.sqrt (weight : ℝ)) : ℚ) := by
  unfold ceilSquareRootAtomicRationalOutput
  rw [ceilSquareRootUnaryOutput_valid target input weight hweight,
    rationalRadiusUnaryOutput_marked]
  simp only [List.tail_cons]
  rw [structuralAtomicNaturalWord_eq_prefix,
    sourceRationalNatCast_atomic]
  simp only [List.length_replicate]


-- @@ L1974-1974 verbatim
end BinaryRadiusTM


-- @@ L1976-1976 verbatim
namespace GaussianPivotScheduleTM


-- @@ L1978-1978 verbatim
open Turing


-- @@ L1980-1984 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryGaussianPivotWord (candidates : List Bool) : List Bool :=
  match candidates.findIdx? id with
  | none => [false]
  | some index => true :: List.replicate index true


-- @@ L1986-2001 verbatim
@[simp] private theorem binaryGaussianPivotWord_found
    (zeros : ℕ) (remaining : List Bool) :
    binaryGaussianPivotWord
        (List.replicate zeros false ++ true :: remaining) =
      true :: List.replicate zeros true := by
  have hfind :
      (List.replicate zeros false ++ true :: remaining).findIdx? id =
        some zeros := by
    induction zeros with
    | zero => simp only [List.replicate_zero, List.nil_append, List.findIdx?_cons, id_eq,
        ↓reduceIte]
    | succ zeros ih =>
        simp only [List.replicate_succ, List.cons_append, List.findIdx?_cons, id_eq,
            Bool.false_eq_true, ↓reduceIte,
            ih, Option.map_some]
  simp only [binaryGaussianPivotWord, hfind]


-- @@ L2003-2014 verbatim
@[simp] private theorem binaryGaussianPivotWord_absent
    (zeros : ℕ) :
    binaryGaussianPivotWord (List.replicate zeros false) = [false] := by
  have hfind :
      (List.replicate zeros false).findIdx? id = none := by
    induction zeros with
    | zero => simp only [List.replicate_zero, List.findIdx?_nil]
    | succ zeros ih =>
        simp only [List.replicate_succ, List.findIdx?_cons, id_eq, Bool.false_eq_true, ↓reduceIte,
            ih,
            Option.map_none]
  simp only [binaryGaussianPivotWord, hfind]


-- @@ L2016-2022 verbatim
private def pivotPeek (stack : Fin 2)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)


-- @@ L2024-2027 verbatim
private def pivotGoto (phase : Fin 3) :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => phase))


-- @@ L2029-2038 verbatim
private def pivotScanStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  pivotPeek 0
    (.branch (fun candidate => candidate.getD false)
      (.pop 0 (fun _ _ => none)
        (.push 1 (fun _ => true) (pivotGoto 1)))
      (.pop 0 (fun _ _ => none)
        (.push 1 (fun _ => true) (pivotGoto 0))))
    (pivotGoto 2)


-- @@ L2040-2045 verbatim
private def pivotSuccessDrainStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  pivotPeek 0
    (.pop 0 (fun _ _ => none) (pivotGoto 1))
    (.load (fun _ => none) .halt)


-- @@ L2047-2052 verbatim
private def pivotFailureStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  pivotPeek 1
    (.pop 1 (fun _ _ => none) (pivotGoto 2))
    (.push 1 (fun _ => false) (.load (fun _ => none) .halt))


-- @@ L2054-2066 verbatim
private abbrev binaryGaussianPivotMachine : Turing.FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 3) then pivotScanStatement
    else if phase = (1 : Fin 3) then pivotSuccessDrainStatement
    else pivotFailureStatement


-- @@ L2068-2073 verbatim
private def pivotConfiguration
    (phase : Fin 3) (input output : List Bool) :
    binaryGaussianPivotMachine.Cfg where
  l := some phase
  var := none
  stk := ![input, output]


-- @@ L2075-2084 verbatim
private theorem binaryGaussianPivotMachine_init
    (input : List Bool) :
    Turing.initList binaryGaussianPivotMachine input =
      pivotConfiguration 0 input [] := by
  simp only [binaryGaussianPivotMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq,
      dite_eq_ite,
      pivotConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp


-- @@ L2086-2098 verbatim
/-- Executes the `binaryGaussianPivotStepTac` machine-step simplifier. -/
macro "binaryGaussianPivotStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [binaryGaussianPivotMachine, pivotConfiguration,
          pivotPeek, pivotGoto, pivotScanStatement,
          pivotSuccessDrainStatement, pivotFailureStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))


-- @@ L2100-2105 expanded
private theorem pivot_scan_false (input output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 0 (false :: input) output) =
      some (pivotConfiguration 0 input (true :: output)) :=
  by
  (first
    | rfl
    |
      (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
              pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
              Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L2107-2112 expanded
private theorem pivot_scan_true (input output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 0 (true :: input) output) =
      some (pivotConfiguration 1 input (true :: output)) :=
  by
  (first
    | rfl
    |
      (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
              pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
              Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L2114-2118 expanded
private theorem pivot_scan_missing (output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 0 [] output) =
      some (pivotConfiguration 2 [] output) :=
  by
  (first
    | rfl
    |
      (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
              pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
              Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L2120-2125 expanded
private theorem pivot_success_drain_step (bit : Bool) (input output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 1 (bit :: input) output) =
      some (pivotConfiguration 1 input output) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
                pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
                Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L2127-2131 expanded
private theorem pivot_success_finish (output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 1 [] output) =
      some (Turing.haltList binaryGaussianPivotMachine output) :=
  by
  (first
    | rfl
    |
      (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
              pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
              Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L2133-2138 expanded
private theorem pivot_failure_drain_step (bit : Bool) (output : List Bool) :
    binaryGaussianPivotMachine.step (pivotConfiguration 2 [] (bit :: output)) =
      some (pivotConfiguration 2 [] output) :=
  by
  cases bit <;>
    (first
      | rfl
      |
        (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
                pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
                Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
              try { congr 2; funext stack;
                fin_cases stack <;>
                  (first
                    | rfl
                    | simp [Function.update])
              } <;>
            try rfl))


-- @@ L2140-2144 expanded
private theorem pivot_failure_finish :
    binaryGaussianPivotMachine.step (pivotConfiguration 2 [] []) =
      some (Turing.haltList binaryGaussianPivotMachine [false]) :=
  by
  (first
    | rfl
    |
      (simp [binaryGaussianPivotMachine, pivotConfiguration, pivotPeek, pivotGoto,
              pivotScanStatement, pivotSuccessDrainStatement, pivotFailureStatement,
              Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
            try { congr 2; funext stack;
              fin_cases stack <;>
                (first
                  | rfl
                  | simp [Function.update])
            } <;>
          try rfl))


-- @@ L2146-2159 verbatim
private def pivot_successDrainTrace
    (input output : List Bool) :
    EvalsToInTime binaryGaussianPivotMachine.step (pivotConfiguration 1 input output)
      (some (Turing.haltList binaryGaussianPivotMachine output))
      (input.length + 1) := by
  induction input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (pivot_success_finish output)
  | cons bit input ih =>
      have first := oneStep _ _ (pivot_success_drain_step bit input output)
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using full


-- @@ L2161-2174 verbatim
private def pivot_failureTrace
    (output : List Bool) :
    EvalsToInTime binaryGaussianPivotMachine.step (pivotConfiguration 2 [] output)
      (some (Turing.haltList binaryGaussianPivotMachine [false]))
      (output.length + 1) := by
  induction output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using oneStep _ _
          pivot_failure_finish
  | cons bit output ih =>
      have first := oneStep _ _ (pivot_failure_drain_step bit output)
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using full


-- @@ L2176-2199 verbatim
private def pivot_foundTrace
    (zeros : ℕ) (remaining output : List Bool) :
    EvalsToInTime binaryGaussianPivotMachine.step (pivotConfiguration 0
        (List.replicate zeros false ++ true :: remaining) output)
      (some (Turing.haltList binaryGaussianPivotMachine
        (true :: List.replicate zeros true ++ output)))
      (zeros + remaining.length + 2) := by
  induction zeros generalizing output with
  | zero =>
      have first := oneStep _ _ (pivot_scan_true remaining output)
      have rest := pivot_successDrainTrace remaining (true :: output)
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first rest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, List.cons_append,
          zero_add,
          Nat.add_assoc, Nat.reduceAdd] using full
  | succ zeros ih =>
      have first := oneStep _ _ (pivot_scan_false
          (List.replicate zeros false ++ true :: remaining) output)
      have rest := ih (true :: output)
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first rest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.add_assoc, Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons]
              using full


-- @@ L2201-2221 verbatim
private def pivot_absentTrace
    (zeros : ℕ) (output : List Bool) :
    EvalsToInTime binaryGaussianPivotMachine.step
      (pivotConfiguration 0 (List.replicate zeros false) output)
      (some (Turing.haltList binaryGaussianPivotMachine [false]))
      (2 * zeros + output.length + 2) := by
  induction zeros generalizing output with
  | zero =>
      have first := oneStep _ _ (pivot_scan_missing output)
      have rest := pivot_failureTrace output
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first rest
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, mul_zero, zero_add, Nat.add_assoc,
          Nat.reduceAdd] using full
  | succ zeros ih =>
      have first := oneStep _ _ (pivot_scan_false (List.replicate zeros false) output)
      have rest := ih (true :: output)
      have full := EvalsToInTime.trans binaryGaussianPivotMachine.step _ _ _ _ _ first rest
      have bounded := rebound (newBudget := 2 * (zeros + 1) + output.length + 2)
        full (by simp only [List.length_cons, add_le_add_iff_right, Nat.reduceLeDiff,
            Order.add_one_le_iff]; omega)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ] using bounded


-- @@ L2223-2226 verbatim
private inductive BinaryGaussianPivotInputShape (input : List Bool) : Type where
  | found (zeros : ℕ) (remaining : List Bool)
      (shape : input = List.replicate zeros false ++ true :: remaining)
  | absent (shape : input = List.replicate input.length false)


-- @@ L2228-2246 verbatim
private def binaryGaussianPivotInputShape
    (input : List Bool) : BinaryGaussianPivotInputShape input := by
  induction input with
  | nil => exact .absent rfl
  | cons bit remaining ih =>
      cases bit with
      | true => exact .found 0 remaining rfl
      | false =>
          cases ih with
          | found zeros tail hshape =>
              exact .found (zeros + 1) tail (by
                change false :: remaining =
                  false :: (List.replicate zeros false ++ true :: tail)
                exact congrArg (List.cons false) hshape)
          | absent hshape =>
              exact .absent (by
                change false :: remaining =
                  false :: List.replicate remaining.length false
                exact congrArg (List.cons false) hshape)


-- @@ L2248-2271 verbatim
private def binaryGaussianPivot_totalTrace (input : List Bool) :
    EvalsToInTime binaryGaussianPivotMachine.step (pivotConfiguration 0 input [])
      (some (Turing.haltList binaryGaussianPivotMachine
        (binaryGaussianPivotWord input)))
      (2 * input.length + 3) := by
  cases binaryGaussianPivotInputShape input with
  | found zeros remaining hshape =>
      subst input
      have full := pivot_foundTrace zeros remaining []
      simp only [List.append_nil] at full
      rw [binaryGaussianPivotWord_found]
      exact rebound full (by
        simp only [List.length_append, List.length_replicate,
          List.length_cons]
        omega)
  | absent hshape =>
      have hword : binaryGaussianPivotWord input = [false] := by
        rw [hshape, binaryGaussianPivotWord_absent]
      have full := pivot_absentTrace input.length []
      rw [← hshape] at full
      rw [hword]
      exact rebound full (by
        simp only [List.length_nil, Nat.add_zero]
        omega)


-- @@ L2273-2294 verbatim
/-- GapCVP reduction support. -/
noncomputable def binaryGaussianPivotComputable :
    BitTM
      binaryGaussianPivotWord where
  tm := binaryGaussianPivotMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := {
    steps := (binaryGaussianPivot_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, binaryGaussianPivotMachine_init,
              Option.map_some] using
          (binaryGaussianPivot_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (binaryGaussianPivot_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }


-- @@ L2296-2302 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianPivotCandidates
    {m n : ℕ} (state : GapCVP.Core.EffectiveBinaryGaussian.State m n)
    (column : Fin n) : List Bool :=
  (List.finRange m).map (fun row =>
    decide (state.nextPivot ≤ row.val ∧
      state.system.check row column = (1 : ZMod 2)))


-- @@ L2304-2304 verbatim
end GaussianPivotScheduleTM


-- @@ L2306-2306 verbatim
namespace GaussianPackedPivotColumnTM


-- @@ L2308-2308 verbatim
open Turing GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L2309-2309 verbatim
open GapCVP.SourceFourFamilyMarkerRotationTM

-- @@ L2310-2310 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM


-- @@ L2312-2324 verbatim
private theorem binaryGaussianPivotEligibilityWord_length
    (input : List Bool) :
    (sourceFourFamilyBooleanAndPairWord input).length = 1 := by
  cases input with
  | nil => rfl
  | cons first remaining =>
      cases first with
      | false => rfl
      | true =>
          cases remaining with
          | nil => rfl
          | cons second remaining =>
              cases second <;> rfl


-- @@ L2326-2331 verbatim
/-- GapCVP reduction support. -/
def binaryGaussianPackedPivotCandidateOutput :
    List Bool → List Bool :=
  boundedRecordFoldOutput
    (fourFamilyOriginalMarkerRotationOutput
      sourceFourFamilyBooleanAndPairWord)


-- @@ L2333-2338 verbatim
private noncomputable def binaryGaussianPackedPivotCandidateComputable :
    BitTM
      binaryGaussianPackedPivotCandidateOutput :=
  fourFamilyOriginalMarkerFoldComputable
    sourceFourFamilyBooleanAndPairComputable
    (fun input => (binaryGaussianPivotEligibilityWord_length input).le)


-- @@ L2340-2344 verbatim
/-- GapCVP reduction support. -/
@[expose]
def binaryGaussianPackedPivotRowQuery
    (eligible entry : Bool) (source : List Bool) : List Bool :=
  eligible :: entry :: source


-- @@ L2346-2353 verbatim
/-- GapCVP reduction support. -/
@[expose]
def binaryGaussianPackedPivotColumnWord
    (rows : List (Bool × Bool)) (source : List Bool) : List Bool :=
  unaryBoundedFoldWord rows.length
    (sourceMixedRadixOriginalSourceQueryStream
      (rows.map (fun row =>
        binaryGaussianPackedPivotRowQuery row.1 row.2 source)))


-- @@ L2355-2360 verbatim
@[simp] private theorem binaryGaussianPivotEligibilityWord_valid
    (eligible entry : Bool) (source : List Bool) :
    sourceFourFamilyBooleanAndPairWord
        (binaryGaussianPackedPivotRowQuery eligible entry source) =
      [eligible && entry] := by
  cases eligible <;> cases entry <;> rfl


-- @@ L2362-2395 verbatim
@[simp] theorem binaryGaussianPackedPivotCandidateOutput_valid
    (rows : List (Bool × Bool)) (source : List Bool) :
    binaryGaussianPackedPivotCandidateOutput
        (binaryGaussianPackedPivotColumnWord rows source) =
      rows.map (fun row => row.1 && row.2) := by
  unfold binaryGaussianPackedPivotCandidateOutput
    binaryGaussianPackedPivotColumnWord
  have h := boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
    sourceFourFamilyBooleanAndPairWord
    (rows.map (fun row =>
      binaryGaussianPackedPivotRowQuery row.1 row.2 source)) []
  have hflatten :
      rows.flatMap (fun row => [row.1 && row.2]) =
        rows.map (fun row => row.1 && row.2) := by
    calc
      rows.flatMap (fun row => [row.1 && row.2]) =
          (rows.map (fun row => row.1 && row.2)).flatMap
            (fun bit => [bit]) := by
              simp only [List.flatMap_map]
      _ = rows.map (fun row => row.1 && row.2) :=
        List.flatMap_singleton' _
  calc
    boundedRecordFoldOutput
        (fourFamilyOriginalMarkerRotationOutput
          sourceFourFamilyBooleanAndPairWord)
        (unaryBoundedFoldWord rows.length
          (sourceMixedRadixOriginalSourceQueryStream
            (rows.map (fun row =>
              binaryGaussianPackedPivotRowQuery row.1 row.2 source)))) =
        rows.flatMap (fun row => [row.1 && row.2]) := by
          simpa only [List.length_map, List.append_nil, fourFamilyOriginalMarkerStream,
              List.flatMap_map,
              binaryGaussianPivotEligibilityWord_valid, List.nil_append] using h
    _ = rows.map (fun row => row.1 && row.2) := hflatten


-- @@ L2397-2397 verbatim
end GaussianPackedPivotColumnTM


-- @@ L2399-2399 verbatim
namespace GaussianAdaptivePivotStepTM


-- @@ L2401-2401 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L2402-2402 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceFourFamilyMarkerRotationTM

-- @@ L2403-2403 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.CLStructuralPrefixWriter

-- @@ L2404-2404 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFlatAdjacentRecordSwapTM

-- @@ L2405-2405 verbatim
open GapCVP.CNFFlatAdjacentConditionalSwapTM GapCVP.GaussianRowWorker


-- @@ L2407-2413 verbatim
/-- GapCVP reduction support. -/
@[expose]
def binaryGaussianDynamicBranchOutput
    (selector : List Bool → Bool)
    (valid fallback : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  if selector input then valid input else fallback input


-- @@ L2415-2462 verbatim
/-- GapCVP reduction support. -/
noncomputable def binaryGaussianDynamicBranchComputable
    {selector : List Bool → Bool}
    {valid fallback : List Bool → List Bool}
    (selection : BitTM
      (fun input => selector input :: input))
    (hvalid : BitTM valid)
    (hfallback : BitTM fallback) :
    BitTM
      (binaryGaussianDynamicBranchOutput selector valid fallback) := by
  have hmarker := GapCVP.TMComposition.computableInPolyTime
    selection binaryGaussianFirstCellComputable
  have hvalidPrefix := GapCVP.TMComposition.computableInPolyTime
    hvalid structuralPrefixWriterComputable
  have hfallbackPrefix := GapCVP.TMComposition.computableInPolyTime
    hfallback structuralPrefixWriterComputable
  have hbranches := pointwiseAppendComputable
    hfallbackPrefix hvalidPrefix
  have hselected := pointwiseAppendComputable
    hmarker hbranches
  have hswap := GapCVP.TMComposition.computableInPolyTime
    hselected flatAdjacentConditionalSwapComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hswap firstFieldContentsComputable
  convert hphysical using 1
  funext input
  change
    binaryGaussianDynamicBranchOutput selector valid fallback input =
      firstFieldContents
        (flatAdjacentConditionalSwapOutput
          (binaryGaussianFirstCellWord (selector input :: input) ++
            (lengthPrefixedWord (fallback input) ++
              lengthPrefixedWord (valid input))))
  cases hdecision : selector input with
  | false =>
      simp only [binaryGaussianDynamicBranchOutput, hdecision, Bool.false_eq_true, ↓reduceIte,
          flatAdjacentConditionalSwapOutput, binaryGaussianFirstCellWord_valid, List.cons_append,
              List.nil_append,
          firstFieldContents_valid]
  | true =>
      simp only [binaryGaussianDynamicBranchOutput,
        hdecision, ↓reduceIte, binaryGaussianFirstCellWord_valid,
        List.singleton_append, flatAdjacentConditionalSwapOutput]
      have hswap := flatAdjacentRecordSwapOutput_records
        (fallback input) (valid input) []
      simp only [List.append_nil] at hswap
      rw [hswap]
      simp only [firstFieldContents_valid]


-- @@ L2464-2467 verbatim
private theorem binaryGaussianFirstFieldSuffix_nonexpansive
    (input : List Bool) :
    (firstFieldSuffix input).length ≤ input.length :=
  sourceFourFamilyFirstFieldSuffix_length_le input


-- @@ L2469-2472 verbatim
private theorem binaryGaussianFirstFieldSuffix_polynomialStates :
    PolynomiallyBoundedFoldStates firstFieldSuffix Polynomial.X :=
  GapCVP.Factor400BinarySourceTM.boundedFoldStates_of_nonexpansive
    binaryGaussianFirstFieldSuffix_nonexpansive


-- @@ L2474-2477 verbatim
/-- GapCVP reduction support. -/
def binaryGaussianIndexedBatchOutput : List Bool → List Bool :=
  firstFieldContents ∘
    boundedRecordFoldOutput firstFieldSuffix


-- @@ L2479-2487 verbatim
/-- GapCVP reduction support. -/
noncomputable def binaryGaussianIndexedBatchComputable :
    BitTM
      binaryGaussianIndexedBatchOutput := by
  have hskip := boundedDependentRecordFoldComputable
    firstFieldSuffixComputable Polynomial.X
    binaryGaussianFirstFieldSuffix_polynomialStates
  exact GapCVP.TMComposition.computableInPolyTime
    hskip firstFieldContentsComputable


-- @@ L2489-2493 verbatim
/-- GapCVP reduction support. -/
@[expose]
def binaryGaussianPivotBatchStream
    (batches : List (List Bool)) : List Bool :=
  sourceMixedRadixOriginalSourceQueryStream batches


-- @@ L2495-2520 verbatim
private theorem binaryGaussian_skipBatchRecords
    (batches : List (List Bool)) (suffix : List Bool)
    (index : ℕ) (hindex : index ≤ batches.length) :
    ((firstFieldSuffix^[index])
      (binaryGaussianPivotBatchStream batches ++ suffix)) =
      binaryGaussianPivotBatchStream (batches.drop index) ++ suffix := by
  induction index generalizing batches with
  | zero => simp only [Function.iterate_zero, id_eq, List.drop_zero]
  | succ index ih =>
      cases batches with
      | nil => simp only [List.length_nil, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, one_ne_zero,
          and_false] at hindex
      | cons batch remaining =>
          have hremaining : index ≤ remaining.length := by
            simpa only [List.length_cons, add_le_add_iff_right] using hindex
          rw [Function.iterate_succ_apply]
          have hprefix :
              binaryGaussianPivotBatchStream (batch :: remaining) ++ suffix =
                lengthPrefixedWord batch ++
                  (binaryGaussianPivotBatchStream remaining ++ suffix) := by
            simp only [binaryGaussianPivotBatchStream, sourceMixedRadixOriginalSourceQueryStream,
                List.flatMap_cons,
                List.append_assoc]
          rw [hprefix, firstFieldSuffix_valid]
          rw [ih remaining hremaining]
          simp only [List.drop_succ_cons]


-- @@ L2522-2549 verbatim
theorem binaryGaussianIndexedBatchOutput_valid
    (batches : List (List Bool)) (suffix : List Bool)
    (index : ℕ) (hindex : index < batches.length) :
    binaryGaussianIndexedBatchOutput
        (unaryBoundedFoldWord index
          (binaryGaussianPivotBatchStream batches ++ suffix)) =
      batches[index] := by
  unfold binaryGaussianIndexedBatchOutput
    boundedRecordFoldOutput
  simp only [Function.comp_apply, parseUnaryBoundedFold_word]
  rw [binaryGaussian_skipBatchRecords batches suffix index
    (Nat.le_of_lt hindex)]
  have hdrop :
      batches.drop index =
        batches[index] :: batches.drop (index + 1) := by
    exact (List.cons_getElem_drop_succ
      (l := batches) (n := index) (h := hindex)).symm
  rw [hdrop]
  change
    firstFieldContents
      ((lengthPrefixedWord batches[index] ++
        binaryGaussianPivotBatchStream
          (batches.drop (index + 1))) ++ suffix) =
      batches[index]
  rw [List.append_assoc]
  exact firstFieldContents_valid batches[index]
    (binaryGaussianPivotBatchStream
      (batches.drop (index + 1)) ++ suffix)


-- @@ L2551-2551 verbatim
end GaussianAdaptivePivotStepTM


-- @@ L2553-2553 verbatim
namespace BinaryGaussianStructuralAtomTM


-- @@ L2555-2555 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L2556-2556 verbatim
open GapCVP.SourceWholeOutputAssemblyTM

-- @@ L2557-2557 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L2558-2558 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L2559-2559 verbatim
open GapCVP.BinaryStructuralRecordTM


-- @@ L2561-2563 verbatim
/-- GapCVP reduction support. -/
def structuralRankUnary (query : List Bool) : List Bool :=
  firstFieldContents query


-- @@ L2565-2569 verbatim
/-- GapCVP reduction support. -/
noncomputable def structuralRankUnaryComputable :
    BitTM
      structuralRankUnary :=
  firstFieldContentsComputable


-- @@ L2571-2573 verbatim
/-- GapCVP reduction support. -/
def structuralRankOriginalSource (query : List Bool) : List Bool :=
  firstFieldSuffix (firstFieldSuffix query)


-- @@ L2575-2590 verbatim
/-- GapCVP reduction support. -/
noncomputable def structuralRankOriginalSourceComputable :
    BitTM
      structuralRankOriginalSource := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  change
    BitTM
      (fun query : List Bool =>
        firstFieldSuffix (firstFieldSuffix query))
  change
    BitTM
      (fun query : List Bool =>
        firstFieldSuffix (firstFieldSuffix query))
    at hphysical
  exact hphysical


-- @@ L2592-2602 verbatim
@[simp] theorem structuralRankUnary_query
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    structuralRankUnary
      (constructiveStructuralRankQuery dimension input rank) =
        List.replicate rank true := by
  unfold structuralRankUnary constructiveStructuralRankQuery
  exact firstFieldContents_valid
    (List.replicate rank true)
    (sourceQaryMaskDynamicGridBaseSource
      (constructiveStructuralRecordWidth dimension) input)


-- @@ L2604-2617 verbatim
@[simp] theorem structuralRankOriginalSource_query
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    structuralRankOriginalSource
      (constructiveStructuralRankQuery dimension input rank) = input := by
  unfold structuralRankOriginalSource
    constructiveStructuralRankQuery
    sourceQaryMaskDynamicGridBaseSource
  rw [firstFieldSuffix_valid
    (List.replicate rank true)
    (lengthPrefixedWord
      ((constructiveStructuralRecordWidth dimension).output input) ++ input)]
  exact firstFieldSuffix_valid
    ((constructiveStructuralRecordWidth dimension).output input) input


-- @@ L2619-2624 verbatim
/-- GapCVP reduction support. -/
def structuralRankLessBit
    (bound : List Bool → List Bool)
    (query : List Bool) : Bool :=
  (fourFamilyComputedUnaryLessBitOutput
    structuralRankUnary bound query).headD false


-- @@ L2626-2643 verbatim
private theorem structuralRankLessMarker_eq
    (bound : List Bool → List Bool)
    (query : List Bool) :
    fourFamilyComputedUnaryLessBitOutput
        structuralRankUnary bound query =
      [structuralRankLessBit bound query] := by
  have hlength := fourFamilyComputedUnaryLessBitOutput_length
    structuralRankUnary bound query
  cases hword : fourFamilyComputedUnaryLessBitOutput
      structuralRankUnary bound query with
  | nil => simp only [hword, List.length_nil, zero_ne_one] at hlength
  | cons bit remaining =>
      cases remaining with
      | nil => simp only [structuralRankLessBit, hword, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some]
      | cons next tail => simp only [hword, List.length_cons, Nat.add_eq_right,
          Nat.add_eq_zero_iff, List.length_eq_zero_iff,
                              one_ne_zero, and_false] at hlength


-- @@ L2645-2671 verbatim
/-- GapCVP reduction support. -/
noncomputable def structuralRankLessSelectionComputable
    {bound : List Bool → List Bool}
    (hbound : BitTM bound) :
    BitTM
      (fun query : List Bool =>
        structuralRankLessBit bound query :: query) := by
  have hmarker := fourFamilyComputedUnaryLessBitComputable
    structuralRankUnaryComputable hbound
  have hphysical := pointwiseAppendComputable hmarker
    (Turing.idComputableInPolyTime bitEncoding)
  have heq :
      (fun query : List Bool =>
        fourFamilyComputedUnaryLessBitOutput
          structuralRankUnary bound query ++ query) =
      (fun query : List Bool =>
        structuralRankLessBit bound query :: query) := by
    funext query
    rw [structuralRankLessMarker_eq bound query]
    rfl
  change
    BitTM
      (fun query : List Bool =>
        fourFamilyComputedUnaryLessBitOutput
          structuralRankUnary bound query ++ query)
    at hphysical
  rwa [heq] at hphysical


-- @@ L2673-2683 verbatim
theorem structuralRankLessBit_valid
    (bound : List Bool → List Bool)
    (query : List Bool) (rank ceiling : ℕ)
    (hrank : structuralRankUnary query = List.replicate rank true)
    (hbound : bound query = List.replicate ceiling true) :
    structuralRankLessBit bound query = decide (rank < ceiling) := by
  have hmarker := fourFamilyComputedUnaryLessBitOutput_valid
    structuralRankUnary bound query rank ceiling hrank hbound
  unfold structuralRankLessBit
  rw [hmarker]
  rfl


-- @@ L2685-2687 verbatim
/-- GapCVP reduction support. -/
def structuralRankOneBound (_query : List Bool) : List Bool :=
  [true]


-- @@ L2689-2693 verbatim
/-- GapCVP reduction support. -/
noncomputable def structuralRankOneBoundComputable :
    BitTM
      structuralRankOneBound :=
  SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable [true]


-- @@ L2695-2697 verbatim
/-- GapCVP reduction support. -/
def structuralRankTwoBound (_query : List Bool) : List Bool :=
  [true, true]


-- @@ L2699-2704 verbatim
/-- GapCVP reduction support. -/
noncomputable def structuralRankTwoBoundComputable :
    BitTM
      structuralRankTwoBound :=
  SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
    [true, true]


-- @@ L2706-2716 verbatim
theorem structuralRankOneDecision_query
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    structuralRankLessBit structuralRankOneBound
      (constructiveStructuralRankQuery dimension input rank) =
        decide (rank < 1) :=
  structuralRankLessBit_valid
    structuralRankOneBound
    (constructiveStructuralRankQuery dimension input rank)
    rank 1
    (structuralRankUnary_query dimension input rank) rfl


-- @@ L2718-2728 verbatim
theorem structuralRankTwoDecision_query
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    structuralRankLessBit structuralRankTwoBound
      (constructiveStructuralRankQuery dimension input rank) =
        decide (rank < 2) :=
  structuralRankLessBit_valid
    structuralRankTwoBound
    (constructiveStructuralRankQuery dimension input rank)
    rank 2
    (structuralRankUnary_query dimension input rank) rfl


-- @@ L2730-2730 verbatim
end BinaryGaussianStructuralAtomTM


-- @@ L2732-2732 verbatim
namespace BinaryGaussianStructuralRecordIndex


-- @@ L2734-2734 verbatim
open GapCVP.BinaryEncoding GapCVP.SourceWholeOutputAssemblyTM


-- @@ L2736-2746 verbatim
theorem sourceVectorStructuralRecords_getD
    {α : Type*} [Encodable α]
    (n : ℕ) (values : Fin n → α) (index : Fin n) :
    (sourceVectorStructuralRecords n values).getD index.val [] =
      encodeAtomic (values index) := by
  have hindex : index.val <
      (sourceVectorStructuralRecords n values).length := by
    simpa only [sourceVectorStructuralRecords_length] using index.isLt
  rw [List.getD_eq_getElem
    (sourceVectorStructuralRecords n values) [] hindex]
  simp only [sourceVectorStructuralRecords, List.getElem_ofFn, Fin.eta]


-- @@ L2748-2756 verbatim
private theorem sourceMatrixStructuralRecords_succ
    (m n : ℕ)
    (matrix : Fin (m + 1) → Fin n → ℤ) :
    sourceMatrixStructuralRecords (m + 1) n matrix =
      sourceVectorStructuralRecords n (matrix 0) ++
        sourceMatrixStructuralRecords m n
          (fun row => matrix row.succ) := by
  simp only [sourceMatrixStructuralRecords, sourceVectorStructuralRecords, List.ofFn_succ,
      List.flatten_cons]


-- @@ L2758-2801 verbatim
theorem sourceMatrixStructuralRecords_getD
    (m n : ℕ) (matrix : Fin m → Fin n → ℤ)
    (row : Fin m) (column : Fin n) :
    (sourceMatrixStructuralRecords m n matrix).getD
        (row.val * n + column.val) [] =
      encodeAtomic (matrix row column) := by
  induction m with
  | zero => exact Fin.elim0 row
  | succ m ih =>
      refine Fin.cases ?_ (fun previous => ?_) row
      · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
        rw [sourceMatrixStructuralRecords_succ]
        have hcolumn : column.val <
            (sourceVectorStructuralRecords n (matrix 0)).length := by
          simpa only [sourceVectorStructuralRecords_length] using
            column.isLt
        rw [List.getD_append
          (sourceVectorStructuralRecords n (matrix 0))
          (sourceMatrixStructuralRecords m n
            (fun index => matrix index.succ))
          [] column.val hcolumn]
        exact sourceVectorStructuralRecords_getD
          n (matrix 0) column
      · rw [sourceMatrixStructuralRecords_succ]
        have hprefix :
            (sourceVectorStructuralRecords n (matrix 0)).length ≤
              previous.succ.val * n + column.val := by
          rw [sourceVectorStructuralRecords_length]
          simp only [Fin.val_succ, Nat.succ_mul]
          omega
        rw [List.getD_append_right
          (sourceVectorStructuralRecords n (matrix 0))
          (sourceMatrixStructuralRecords m n
            (fun index => matrix index.succ))
          [] (previous.succ.val * n + column.val) hprefix]
        rw [sourceVectorStructuralRecords_length]
        have hindex :
            previous.succ.val * n + column.val - n =
              previous.val * n + column.val := by
          simp only [Fin.val_succ, Nat.succ_mul]
          omega
        rw [hindex]
        exact ih (fun index => matrix index.succ)
          previous


-- @@ L2803-2807 verbatim
theorem sourceLatticeStructuralRecords_getD_dimension
    (lattice : GapCVPInstance) :
    (sourceLatticeStructuralRecords lattice).getD 0 [] =
      encodeAtomic lattice.dimension := by
  rfl


-- @@ L2809-2813 verbatim
theorem sourceLatticeStructuralRecords_getD_radius
    (lattice : GapCVPInstance) :
    (sourceLatticeStructuralRecords lattice).getD 1 [] =
      encodeAtomic lattice.radius := by
  rfl


-- @@ L2815-2844 verbatim
theorem sourceLatticeStructuralRecords_getD_target
    (lattice : GapCVPInstance)
    (index : Fin lattice.dimension) :
    (sourceLatticeStructuralRecords lattice).getD
        (2 + index.val) [] =
      encodeAtomic (lattice.target index) := by
  let vector := sourceVectorStructuralRecords
    lattice.dimension lattice.target
  let matrix := sourceMatrixStructuralRecords
    lattice.dimension lattice.dimension (Matrix.of.symm lattice.basis)
  have hsplit : sourceLatticeStructuralRecords lattice =
      [encodeAtomic lattice.dimension, encodeAtomic lattice.radius] ++
        (vector ++ matrix) := by
    simp only [sourceLatticeStructuralRecords, List.cons_append, List.nil_append, vector, matrix]
  rw [hsplit]
  have hprefix :
      ([encodeAtomic lattice.dimension,
        encodeAtomic lattice.radius] : List (List Bool)).length ≤
        2 + index.val := by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
            le_add_iff_nonneg_right, zero_le]
  rw [List.getD_append_right
    [encodeAtomic lattice.dimension, encodeAtomic lattice.radius]
    (vector ++ matrix) [] (2 + index.val) hprefix]
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.add_sub_cancel_left]
  have hindex : index.val < vector.length := by
    simp only [sourceVectorStructuralRecords_length, Fin.is_lt, vector]
  rw [List.getD_append vector matrix [] index.val hindex]
  exact sourceVectorStructuralRecords_getD
    lattice.dimension lattice.target index


-- @@ L2846-2899 verbatim
theorem sourceLatticeStructuralRecords_getD_basis
    (lattice : GapCVPInstance)
    (row column : Fin lattice.dimension) :
    (sourceLatticeStructuralRecords lattice).getD
        (2 + lattice.dimension +
          row.val * lattice.dimension + column.val) [] =
      encodeAtomic (lattice.basis row column) := by
  let vector := sourceVectorStructuralRecords
    lattice.dimension lattice.target
  let matrix := sourceMatrixStructuralRecords
    lattice.dimension lattice.dimension (Matrix.of.symm lattice.basis)
  have hsplit : sourceLatticeStructuralRecords lattice =
      [encodeAtomic lattice.dimension, encodeAtomic lattice.radius] ++
        (vector ++ matrix) := by
    simp only [sourceLatticeStructuralRecords, List.cons_append, List.nil_append, vector, matrix]
  rw [hsplit]
  have hprefix :
      ([encodeAtomic lattice.dimension,
        encodeAtomic lattice.radius] : List (List Bool)).length ≤
        2 + lattice.dimension +
          row.val * lattice.dimension + column.val := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [List.getD_append_right
    [encodeAtomic lattice.dimension, encodeAtomic lattice.radius]
    (vector ++ matrix) []
    (2 + lattice.dimension +
      row.val * lattice.dimension + column.val) hprefix]
  have hfirst :
      2 + lattice.dimension +
          row.val * lattice.dimension + column.val -
        ([encodeAtomic lattice.dimension,
          encodeAtomic lattice.radius] : List (List Bool)).length =
      lattice.dimension + row.val * lattice.dimension + column.val := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hfirst]
  have hvector : vector.length ≤
      lattice.dimension + row.val * lattice.dimension + column.val := by
    simp only [vector, sourceVectorStructuralRecords_length]
    omega
  rw [List.getD_append_right vector matrix []
    (lattice.dimension + row.val * lattice.dimension + column.val)
    hvector]
  have hsecond :
      lattice.dimension + row.val * lattice.dimension + column.val -
          vector.length =
        row.val * lattice.dimension + column.val := by
    simp only [vector, sourceVectorStructuralRecords_length]
    omega
  rw [hsecond]
  exact sourceMatrixStructuralRecords_getD
    lattice.dimension lattice.dimension (Matrix.of.symm lattice.basis)
      row column


-- @@ L2901-2901 verbatim
end BinaryGaussianStructuralRecordIndex


-- @@ L2903-2903 verbatim
namespace BinaryPhysicalRowBasisDivisionTM


-- @@ L2905-2905 verbatim
open Turing GapCVP.SourceStructuralTuringTM GapCVP.SourceFormulaStructuralDecoder

-- @@ L2906-2906 verbatim
open GapCVP.SourceMachineCert GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L2907-2907 verbatim
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM GapCVP.CNFCappedUnaryPairArithmeticTM


-- @@ L2909-2912 verbatim
private def sourcePhysicalComputedUnaryDivisionQuery
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  dividend input ++ false :: (modulus input ++ false :: input)


-- @@ L2914-2924 verbatim
private noncomputable def sourcePhysicalComputedUnaryDivisionQueryComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (sourcePhysicalComputedUnaryDivisionQuery dividend modulus) := by
  have harchived := pointwiseAppendComputable
    hmodulus (prependBitComputable false)
  have hdelimiter := GapCVP.TMComposition.computableInPolyTime
    harchived (prependBitComputable false)
  exact pointwiseAppendComputable hdividend hdelimiter


-- @@ L2926-2934 verbatim
private theorem sourcePhysicalComputedUnaryDivisionQuery_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hdividend : dividend input = List.replicate first true)
    (hmodulus : modulus input = List.replicate second true) :
    sourcePhysicalComputedUnaryDivisionQuery dividend modulus input =
      sourceUnaryDivisionQuery first second input := by
  simp only [sourcePhysicalComputedUnaryDivisionQuery, hdividend, hmodulus,
      sourceUnaryDivisionQuery]


-- @@ L2936-2939 verbatim
private def sourcePhysicalComputedUnaryDivisionOutput
    (dividend modulus : List Bool → List Bool) : List Bool → List Bool :=
  sourceUnaryDivisionOutput ∘
    sourcePhysicalComputedUnaryDivisionQuery dividend modulus


-- @@ L2941-2950 verbatim
private noncomputable def sourcePhysicalComputedUnaryDivisionComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (sourcePhysicalComputedUnaryDivisionOutput dividend modulus) :=
  GapCVP.TMComposition.computableInPolyTime
    (sourcePhysicalComputedUnaryDivisionQueryComputable
      hdividend hmodulus)
    sourceUnaryDivisionComputable


-- @@ L2952-2966 verbatim
private theorem sourcePhysicalComputedUnaryDivisionOutput_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hpositive : 0 < second)
    (hdividend : dividend input = List.replicate first true)
    (hmodulus : modulus input = List.replicate second true) :
    sourcePhysicalComputedUnaryDivisionOutput dividend modulus input =
      List.replicate (first / second) true ++
        false :: (List.replicate (first % second) true ++
          false :: sourceUnaryDivisionQuery first second input) := by
  unfold sourcePhysicalComputedUnaryDivisionOutput
  rw [Function.comp_apply,
    sourcePhysicalComputedUnaryDivisionQuery_valid
      dividend modulus input first second hdividend hmodulus]
  exact sourceUnaryDivisionOutput_valid first second input hpositive


-- @@ L2968-2974 verbatim
/-- GapCVP reduction support. -/
def sourcePhysicalComputedUnaryQuotient
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (sourcePhysicalComputedUnaryDivisionOutput
      dividend modulus input)).tail


-- @@ L2976-2988 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalComputedUnaryQuotientComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (sourcePhysicalComputedUnaryQuotient dividend modulus) :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (sourcePhysicalComputedUnaryDivisionComputable
        hdividend hmodulus)
      unaryPrefixComputable)
    dropHeadComputable


-- @@ L2990-3002 verbatim
theorem sourcePhysicalComputedUnaryQuotient_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hpositive : 0 < second)
    (hdividend : dividend input = List.replicate first true)
    (hmodulus : modulus input = List.replicate second true) :
    sourcePhysicalComputedUnaryQuotient dividend modulus input =
      List.replicate (first / second) true := by
  unfold sourcePhysicalComputedUnaryQuotient
  rw [sourcePhysicalComputedUnaryDivisionOutput_valid
    dividend modulus input first second hpositive hdividend hmodulus,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L3004-3011 verbatim
/-- GapCVP reduction support. -/
def sourcePhysicalComputedUnaryRemainder
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (sourcePhysicalComputedUnaryDivisionOutput
        dividend modulus input))).tail


-- @@ L3013-3027 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalComputedUnaryRemainderComputable
    {dividend modulus : List Bool → List Bool}
    (hdividend : BitTM dividend)
    (hmodulus : BitTM modulus) :
    BitTM
      (sourcePhysicalComputedUnaryRemainder dividend modulus) :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (GapCVP.TMComposition.computableInPolyTime
        (sourcePhysicalComputedUnaryDivisionComputable
          hdividend hmodulus)
        actualUnaryPrefixSuffixComputable)
      unaryPrefixComputable)
    dropHeadComputable


-- @@ L3029-3042 verbatim
theorem sourcePhysicalComputedUnaryRemainder_valid
    (dividend modulus : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hpositive : 0 < second)
    (hdividend : dividend input = List.replicate first true)
    (hmodulus : modulus input = List.replicate second true) :
    sourcePhysicalComputedUnaryRemainder dividend modulus input =
      List.replicate (first % second) true := by
  unfold sourcePhysicalComputedUnaryRemainder
  rw [sourcePhysicalComputedUnaryDivisionOutput_valid
    dividend modulus input first second hpositive hdividend hmodulus,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L3044-3044 verbatim
end BinaryPhysicalRowBasisDivisionTM


-- @@ L3046-3046 verbatim
namespace GaussianPhysicalWordRankIndexTM


-- @@ L3048-3048 verbatim
open Turing GapCVP.BinaryDimensionTM GapCVP.BinaryGaussianStructuralAtomTM

-- @@ L3049-3049 verbatim
open GapCVP.BinaryStructuralRecordTM GapCVP.SourceWholeOutputAssemblyTM

-- @@ L3050-3050 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM


-- @@ L3052-3055 verbatim
/-- GapCVP reduction support. -/
def factor400PhysicalWordGaussianTargetCoordinateUnary :
    List Bool → List Bool :=
  unarySubtractionOutput structuralRankUnary structuralRankTwoBound


-- @@ L3057-3062 verbatim
/-- GapCVP reduction support. -/
noncomputable def factor400PhysicalWordGaussianTargetCoordinateComputable :
    BitTM
      factor400PhysicalWordGaussianTargetCoordinateUnary :=
  unarySubtractionComputable
    structuralRankUnaryComputable structuralRankTwoBoundComputable


-- @@ L3064-3073 verbatim
theorem factor400PhysicalWordGaussianTargetCoordinateUnary_query
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) :
    factor400PhysicalWordGaussianTargetCoordinateUnary
        (constructiveStructuralRankQuery dimension input rank) =
      List.replicate (rank - 2) true := by
  exact unarySubtractionOutput_valid
    structuralRankUnary structuralRankTwoBound
    (constructiveStructuralRankQuery dimension input rank)
    rank 2 (structuralRankUnary_query dimension input rank) rfl


-- @@ L3075-3075 verbatim
end GaussianPhysicalWordRankIndexTM


-- @@ L3077-3077 verbatim
namespace GaussianReducedConsistencyTM


-- @@ L3079-3079 verbatim
open Turing GapCVP.GaussianRowWorker GapCVP.GaussianPivotScheduleTM

-- @@ L3080-3080 verbatim
open GapCVP.GaussianPackedPivotColumnTM GapCVP.SourceFourFamilyBooleanPredicateTM


-- @@ L3082-3087 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryGaussianReducedConsistencyWord : List Bool → List Bool :=
  sourceFourFamilyBooleanNotWord ∘
    binaryGaussianFirstCellWord ∘
    binaryGaussianPivotWord ∘
    binaryGaussianPackedPivotCandidateOutput


-- @@ L3089-3099 verbatim
/-- GapCVP reduction support. -/
noncomputable def binaryGaussianReducedConsistencyComputable :
    BitTM
      binaryGaussianReducedConsistencyWord := by
  have hpivot := GapCVP.TMComposition.computableInPolyTime
    binaryGaussianPackedPivotCandidateComputable
    binaryGaussianPivotComputable
  have hfirst := GapCVP.TMComposition.computableInPolyTime
    hpivot binaryGaussianFirstCellComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hfirst sourceFourFamilyBooleanNotComputable


-- @@ L3101-3106 verbatim
private def effectiveGaussianReducedConsistencyRows
    (system : GapCVP.Core.BinaryAffineSystem) : List (Bool × Bool) :=
  (List.finRange system.rowCount).map fun row =>
    (decide (system.effectiveGaussianState.nextPivot ≤ row.val),
      decide (system.effectiveGaussianState.system.rhs row =
        (1 : ZMod 2)))


-- @@ L3108-3113 verbatim
/-- GapCVP reduction support. -/
def effectiveGaussianReducedConsistencyQuery
    (system : GapCVP.Core.BinaryAffineSystem)
    (source : List Bool) : List Bool :=
  binaryGaussianPackedPivotColumnWord
    (effectiveGaussianReducedConsistencyRows system) source


-- @@ L3115-3118 verbatim
private def effectiveGaussianReducedInconsistencyBits
    (system : GapCVP.Core.BinaryAffineSystem) : List Bool :=
  (effectiveGaussianReducedConsistencyRows system).map
    (fun row => row.1 && row.2)


-- @@ L3120-3158 verbatim
private theorem effectiveGaussianReducedInconsistencyBits_find_none_iff
    (system : GapCVP.Core.BinaryAffineSystem) :
    (effectiveGaussianReducedInconsistencyBits system).findIdx? id = none ↔
      system.effectiveReducedConsistent = true := by
  rw [List.findIdx?_eq_none_iff,
    GapCVP.Core.BinaryAffineSystem.effectiveReducedConsistent_iff]
  constructor
  · intro hnone row hrow
    have hpair :
        (decide (system.effectiveGaussianState.nextPivot ≤ row.val),
          decide (system.effectiveGaussianState.system.rhs row =
            (1 : ZMod 2))) ∈
          effectiveGaussianReducedConsistencyRows system := by
      apply List.mem_map.mpr
      exact ⟨row, List.mem_finRange row, rfl⟩
    have hbit :
        (decide (system.effectiveGaussianState.nextPivot ≤ row.val) &&
          decide (system.effectiveGaussianState.system.rhs row =
            (1 : ZMod 2))) ∈
          effectiveGaussianReducedInconsistencyBits system := by
      apply List.mem_map.mpr
      exact ⟨_, hpair, rfl⟩
    have hfalse := hnone _ hbit
    have hne :
        system.effectiveGaussianState.system.rhs row ≠
          (1 : ZMod 2) := by
      intro hone
      simp only [hrow, decide_true, hone, Bool.and_self, id_eq, Bool.true_eq_false] at hfalse
    exact GapCVP.Core.EffectiveBinaryGaussian.binary_eq_zero_of_ne_one
      _ hne
  · intro hconsistent bit hbit
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hbit
    obtain ⟨row, _, hrow⟩ := List.mem_map.mp hpair
    subst pair
    by_cases heligible :
      system.effectiveGaussianState.nextPivot ≤ row.val
    · have hrhs := hconsistent row heligible
      simp only [heligible, decide_true, hrhs, zero_ne_one, decide_false, Bool.and_false, id_eq]
    · simp only [heligible, decide_false, Bool.false_and, id_eq]


-- @@ L3160-3202 verbatim
theorem binaryGaussianReducedConsistencyWord_effective
    (system : GapCVP.Core.BinaryAffineSystem)
    (source : List Bool) :
    binaryGaussianReducedConsistencyWord
        (effectiveGaussianReducedConsistencyQuery system source) =
      [system.effectiveReducedConsistent] := by
  change
    sourceFourFamilyBooleanNotWord
      (binaryGaussianFirstCellWord
        (binaryGaussianPivotWord
          (binaryGaussianPackedPivotCandidateOutput
            (effectiveGaussianReducedConsistencyQuery
              system source)))) =
      [system.effectiveReducedConsistent]
  simp only [effectiveGaussianReducedConsistencyQuery]
  rw [binaryGaussianPackedPivotCandidateOutput_valid]
  change
    sourceFourFamilyBooleanNotWord
      (binaryGaussianFirstCellWord
        (binaryGaussianPivotWord
          (effectiveGaussianReducedInconsistencyBits system))) =
      [system.effectiveReducedConsistent]
  cases hfind :
      (effectiveGaussianReducedInconsistencyBits system).findIdx? id with
  | none =>
      have hconsistent : system.effectiveReducedConsistent = true :=
        (effectiveGaussianReducedInconsistencyBits_find_none_iff
          system).mp hfind
      simp only [binaryGaussianPivotWord, hfind, binaryGaussianFirstCellWord_valid,
          sourceFourFamilyBooleanNotWord_bit, Bool.not_false, hconsistent]
  | some index =>
      have hnot : system.effectiveReducedConsistent ≠ true := by
        intro hconsistent
        have hnone :=
          (effectiveGaussianReducedInconsistencyBits_find_none_iff
            system).mpr hconsistent
        simp only [hfind, reduceCtorEq] at hnone
      have hfalse : system.effectiveReducedConsistent = false := by
        cases h : system.effectiveReducedConsistent with
        | false => rfl
        | true => exact (hnot h).elim
      simp only [binaryGaussianPivotWord, hfind, binaryGaussianFirstCellWord_valid,
          sourceFourFamilyBooleanNotWord_bit, Bool.not_true, hfalse]


-- @@ L3204-3204 verbatim
end GaussianReducedConsistencyTM


-- @@ L3206-3206 verbatim
namespace GaussianAdaptiveEliminationCorrectness


-- @@ L3208-3208 verbatim
open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.GaussianPivotScheduleTM

-- @@ L3209-3209 verbatim
open GapCVP.GaussianPackedPivotColumnTM


-- @@ L3211-3222 verbatim
theorem finRange_idxOfOption_eq_some
    {count : ℕ} (row : Fin count) :
    (List.finRange count).idxOf? row = some row.val := by
  apply (List.idxOf?_eq_some_iff).mpr
  have hposition : row.val < (List.finRange count).length := by
    simpa only [List.length_finRange] using row.isLt
  refine ⟨hposition, ?_, ?_⟩
  · simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  · intro position hposition hequal
    have hvalue := congrArg Fin.val hequal
    simp only [List.getElem_finRange, Fin.cast_mk] at hvalue
    omega


-- @@ L3224-3247 verbatim
private theorem effectiveGaussianPivotCandidates_findIdxOption
    {m n : ℕ} (state : State m n) (column : Fin n) :
    (effectiveGaussianPivotCandidates state column).findIdx? id =
      (findPivotOption state column).map Fin.val := by
  unfold effectiveGaussianPivotCandidates findPivotOption
  rw [List.findIdx?_map, List.findIdx?_eq_bind_find?_idxOf?]
  change
    ((List.finRange m).find?
      (fun row => decide
        (state.nextPivot ≤ row.val ∧
          state.system.check row column = (1 : ZMod 2)))).bind
        (fun row => (List.finRange m).idxOf? row) =
      ((List.finRange m).find?
        (fun row => decide
          (state.nextPivot ≤ row.val ∧
            state.system.check row column = (1 : ZMod 2)))).map
        Fin.val
  cases (List.finRange m).find?
      (fun row => decide
        (state.nextPivot ≤ row.val ∧
          state.system.check row column = (1 : ZMod 2))) with
  | none => rfl
  | some row =>
      simpa only [Option.bind_some, Option.map_some] using finRange_idxOfOption_eq_some row


-- @@ L3249-3258 verbatim
theorem binaryGaussianPivotWord_effective
    {m n : ℕ} (state : State m n) (column : Fin n) :
    binaryGaussianPivotWord
        (effectiveGaussianPivotCandidates state column) =
      match findPivotOption state column with
      | none => [false]
      | some row => true :: List.replicate row.val true := by
  unfold binaryGaussianPivotWord
  rw [effectiveGaussianPivotCandidates_findIdxOption]
  cases findPivotOption state column <;> rfl


-- @@ L3260-3265 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianPackedCheckBits
    {m n : ℕ} (state : State m n) : List Bool :=
  (List.finRange m).flatMap fun row =>
    (List.finRange n).map fun column =>
      decide (state.system.check row column = (1 : ZMod 2))


-- @@ L3267-3271 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianPackedRhsBits
    {m n : ℕ} (state : State m n) : List Bool :=
  (List.finRange m).map fun row =>
    decide (state.system.rhs row = (1 : ZMod 2))


-- @@ L3273-3277 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianStatePivotRowOption
    {m n : ℕ} (state : State m n) (column : Fin n) : Option (Fin m) :=
  (state.pivots.find? fun pivot =>
    decide (pivot.2 = column)).map Prod.fst


-- @@ L3279-3284 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianStatePivotWord
    {m n : ℕ} (state : State m n) (column : Fin n) : List Bool :=
  match effectiveGaussianStatePivotRowOption state column with
  | none => [false]
  | some row => true :: List.replicate row.val true


-- @@ L3286-3291 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianStateReducedConsistencyRows
    {m n : ℕ} (state : State m n) : List (Bool × Bool) :=
  (List.finRange m).map fun row =>
    (decide (state.nextPivot ≤ row.val),
      decide (state.system.rhs row = (1 : ZMod 2)))


-- @@ L3293-3297 verbatim
/-- GapCVP reduction support. -/
@[expose] def effectiveGaussianStateReducedConsistencyQuery
    {m n : ℕ} (state : State m n) (source : List Bool) : List Bool :=
  binaryGaussianPackedPivotColumnWord
    (effectiveGaussianStateReducedConsistencyRows state) source


-- @@ L3299-3304 verbatim
theorem effectiveGaussianStatePivotRow_effective
    (system : BinaryAffineSystem) (column : Fin system.dimension) :
    effectiveGaussianStatePivotRowOption
        system.effectiveGaussianState column =
      system.effectivePivotRowOption column := by
  rfl


-- @@ L3306-3311 verbatim
theorem effectiveGaussianStateReducedConsistencyQuery_effective
    (system : BinaryAffineSystem) (source : List Bool) :
    effectiveGaussianStateReducedConsistencyQuery
        system.effectiveGaussianState source =
      GapCVP.GaussianReducedConsistencyTM.effectiveGaussianReducedConsistencyQuery
        system source := by rfl


-- @@ L3313-3313 verbatim
end GaussianAdaptiveEliminationCorrectness


-- @@ L3315-3315 verbatim
namespace BinaryPhysicalWordEntries


-- @@ L3317-3317 verbatim
open scoped BigOperators


-- @@ L3319-3319 verbatim
open GapCVP.Core


-- @@ L3321-3321 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L3323-3344 verbatim
theorem binaryFieldParityMatrix_apply_basisCoordinate
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {degree fieldRowCount dimension : ℕ}
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (checks : Matrix (Fin fieldRowCount) (Fin dimension) K)
    (row : Fin fieldRowCount)
    (coordinate : Fin degree)
    (column : Fin dimension) :
    binaryFieldParityMatrix basis checks
        (row, coordinate) column =
      basis.equivFun (checks row column) coordinate := by
  simp only [binaryFieldParityMatrix, binaryFieldParityLinearMap, binaryFieldVectorEquiv,
      binaryFieldBitEmbedding, LinearMap.toMatrix'_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, Function.comp_apply, Matrix.mulVecBilin_apply,
          LinearEquiv.trans_apply,
      LinearEquiv.coe_curry_symm, Function.uncurry_apply_pair, LinearEquiv.piCongrRight_apply,
          Matrix.mulVec, dotProduct,
      LinearMap.pi_apply, LinearMap.coe_proj, Function.eval, Pi.single_apply,
          Algebra.linearMap_apply,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte,
      Module.Basis.equivFun_apply]


-- @@ L3346-3346 verbatim
end BinaryPhysicalWordEntries


-- @@ L3348-3348 verbatim
namespace BinarySourceFieldMultiplicationTM


-- @@ L3350-3350 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L3351-3351 verbatim
open GapCVP.BinaryModularReductionTM


-- @@ L3353-3358 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinarySourceFieldQuery
    (lower left right source : List Bool) : List Bool :=
  lengthPrefixedWord lower ++
    lengthPrefixedWord left ++
      lengthPrefixedWord right ++ source


-- @@ L3360-3362 verbatim
/-- GapCVP reduction support. -/
def factor400BinarySourceLowerBits : List Bool → List Bool :=
  firstFieldContents


-- @@ L3364-3366 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinarySourceLeftBits : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix


-- @@ L3368-3370 verbatim
/-- GapCVP reduction support. -/
def factor400BinarySourceRightBits : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix


-- @@ L3372-3374 verbatim
/-- GapCVP reduction support. -/
def factor400BinarySourceFieldSuffix : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix


-- @@ L3376-3380 verbatim
/-- GapCVP reduction support. -/
noncomputable def binarySourceLowerBitsComputable :
    BitTM
      factor400BinarySourceLowerBits :=
  firstFieldContentsComputable


-- @@ L3382-3387 verbatim
/-- GapCVP reduction support. -/
noncomputable def binarySourceLeftBitsComputable :
    BitTM
      factor400BinarySourceLeftBits :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L3389-3396 verbatim
/-- GapCVP reduction support. -/
noncomputable def binarySourceRightBitsComputable :
    BitTM
      factor400BinarySourceRightBits := by
  exact GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable firstFieldSuffixComputable)
    firstFieldContentsComputable


-- @@ L3398-3405 verbatim
/-- GapCVP reduction support. -/
noncomputable def factor400BinarySourceFieldSuffixComputable :
    BitTM
      factor400BinarySourceFieldSuffix := by
  exact GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable firstFieldSuffixComputable)
    firstFieldSuffixComputable


-- @@ L3407-3412 verbatim
@[simp] theorem factor400BinarySourceLowerBits_query
    (lower left right source : List Bool) :
    factor400BinarySourceLowerBits
      (factor400BinarySourceFieldQuery lower left right source) = lower := by
  simp only [factor400BinarySourceLowerBits, factor400BinarySourceFieldQuery, List.append_assoc,
      firstFieldContents_valid]


-- @@ L3414-3419 verbatim
@[simp] theorem factor400BinarySourceLeftBits_query
    (lower left right source : List Bool) :
    factor400BinarySourceLeftBits
      (factor400BinarySourceFieldQuery lower left right source) = left := by
  simp only [factor400BinarySourceLeftBits, factor400BinarySourceFieldQuery, List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L3421-3426 verbatim
@[simp] theorem factor400BinarySourceRightBits_query
    (lower left right source : List Bool) :
    factor400BinarySourceRightBits
      (factor400BinarySourceFieldQuery lower left right source) = right := by
  simp only [factor400BinarySourceRightBits, factor400BinarySourceFieldQuery, List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L3428-3433 verbatim
@[simp] theorem factor400BinarySourceFieldSuffix_query
    (lower left right source : List Bool) :
    factor400BinarySourceFieldSuffix
      (factor400BinarySourceFieldQuery lower left right source) = source := by
  simp only [factor400BinarySourceFieldSuffix, factor400BinarySourceFieldQuery, List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid]


-- @@ L3435-3439 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinarySourcePaddedWord
    (degree : ℕ) (bits : List Bool) :
    GapCVP.Core.EffectiveBinaryField.Word degree :=
  fun position => bits.getD position.val false


-- @@ L3441-3445 verbatim
@[simp] theorem factor400BinaryFiniteWordBits_length
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree) :
    (finiteWordBits word).length = degree := by
  simp only [finiteWordBits, List.length_map, List.length_finRange]


-- @@ L3447-3457 verbatim
@[simp] theorem factor400BinarySourcePaddedWord_finiteWordBits
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree) :
    factor400BinarySourcePaddedWord degree (finiteWordBits word) = word := by
  funext position
  unfold factor400BinarySourcePaddedWord finiteWordBits
  have hposition : position.val <
      ((List.finRange degree).map word).length := by
    simp only [List.length_map, List.length_finRange, Fin.is_lt]
  rw [List.getD_eq_getElem _ false hposition]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]


-- @@ L3459-3475 verbatim
/-- GapCVP reduction support. -/
@[expose] def binarySourceMultiplyModWord
    (input : List Bool) : List Bool :=
  match readLengthPrefixedWord input with
  | none => []
  | some (lowerBits, lowerSuffix) =>
      match readLengthPrefixedWord lowerSuffix with
      | none => []
      | some (leftBits, leftSuffix) =>
          match readLengthPrefixedWord leftSuffix with
          | none => []
          | some (rightBits, _) =>
              finiteWordBits
                (GapCVP.Core.EffectiveBinaryField.multiplyMod
                  (factor400BinarySourcePaddedWord leftBits.length lowerBits)
                  (factor400BinarySourcePaddedWord leftBits.length leftBits)
                  (factor400BinarySourcePaddedWord leftBits.length rightBits))


-- @@ L3477-3491 verbatim
theorem binarySourceMultiplyModWord_valid
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceMultiplyModWord
    (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyMod lower left right) := by
  simp only [binarySourceMultiplyModWord, factor400BinarySourceFieldQuery, List.append_assoc,
      readLengthPrefixedWord_append]
  rw [factor400BinaryFiniteWordBits_length left]
  simp only [factor400BinarySourcePaddedWord_finiteWordBits]


-- @@ L3493-3493 verbatim
end BinarySourceFieldMultiplicationTM


-- @@ L3495-3495 verbatim
namespace BinaryPhysicalLagrangeProductFoldTM


-- @@ L3497-3497 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L3498-3498 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceWholeOutputAssemblyTM

-- @@ L3499-3499 verbatim
open GapCVP.SourceMixedRadixPolynomialPaddedDescriptorFoldTM GapCVP.CLStructuralPrefixWriter

-- @@ L3500-3500 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM

-- @@ L3501-3501 verbatim
open GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L3503-3505 verbatim
private def sourcePhysicalLagrangeProductAnchor
    (state : List Bool) : List Bool :=
  firstFieldContents state


-- @@ L3507-3511 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourcePhysicalLagrangeProductAccumulator
    (state : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix state)


-- @@ L3513-3515 verbatim
private def sourcePhysicalLagrangeProductFactor
    (state : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix (firstFieldSuffix state))


-- @@ L3517-3520 verbatim
private def sourcePhysicalLagrangeProductRemaining
    (state : List Bool) : List Bool :=
  firstFieldSuffix
    (firstFieldSuffix (firstFieldSuffix state))


-- @@ L3522-3524 verbatim
private def sourcePhysicalLagrangeProductModulus
    (state : List Bool) : List Bool :=
  firstFieldContents (sourcePhysicalLagrangeProductAnchor state)


-- @@ L3526-3528 verbatim
private def sourcePhysicalLagrangeProductOriginalSource
    (state : List Bool) : List Bool :=
  firstFieldSuffix (sourcePhysicalLagrangeProductAnchor state)


-- @@ L3530-3533 verbatim
private noncomputable def sourcePhysicalLagrangeProductAnchorComputable :
    BitTM
      sourcePhysicalLagrangeProductAnchor :=
  firstFieldContentsComputable


-- @@ L3535-3540 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalLagrangeProductAccumulatorComputable :
    BitTM
      sourcePhysicalLagrangeProductAccumulator :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L3542-3548 verbatim
private noncomputable def sourcePhysicalLagrangeProductFactorComputable :
    BitTM
      sourcePhysicalLagrangeProductFactor :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable firstFieldSuffixComputable)
    firstFieldContentsComputable


-- @@ L3550-3556 verbatim
private noncomputable def sourcePhysicalLagrangeProductRemainingComputable :
    BitTM
      sourcePhysicalLagrangeProductRemaining :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      firstFieldSuffixComputable firstFieldSuffixComputable)
    firstFieldSuffixComputable


-- @@ L3558-3563 verbatim
private noncomputable def sourcePhysicalLagrangeProductModulusComputable :
    BitTM
      sourcePhysicalLagrangeProductModulus :=
  GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalLagrangeProductAnchorComputable
    firstFieldContentsComputable


-- @@ L3565-3570 verbatim
private noncomputable def sourcePhysicalLagrangeProductOriginalSourceComputable :
    BitTM
      sourcePhysicalLagrangeProductOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalLagrangeProductAnchorComputable
    firstFieldSuffixComputable


-- @@ L3572-3578 verbatim
private def sourcePhysicalLagrangeProductFieldQuery
    (state : List Bool) : List Bool :=
  factor400BinarySourceFieldQuery
    (sourcePhysicalLagrangeProductModulus state)
    (sourcePhysicalLagrangeProductAccumulator state)
    (sourcePhysicalLagrangeProductFactor state)
    (sourcePhysicalLagrangeProductOriginalSource state)


-- @@ L3580-3607 verbatim
private noncomputable def sourcePhysicalLagrangeProductFieldQueryComputable :
    BitTM
      sourcePhysicalLagrangeProductFieldQuery := by
  have hprefixed
      (worker : List Bool → List Bool)
      (hworker : BitTM worker) :
      BitTM
        (fun input => lengthPrefixedWord (worker input)) := by
    have h := GapCVP.TMComposition.computableInPolyTime
      hworker structuralPrefixWriterComputable
    simpa only [Function.comp_def] using h
  have htail := pointwiseAppendComputable
    (hprefixed sourcePhysicalLagrangeProductFactor
      sourcePhysicalLagrangeProductFactorComputable)
    sourcePhysicalLagrangeProductOriginalSourceComputable
  have hmiddle := pointwiseAppendComputable
    (hprefixed sourcePhysicalLagrangeProductAccumulator
      sourcePhysicalLagrangeProductAccumulatorComputable) htail
  have hfull := pointwiseAppendComputable
    (hprefixed sourcePhysicalLagrangeProductModulus
      sourcePhysicalLagrangeProductModulusComputable) hmiddle
  change BitTM
    (fun state => factor400BinarySourceFieldQuery
      (sourcePhysicalLagrangeProductModulus state)
      (sourcePhysicalLagrangeProductAccumulator state)
      (sourcePhysicalLagrangeProductFactor state)
      (sourcePhysicalLagrangeProductOriginalSource state))
  simpa only [factor400BinarySourceFieldQuery, List.append_assoc] using hfull


-- @@ L3609-3612 verbatim
private def sourcePhysicalLagrangeProductNext
    (state : List Bool) : List Bool :=
  binarySourceMultiplyModWord
    (sourcePhysicalLagrangeProductFieldQuery state)


-- @@ L3614-3624 verbatim
private noncomputable def sourcePhysicalLagrangeProductNextComputable
    (multiplyComputer : BitTM binarySourceMultiplyModWord) :
    BitTM
      sourcePhysicalLagrangeProductNext := by
  have h := GapCVP.TMComposition.computableInPolyTime
    sourcePhysicalLagrangeProductFieldQueryComputable
    multiplyComputer
  change BitTM
    (fun state => binarySourceMultiplyModWord
      (sourcePhysicalLagrangeProductFieldQuery state))
  simpa only [Function.comp_def] using h


-- @@ L3626-3632 verbatim
private def sourcePhysicalLagrangeProductStep
    (state : List Bool) : List Bool :=
  lengthPrefixedWord
      (sourcePhysicalLagrangeProductAnchor state) ++
    lengthPrefixedWord
      (sourcePhysicalLagrangeProductNext state) ++
        sourcePhysicalLagrangeProductRemaining state


-- @@ L3634-3659 verbatim
private noncomputable def sourcePhysicalLagrangeProductStepComputable
    (multiplyComputer : BitTM binarySourceMultiplyModWord) :
    BitTM
      sourcePhysicalLagrangeProductStep := by
  have hprefixed
      (worker : List Bool → List Bool)
      (hworker : BitTM worker) :
      BitTM
        (fun input => lengthPrefixedWord (worker input)) := by
    have h := GapCVP.TMComposition.computableInPolyTime
      hworker structuralPrefixWriterComputable
    simpa only [Function.comp_def] using h
  have htail := pointwiseAppendComputable
    (hprefixed sourcePhysicalLagrangeProductNext
      (sourcePhysicalLagrangeProductNextComputable multiplyComputer))
    sourcePhysicalLagrangeProductRemainingComputable
  have hfull := pointwiseAppendComputable
    (hprefixed sourcePhysicalLagrangeProductAnchor
      sourcePhysicalLagrangeProductAnchorComputable) htail
  change BitTM
    (fun state => lengthPrefixedWord
      (sourcePhysicalLagrangeProductAnchor state) ++
        lengthPrefixedWord
          (sourcePhysicalLagrangeProductNext state) ++
            sourcePhysicalLagrangeProductRemaining state)
  simpa only [List.append_assoc] using hfull


-- @@ L3661-3667 verbatim
private theorem sourcePhysicalLagrangeProductNext_length
    (state : List Bool) :
    (sourcePhysicalLagrangeProductNext state).length =
      (sourcePhysicalLagrangeProductAccumulator state).length := by
  simp only [sourcePhysicalLagrangeProductNext, binarySourceMultiplyModWord,
      sourcePhysicalLagrangeProductFieldQuery, factor400BinarySourceFieldQuery, List.append_assoc,
      readLengthPrefixedWord_append, finiteWordBits, List.length_map, List.length_finRange]


-- @@ L3669-3676 verbatim
@[simp] private theorem sourcePhysicalLagrangeProductStep_anchor
    (state : List Bool) :
    sourcePhysicalLagrangeProductAnchor
        (sourcePhysicalLagrangeProductStep state) =
      sourcePhysicalLagrangeProductAnchor state := by
  simp only [sourcePhysicalLagrangeProductAnchor, sourcePhysicalLagrangeProductStep,
      List.append_assoc,
      firstFieldContents_valid]


-- @@ L3678-3685 verbatim
@[simp] private theorem sourcePhysicalLagrangeProductStep_accumulator
    (state : List Bool) :
    sourcePhysicalLagrangeProductAccumulator
        (sourcePhysicalLagrangeProductStep state) =
      sourcePhysicalLagrangeProductNext state := by
  simp only [sourcePhysicalLagrangeProductAccumulator, sourcePhysicalLagrangeProductStep,
      List.append_assoc,
      firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L3687-3692 verbatim
@[simp] private theorem sourcePhysicalLagrangeProductStep_remaining
    (state : List Bool) :
    firstFieldSuffix
      (firstFieldSuffix (sourcePhysicalLagrangeProductStep state)) =
        sourcePhysicalLagrangeProductRemaining state := by
  simp only [sourcePhysicalLagrangeProductStep, List.append_assoc, firstFieldSuffix_valid]


-- @@ L3694-3703 verbatim
private theorem sourcePhysicalLagrangeProduct_iterate_anchor
    (state : List Bool) (stage : ℕ) :
    sourcePhysicalLagrangeProductAnchor
      (((sourcePhysicalLagrangeProductStep)^[stage]) state) =
        sourcePhysicalLagrangeProductAnchor state := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      simpa only [sourcePhysicalLagrangeProductStep_anchor] using ih


-- @@ L3705-3716 verbatim
private theorem sourcePhysicalLagrangeProduct_iterate_accumulator_length
    (state : List Bool) (stage : ℕ) :
    (sourcePhysicalLagrangeProductAccumulator
      (((sourcePhysicalLagrangeProductStep)^[stage]) state)).length =
        (sourcePhysicalLagrangeProductAccumulator state).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        sourcePhysicalLagrangeProductStep_accumulator,
        sourcePhysicalLagrangeProductNext_length]
      exact ih


-- @@ L3718-3721 verbatim
private theorem sourcePhysicalLagrangeProductSuffix_length_le
    (state : List Bool) :
    (firstFieldSuffix state).length ≤ state.length :=
  sourceMixedRadixPhysicalFirstFieldSuffix_length_le state


-- @@ L3723-3736 verbatim
private theorem sourcePhysicalLagrangeProduct_iterate_pending_length_le
    (state : List Bool) (stage : ℕ) :
    (firstFieldSuffix (firstFieldSuffix
      (((sourcePhysicalLagrangeProductStep)^[stage]) state))).length ≤
      (firstFieldSuffix (firstFieldSuffix state)).length := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        sourcePhysicalLagrangeProductStep_remaining]
      exact (sourcePhysicalLagrangeProductSuffix_length_le
        (firstFieldSuffix
          (firstFieldSuffix
            (((sourcePhysicalLagrangeProductStep)^[stage]) state)))).trans ih


-- @@ L3738-3794 verbatim
private theorem sourcePhysicalLagrangeProduct_iterate_length_le
    (state : List Bool) (stage : ℕ) :
    (((sourcePhysicalLagrangeProductStep)^[stage]) state).length ≤
      5 * state.length + 2 := by
  cases stage with
  | zero => simp only [Function.iterate_zero, id_eq]; omega
  | succ stage =>
      rw [Function.iterate_succ_apply']
      let current := ((sourcePhysicalLagrangeProductStep)^[stage]) state
      have hanchor := sourceMixedRadixPhysicalFirstFieldContents_length_le
        state
      have haccContents :=
        sourceMixedRadixPhysicalFirstFieldContents_length_le
          (firstFieldSuffix state)
      have haccSuffix :=
        sourcePhysicalLagrangeProductSuffix_length_le state
      have hacc :
          (sourcePhysicalLagrangeProductAccumulator state).length ≤
            state.length := by
        exact haccContents.trans haccSuffix
      have hpending₁ :=
        sourcePhysicalLagrangeProductSuffix_length_le state
      have hpending₂ :=
        sourcePhysicalLagrangeProductSuffix_length_le
          (firstFieldSuffix state)
      have hpending :
          (firstFieldSuffix (firstFieldSuffix current)).length ≤
            state.length :=
        (sourcePhysicalLagrangeProduct_iterate_pending_length_le
          state stage).trans (hpending₂.trans hpending₁)
      have hremaining :=
        (sourcePhysicalLagrangeProductSuffix_length_le
          (firstFieldSuffix (firstFieldSuffix current))).trans hpending
      have hcurrentAnchor :=
        sourcePhysicalLagrangeProduct_iterate_anchor state stage
      have hcurrentAccumulator :=
        sourcePhysicalLagrangeProduct_iterate_accumulator_length
          state stage
      change (sourcePhysicalLagrangeProductStep current).length ≤ _
      simp only [sourcePhysicalLagrangeProductStep,
        List.length_append, lengthPrefixedWord_length,
        sourcePhysicalLagrangeProductNext_length]
      change
        (2 * (sourcePhysicalLagrangeProductAnchor current).length + 1) +
          (2 * (sourcePhysicalLagrangeProductAccumulator current).length + 1) +
          (firstFieldSuffix
            (firstFieldSuffix (firstFieldSuffix current))).length ≤
            5 * state.length + 2
      have hanchor' :
          (sourcePhysicalLagrangeProductAnchor current).length ≤
            state.length := by
        simpa only using hcurrentAnchor.symm ▸ hanchor
      have hacc' :
          (sourcePhysicalLagrangeProductAccumulator current).length ≤
            state.length := by
        simpa only using hcurrentAccumulator.symm ▸ hacc
      omega


-- @@ L3796-3797 verbatim
private def sourcePhysicalLagrangeProductStatePolynomial : Polynomial ℕ :=
  5 * Polynomial.X + 2


-- @@ L3799-3815 verbatim
private theorem sourcePhysicalLagrangeProduct_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates sourcePhysicalLagrangeProductStep
      sourcePhysicalLagrangeProductStatePolynomial := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hseed := GapCVP.CNFTypedRecordWorkerTM.parsedUnaryFold_seed_length_le
    input count seed hparse
  have hstage := sourcePhysicalLagrangeProduct_iterate_length_le
    seed stage
  change
    (((sourcePhysicalLagrangeProductStep)^[stage]) seed).length ≤
      sourcePhysicalLagrangeProductStatePolynomial.eval input.length
  simp only [sourcePhysicalLagrangeProductStatePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega


-- @@ L3817-3819 verbatim
/-- GapCVP reduction support. -/
def sourcePhysicalLagrangeProductFoldOutput : List Bool → List Bool :=
  boundedRecordFoldOutput sourcePhysicalLagrangeProductStep


-- @@ L3821-3829 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalLagrangeProductFoldComputable
    (multiplyComputer : BitTM binarySourceMultiplyModWord) :
    BitTM
      sourcePhysicalLagrangeProductFoldOutput :=
  boundedDependentRecordFoldComputable
    (sourcePhysicalLagrangeProductStepComputable multiplyComputer)
    sourcePhysicalLagrangeProductStatePolynomial
    sourcePhysicalLagrangeProduct_polynomiallyBoundedFoldStates


-- @@ L3831-3837 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourcePhysicalLagrangePackedFactorWords
    {degree : ℕ}
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree)) :
    List Bool :=
  factors.flatMap
    (fun factor => lengthPrefixedWord (finiteWordBits factor))


-- @@ L3839-3845 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourcePhysicalLagrangeProductSourceAnchor
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) : List Bool :=
  lengthPrefixedWord (finiteWordBits lower) ++ source


-- @@ L3847-3855 verbatim
private def sourcePhysicalLagrangeProductSeed
    {degree : ℕ}
    (lower initial : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (source : List Bool) : List Bool :=
  lengthPrefixedWord
      (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
    lengthPrefixedWord (finiteWordBits initial) ++
      sourcePhysicalLagrangePackedFactorWords factors


-- @@ L3857-3879 verbatim
private theorem sourcePhysicalLagrangeProductStep_valid
    {degree : ℕ}
    (lower current factor : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source pending : List Bool) :
    sourcePhysicalLagrangeProductStep
      (lengthPrefixedWord
        (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
        lengthPrefixedWord (finiteWordBits current) ++
        lengthPrefixedWord (finiteWordBits factor) ++ pending) =
      lengthPrefixedWord
        (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
        lengthPrefixedWord
          (finiteWordBits
            (GapCVP.Core.EffectiveBinaryField.multiplyMod
              lower current factor)) ++ pending := by
  simp only [sourcePhysicalLagrangeProductStep, sourcePhysicalLagrangeProductAnchor,
      sourcePhysicalLagrangeProductSourceAnchor, List.append_assoc, firstFieldContents_valid,
      sourcePhysicalLagrangeProductNext, sourcePhysicalLagrangeProductFieldQuery,
          sourcePhysicalLagrangeProductModulus,
      sourcePhysicalLagrangeProductAccumulator, firstFieldSuffix_valid,
          sourcePhysicalLagrangeProductFactor,
      sourcePhysicalLagrangeProductOriginalSource, binarySourceMultiplyModWord_valid,
      sourcePhysicalLagrangeProductRemaining]


-- @@ L3881-3932 verbatim
private theorem sourcePhysicalLagrangeProduct_iterate_valid
    {degree : ℕ}
    (lower initial : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (source : List Bool) :
    ((sourcePhysicalLagrangeProductStep)^[factors.length])
      (sourcePhysicalLagrangeProductSeed
        lower initial factors source) =
      lengthPrefixedWord
        (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
      lengthPrefixedWord
        (finiteWordBits
          (factors.foldl
            (GapCVP.Core.EffectiveBinaryField.multiplyMod lower)
            initial)) := by
  induction factors generalizing initial with
  | nil =>
      simp only [List.length_nil, sourcePhysicalLagrangeProductSeed,
          sourcePhysicalLagrangePackedFactorWords,
          List.flatMap_nil, List.append_nil, Function.iterate_zero, id_eq, List.foldl_nil]
  | cons factor factors ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      unfold sourcePhysicalLagrangeProductSeed
        sourcePhysicalLagrangePackedFactorWords
      simp only [List.flatMap_cons]
      have hstate :
          lengthPrefixedWord
              (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
            lengthPrefixedWord (finiteWordBits initial) ++
              (lengthPrefixedWord (finiteWordBits factor) ++
                factors.flatMap
                  (fun item => lengthPrefixedWord
                    (finiteWordBits item))) =
          lengthPrefixedWord
              (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
            lengthPrefixedWord (finiteWordBits initial) ++
              lengthPrefixedWord (finiteWordBits factor) ++
                factors.flatMap
                  (fun item => lengthPrefixedWord
                    (finiteWordBits item)) := by
        simp only [List.append_assoc]
      rw [hstate]
      rw [sourcePhysicalLagrangeProductStep_valid]
      change
        ((sourcePhysicalLagrangeProductStep)^[factors.length])
          (sourcePhysicalLagrangeProductSeed
            lower
            (GapCVP.Core.EffectiveBinaryField.multiplyMod
              lower initial factor)
            factors source) = _
      simpa only [List.foldl_cons] using ih (GapCVP.Core.EffectiveBinaryField.multiplyMod lower
          initial factor)


-- @@ L3934-3945 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourcePhysicalLagrangeProductFoldWord
    {degree : ℕ}
    (lower initial : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (source : List Bool) : List Bool :=
  unaryBoundedFoldWord factors.length
    (lengthPrefixedWord
        (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
      lengthPrefixedWord (finiteWordBits initial) ++
        sourcePhysicalLagrangePackedFactorWords factors)


-- @@ L3947-3967 verbatim
theorem sourcePhysicalLagrangeProductFoldOutput_valid
    {degree : ℕ}
    (lower initial : GapCVP.Core.EffectiveBinaryField.Word degree)
    (factors : List (GapCVP.Core.EffectiveBinaryField.Word degree))
    (source : List Bool) :
    sourcePhysicalLagrangeProductFoldOutput
      (sourcePhysicalLagrangeProductFoldWord
        lower initial factors source) =
      lengthPrefixedWord
        (sourcePhysicalLagrangeProductSourceAnchor lower source) ++
      lengthPrefixedWord
        (finiteWordBits
          (factors.foldl
            (GapCVP.Core.EffectiveBinaryField.multiplyMod lower)
            initial)) := by
  unfold sourcePhysicalLagrangeProductFoldOutput
    sourcePhysicalLagrangeProductFoldWord
    boundedRecordFoldOutput
  rw [parseUnaryBoundedFold_word]
  exact sourcePhysicalLagrangeProduct_iterate_valid
    lower initial factors source


-- @@ L3969-3969 verbatim
end BinaryPhysicalLagrangeProductFoldTM


-- @@ L3971-3971 verbatim
namespace BinaryFieldInverseAlgebra


-- @@ L3973-3973 verbatim
open GapCVP.Core GapCVP.Core.EffectiveBinaryField Polynomial

-- @@ L3974-3974 verbatim
open scoped BigOperators


-- @@ L3976-3978 verbatim
/-- GapCVP reduction support. -/
@[expose] def zeroWord (degree : ℕ) : EffectiveBinaryField.Word degree :=
  fun _ => false


-- @@ L3980-3982 verbatim
/-- GapCVP reduction support. -/
@[expose] def oneWord (degree : ℕ) : EffectiveBinaryField.Word degree :=
  fun bit => decide (bit.val = 0)


-- @@ L3984-3999 verbatim
theorem wordPolynomial_zeroWord (degree : ℕ) :
    EffectiveBinaryField.wordPolynomial (zeroWord degree) = 0 := by
  classical
  apply Polynomial.ext
  intro index
  by_cases hindex : index < degree
  · let bit : Fin degree := ⟨index, hindex⟩
    change
      (EffectiveBinaryField.wordPolynomial
        (zeroWord degree)).coeff bit.val =
        (0 : (ZMod 2)[X]).coeff bit.val
    rw [EffectiveBinaryField.wordPolynomial_coeff_fin]
    simp only [bitValue, zeroWord, Bool.false_eq_true, ↓reduceIte, coeff_zero]
  · rw [EffectiveBinaryField.wordPolynomial_coeff_eq_zero
      (zeroWord degree) index (Nat.le_of_not_gt hindex)]
    simp only [coeff_zero]


-- @@ L4001-4019 verbatim
private theorem wordPolynomial_oneWord
    (degree : ℕ) (hdegree : 0 < degree) :
    EffectiveBinaryField.wordPolynomial (oneWord degree) = 1 := by
  classical
  apply Polynomial.ext
  intro index
  by_cases hindex : index < degree
  · let bit : Fin degree := ⟨index, hindex⟩
    change
      (EffectiveBinaryField.wordPolynomial
        (oneWord degree)).coeff bit.val =
        (1 : (ZMod 2)[X]).coeff bit.val
    rw [EffectiveBinaryField.wordPolynomial_coeff_fin]
    simp only [bitValue, oneWord, decide_eq_true_eq, coeff_one]
  · rw [EffectiveBinaryField.wordPolynomial_coeff_eq_zero
      (oneWord degree) index (Nat.le_of_not_gt hindex)]
    have hnonzero : index ≠ 0 := by
      omega
    simp only [coeff_one, hnonzero, ↓reduceIte]


-- @@ L4021-4037 verbatim
private theorem wordPolynomial_foldl_xorAt {d : ℕ} {α : Type}
    (items : List α) (index : α → Fin d) (bit : α → Bool)
    (word : Word d) :
    wordPolynomial
        (items.foldl (fun accumulator item =>
          xorAt accumulator (index item) (bit item)) word) =
      wordPolynomial word +
        (items.map fun item =>
          Polynomial.monomial (index item).val
            (bitValue (bit item))).sum := by
  induction items generalizing word with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons item rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (xorAt word (index item) (bit item)),
        wordPolynomial_xorAt]
      ac_rfl


-- @@ L4039-4042 verbatim
private theorem finRange_polynomial_sum {e : ℕ}
    (f : Fin e → (ZMod 2)[X]) :
    ((List.finRange e).map f).sum = ∑ i : Fin e, f i := by
  rfl


-- @@ L4044-4070 verbatim
theorem wordPolynomial_shiftXor {e : ℕ}
    (lower : Word e) (degree : ℕ) (word : Word (2 * e))
    (hdegree : e ≤ degree ∧ degree < 2 * e) :
    wordPolynomial (shiftXor lower degree word) =
      wordPolynomial word +
        Polynomial.X ^ (degree - e) * wordPolynomial lower := by
  classical
  have hbound (i : Fin e) : degree - e + i.val < 2 * e := by
    have hi := i.isLt
    omega
  let shiftedIndex : Fin e → Fin (2 * e) :=
    fun i => ⟨degree - e + i.val, hbound i⟩
  have hstep :
      (fun (accumulator : Word (2 * e)) (i : Fin e) =>
        if h : degree - e + i.val < 2 * e then
          xorAt accumulator ⟨degree - e + i.val, h⟩ (lower i)
        else accumulator) =
      (fun accumulator i =>
        xorAt accumulator (shiftedIndex i) (lower i)) := by
    funext accumulator i
    simp only [hbound i, ↓reduceDIte, shiftedIndex]
  unfold shiftXor
  rw [hstep, wordPolynomial_foldl_xorAt,
    finRange_polynomial_sum]
  congr 1
  simp only [X_pow_eq_monomial, wordPolynomial, Finset.mul_sum, monomial_mul_monomial, one_mul,
      shiftedIndex]


-- @@ L4072-4099 verbatim
private theorem shiftXor_preserves_ge {e : ℕ}
    (lower : Word e) (degree : ℕ) (word : Word (2 * e))
    (hdegree : e ≤ degree)
    (index : Fin (2 * e)) (hindex : degree ≤ index.val) :
    shiftXor lower degree word index = word index := by
  unfold shiftXor
  let step : Word (2 * e) → Fin e → Word (2 * e) :=
    fun accumulator i =>
      if h : degree - e + i.val < 2 * e then
        xorAt accumulator ⟨degree - e + i.val, h⟩ (lower i)
      else accumulator
  change ((List.finRange e).foldl step word) index = word index
  refine List.foldlRecOn (List.finRange e) step
    (motive := fun accumulator => accumulator index = word index)
    rfl ?_
  intro accumulator hacc i _
  dsimp [step]
  split
  · rename_i hbound
    have hne :
        index ≠ (⟨degree - e + i.val, hbound⟩ : Fin (2 * e)) := by
      intro h
      have hv := congrArg (fun j : Fin (2 * e) => j.val) h
      change index.val = degree - e + i.val at hv
      have hi := i.isLt
      omega
    simpa only [xorAt, hne, ↓reduceIte] using hacc
  · exact hacc


-- @@ L4101-4130 verbatim
private theorem reduceAt_quotient {e : ℕ}
    (lower : Word e) (degree : ℕ) (word : Word (2 * e)) :
    (AdjoinRoot.mk (monicPolynomial lower))
      (wordPolynomial (reduceAt lower degree word)) =
      (AdjoinRoot.mk (monicPolynomial lower))
        (wordPolynomial word) := by
  unfold reduceAt
  split
  · rename_i hdegree
    dsimp only
    split
    · rename_i hbit
      let leading : Fin (2 * e) := ⟨degree, hdegree.2⟩
      have hpoly :
          wordPolynomial
            (shiftXor lower degree (xorAt word leading true)) =
          wordPolynomial word +
            Polynomial.X ^ (degree - e) * monicPolynomial lower := by
        rw [wordPolynomial_shiftXor lower degree
          (xorAt word leading true) hdegree,
          wordPolynomial_xorAt]
        simp only [leading, bitValue, ↓reduceIte,
          ← Polynomial.X_pow_eq_monomial]
        unfold monicPolynomial
        rw [mul_add, ← pow_add, Nat.sub_add_cancel hdegree.1]
        ring
      rw [hpoly, map_add, map_mul, AdjoinRoot.mk_self,
        mul_zero, add_zero]
    · rfl
  · rfl


-- @@ L4132-4145 verbatim
private theorem reduceAt_leading_zero {e : ℕ}
    (lower : Word e) (degree : ℕ) (word : Word (2 * e))
    (hdegree : e ≤ degree ∧ degree < 2 * e) :
    reduceAt lower degree word
      (⟨degree, hdegree.2⟩ : Fin (2 * e)) = false := by
  unfold reduceAt
  rw [dite_eq_left hdegree]
  by_cases hbit : word ⟨degree, hdegree.2⟩ = true
  · simp only [hbit, ↓reduceIte]
    rw [shiftXor_preserves_ge lower degree
      (xorAt word ⟨degree, hdegree.2⟩ true)
      hdegree.1 ⟨degree, hdegree.2⟩ (le_refl degree)]
    simp only [xorAt, ↓reduceIte, hbit, bne_self_eq_false]
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte]


-- @@ L4147-4167 verbatim
private theorem reduceAt_preserves_above {e : ℕ}
    (lower : Word e) (degree : ℕ) (word : Word (2 * e))
    (index : Fin (2 * e)) (habove : degree < index.val) :
    reduceAt lower degree word index = word index := by
  unfold reduceAt
  split
  · rename_i hdegree
    dsimp only
    split
    · rename_i hbit
      rw [shiftXor_preserves_ge lower degree
        (xorAt word ⟨degree, hdegree.2⟩ true)
        hdegree.1 index (Nat.le_of_lt habove)]
      have hne : index ≠ (⟨degree, hdegree.2⟩ : Fin (2 * e)) := by
        intro h
        have hv := congrArg (fun j : Fin (2 * e) => j.val) h
        change index.val = degree at hv
        omega
      simp only [xorAt, hne, ↓reduceIte]
    · rfl
  · rfl


-- @@ L4169-4175 verbatim
/-- GapCVP reduction support. -/
@[expose] def reducePrefix {e : ℕ} (lower : Word e) (count : ℕ)
    (word : Word (2 * e)) : Word (2 * e) :=
  (List.range count).foldl
    (fun accumulator offset =>
      reduceAt lower (2 * e - 1 - offset) accumulator)
    word


-- @@ L4177-4182 verbatim
theorem reducePrefix_succ {e : ℕ}
    (lower : Word e) (count : ℕ) (word : Word (2 * e)) :
    reducePrefix lower (count + 1) word =
      reduceAt lower (2 * e - 1 - count)
        (reducePrefix lower count word) := by
  simp only [reducePrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]


-- @@ L4184-4196 verbatim
private theorem reducePrefix_quotient {e : ℕ}
    (lower : Word e) (count : ℕ) (word : Word (2 * e)) :
    (AdjoinRoot.mk (monicPolynomial lower))
      (wordPolynomial (reducePrefix lower count word)) =
      (AdjoinRoot.mk (monicPolynomial lower))
        (wordPolynomial word) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 = Nat.succ count by omega]
      rw [reducePrefix_succ]
      exact (reduceAt_quotient lower (2 * e - 1 - count)
        (reducePrefix lower count word)).trans ih


-- @@ L4198-4230 verbatim
private theorem reducePrefix_high_zero {e : ℕ}
    (lower : Word e) (count : ℕ) (word : Word (2 * e))
    (hcount : count ≤ e) (index : Fin (2 * e))
    (hindex : 2 * e - count ≤ index.val) :
    reducePrefix lower count word index = false := by
  induction count generalizing word with
  | zero =>
      have hi := index.isLt
      simp only [tsub_zero] at hindex
      omega
  | succ count ih =>
      have hcount' : count < e := by omega
      let degree := 2 * e - 1 - count
      have hdegree : e ≤ degree ∧ degree < 2 * e := by
        dsimp [degree]
        omega
      have hindex' : degree ≤ index.val := by
        dsimp [degree]
        omega
      rw [reducePrefix_succ]
      by_cases heq : index.val = degree
      · have hfin : index = (⟨degree, hdegree.2⟩ : Fin (2 * e)) :=
          Fin.ext heq
        rw [hfin]
        exact reduceAt_leading_zero lower degree
          (reducePrefix lower count word) hdegree
      · have habove : degree < index.val := by omega
        rw [reduceAt_preserves_above lower degree
          (reducePrefix lower count word) index habove]
        apply ih word
        · omega
        · dsimp [degree] at habove
          omega


-- @@ L4232-4238 verbatim
private theorem reduceProduct_quotient {e : ℕ}
    (lower : Word e) (word : Word (2 * e)) :
    (AdjoinRoot.mk (monicPolynomial lower))
      (wordPolynomial (reduceProduct lower word)) =
      (AdjoinRoot.mk (monicPolynomial lower))
        (wordPolynomial word) :=
  reducePrefix_quotient lower e word


-- @@ L4240-4245 verbatim
private theorem reduceProduct_high_zero {e : ℕ}
    (lower : Word e) (word : Word (2 * e))
    (index : Fin (2 * e)) (hindex : e ≤ index.val) :
    reduceProduct lower word index = false := by
  apply reducePrefix_high_zero lower e word (le_refl e) index
  omega


-- @@ L4247-4251 verbatim
/-- GapCVP reduction support. -/
@[expose] def truncateWord {e : ℕ} (word : Word (2 * e)) : Word e :=
  fun i => word ⟨i.val, by
    have hi := i.isLt
    omega⟩


-- @@ L4253-4279 verbatim
private theorem wordPolynomial_truncateWord {e : ℕ}
    (word : Word (2 * e))
    (hzero : ∀ index : Fin (2 * e),
      e ≤ index.val → word index = false) :
    wordPolynomial (truncateWord word) = wordPolynomial word := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < e
  · let low : Fin e := ⟨k, hk⟩
    let high : Fin (2 * e) := ⟨k, by omega⟩
    change
      (wordPolynomial (truncateWord word)).coeff low.val =
        (wordPolynomial word).coeff high.val
    rw [wordPolynomial_coeff_fin, wordPolynomial_coeff_fin]
    rfl
  · have hlarge : e ≤ k := Nat.le_of_not_gt hk
    rw [wordPolynomial_coeff_eq_zero _ k hlarge]
    by_cases hk' : k < 2 * e
    · let index : Fin (2 * e) := ⟨k, hk'⟩
      have hz := hzero index hlarge
      have hc := wordPolynomial_coeff_fin word index
      change 0 = (wordPolynomial word).coeff index.val
      rw [hc, hz]
      decide
    · have hlarge' : 2 * e ≤ k := Nat.le_of_not_gt hk'
      rw [wordPolynomial_coeff_eq_zero word k hlarge']


-- @@ L4281-4294 verbatim
private theorem multiplyMod_quotient {degree : ℕ}
    (lower left right : Word degree) :
    (AdjoinRoot.mk (monicPolynomial lower))
      (wordPolynomial (multiplyMod lower left right)) =
      (AdjoinRoot.mk (monicPolynomial lower)) (wordPolynomial left) *
        (AdjoinRoot.mk (monicPolynomial lower)) (wordPolynomial right) := by
  change
    (AdjoinRoot.mk (monicPolynomial lower))
      (wordPolynomial
        (truncateWord (reduceProduct lower (multiplyWords left right)))) = _
  rw [wordPolynomial_truncateWord
    (reduceProduct lower (multiplyWords left right))
    (reduceProduct_high_zero lower (multiplyWords left right)),
    reduceProduct_quotient, wordPolynomial_multiplyWords, map_mul]


-- @@ L4296-4310 verbatim
private theorem wordElement_multiplyMod {degree : ℕ}
    (left right : Word degree) :
    GapCVP.BinaryFieldBasis.wordElement
        (multiplyMod (irreducibleWord degree) left right) =
      GapCVP.BinaryFieldBasis.wordElement left *
        GapCVP.BinaryFieldBasis.wordElement right := by
  change
    (AdjoinRoot.mk (monicPolynomial (irreducibleWord degree)))
      (wordPolynomial
        (multiplyMod (irreducibleWord degree) left right)) =
      (AdjoinRoot.mk (monicPolynomial (irreducibleWord degree)))
        (wordPolynomial left) *
      (AdjoinRoot.mk (monicPolynomial (irreducibleWord degree)))
        (wordPolynomial right)
  exact multiplyMod_quotient (irreducibleWord degree) left right


-- @@ L4312-4326 verbatim
/-- GapCVP reduction support. -/
@[expose] noncomputable def sourceWordValue
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (word : Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula))) :
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      encodingLength formula :=
  extensionAlgEquivGaloisField
    (GapCVP.Core.sourceFieldExponent
      (GapCVP.Core.sourceSizeParameter encodingLength formula))
    (GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        encodingLength formula))
    (GapCVP.BinaryFieldBasis.wordElement word)


-- @@ L4328-4333 verbatim
private theorem wordElement_oneWord
    (degree : ℕ) (hdegree : 0 < degree) :
    GapCVP.BinaryFieldBasis.wordElement
      (oneWord degree) = 1 := by
  unfold GapCVP.BinaryFieldBasis.wordElement
  rw [wordPolynomial_oneWord degree hdegree, map_one]


-- @@ L4335-4345 verbatim
theorem sourceWordValue_oneWord
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    sourceWordValue encodingLength formula
      (oneWord
        (GapCVP.Core.sourceFieldExponent
          (GapCVP.Core.sourceSizeParameter encodingLength formula))) = 1 := by
  unfold sourceWordValue
  rw [wordElement_oneWord _
    (GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        encodingLength formula)), map_one]


-- @@ L4347-4361 verbatim
theorem sourceWordValue_multiplyMod
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (left right : Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula))) :
    sourceWordValue encodingLength formula
        (multiplyMod
          (irreducibleWord
            (GapCVP.Core.sourceFieldExponent
              (GapCVP.Core.sourceSizeParameter encodingLength formula)))
          left right) =
      sourceWordValue encodingLength formula left *
        sourceWordValue encodingLength formula right := by
  unfold sourceWordValue
  rw [wordElement_multiplyMod, map_mul]


-- @@ L4363-4369 verbatim
/-- GapCVP reduction support. -/
@[expose]
def sourceWordPow {degree : ℕ}
    (word : Word degree) : ℕ → Word degree
  | 0 => oneWord degree
  | n + 1 => multiplyMod (irreducibleWord degree)
      (sourceWordPow word n) word


-- @@ L4371-4383 verbatim
theorem sourceWordValue_sourceWordPow
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (word : Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula)))
    (power : ℕ) :
    sourceWordValue encodingLength formula (sourceWordPow word power) =
      sourceWordValue encodingLength formula word ^ power := by
  induction power with
  | zero =>
      simpa only [sourceWordPow, pow_zero] using sourceWordValue_oneWord encodingLength formula
  | succ power ih =>
      rw [sourceWordPow, sourceWordValue_multiplyMod, ih, pow_succ]


-- @@ L4385-4388 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourceInverseWord {degree : ℕ}
    (word : Word degree) : Word degree :=
  sourceWordPow word ((2 ^ degree - 2))


-- @@ L4390-4428 verbatim
theorem sourceWordValue_sourceInverseWord
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (word : Word
      (GapCVP.Core.sourceFieldExponent
        (GapCVP.Core.sourceSizeParameter encodingLength formula)))
    (hnonzero : sourceWordValue encodingLength formula word ≠ 0) :
    sourceWordValue encodingLength formula (sourceInverseWord word) =
      (sourceWordValue encodingLength formula word)⁻¹ := by
  rw [sourceInverseWord, sourceWordValue_sourceWordPow]
  let degree := GapCVP.Core.sourceFieldExponent
    (GapCVP.Core.sourceSizeParameter encodingLength formula)
  have hdegree : 0 < degree :=
    GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        encodingLength formula)
  have hq : 2 ≤ 2 ^ degree := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ degree :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  apply mul_left_cancel₀ hnonzero
  rw [mul_inv_cancel₀ hnonzero]
  calc
    sourceWordValue encodingLength formula word *
        sourceWordValue encodingLength formula word ^
          (2 ^ degree - 2) =
        sourceWordValue encodingLength formula word ^
          (2 ^ degree - 1) := by
      rw [mul_comm, ← pow_succ]
      congr 1
      omega
    _ = 1 := by
      have hfermat := FiniteField.pow_card_sub_one_eq_one
        (sourceWordValue encodingLength formula word) hnonzero
      have hcard := GapCVP.Core.sourceFiniteField_card
        (GapCVP.Core.sourceSizeParameter_ge_one_hundred
          encodingLength formula)
      rw [hcard] at hfermat
      exact hfermat


-- @@ L4430-4430 verbatim
end BinaryFieldInverseAlgebra



-- @@ L4433-4433 verbatim
end GapCVP


-- @@ L4435-4435 verbatim
end
