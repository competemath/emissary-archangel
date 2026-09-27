/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part11A


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 11, continuation 02 -/


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
namespace BinaryFieldInverseTM


-- @@ L27-27 verbatim
section


-- @@ L29-29 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder


-- @@ L31-31 verbatim
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.BinaryModularReductionTM


-- @@ L33-33 verbatim
open GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L35-35 verbatim
end


-- @@ L37-37 verbatim
end BinaryFieldInverseTM


-- @@ L39-39 verbatim
namespace BinarySourceConvolutionTM


-- @@ L41-41 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L42-42 verbatim
open GapCVP.SourceStructuralTuringTM GapCVP.SourceMachineCert

-- @@ L43-43 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold

-- @@ L44-44 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L45-45 verbatim
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM

-- @@ L46-46 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L47-47 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.SourceFourFamilyMarkerRotationTM

-- @@ L48-48 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.CNFCappedUnaryPairArithmeticTM

-- @@ L49-49 verbatim
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L50-50 verbatim
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.CLStructuralPrefixWriter

-- @@ L51-51 verbatim
open GapCVP.BinaryCoefficientTM GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L53-58 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinarySourceSkipFields :
    ℕ → (List Bool → List Bool)
  | 0 => id
  | count + 1 => firstFieldSuffix ∘
      factor400BinarySourceSkipFields count


-- @@ L60-70 verbatim
/-- GapCVP reduction support. -/
noncomputable def binarySourceSkipFieldsComputable
    (count : ℕ) :
    BitTM
      (factor400BinarySourceSkipFields count) := by
  induction count with
  | zero =>
      exact Turing.idComputableInPolyTime bitEncoding
  | succ count ih =>
      exact GapCVP.TMComposition.computableInPolyTime
        ih firstFieldSuffixComputable


-- @@ L72-74 verbatim
private def binarySourceCoefficientDegreeUnary
    (input : List Bool) : List Bool :=
  List.replicate (factor400BinarySourceLeftBits input).length true


-- @@ L76-85 verbatim
private noncomputable def factor400BinarySourceCoefficientDegreeUnaryComputable :
    BitTM
      binarySourceCoefficientDegreeUnary := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    binarySourceLeftBitsComputable
    (polynomialValueUnaryComputable Polynomial.X)
  change BitTM
    (fun input => List.replicate
      (factor400BinarySourceLeftBits input).length true)
  simpa only [Polynomial.eval_X, Function.comp_def] using hphysical


-- @@ L87-90 verbatim
private def binarySourceConvolutionPairWidthOutput
    (input : List Bool) : List Bool :=
  List.replicate
    ((factor400BinarySourceLeftBits input).length ^ 2) true


-- @@ L92-101 verbatim
private noncomputable def factor400BinarySourceConvolutionPairWidthComputable :
    BitTM
      binarySourceConvolutionPairWidthOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    binarySourceLeftBitsComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 2))
  change BitTM
    (fun input => List.replicate
      ((factor400BinarySourceLeftBits input).length ^ 2) true)
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Function.comp_def] using hphysical


-- @@ L103-106 verbatim
/-- Prefix the source with the unary index of the requested convolution coefficient. -/
def binarySourceConvolutionCoefficientQuery
    (coefficient : ℕ) (source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate coefficient true) ++ source


-- @@ L108-110 verbatim
private def binarySourceConvolutionPairRawSource :
    List Bool → List Bool :=
  factor400BinarySourceSkipFields 3


-- @@ L112-115 verbatim
private noncomputable def binarySourceConvolutionPairRawSourceComputable :
    BitTM
      binarySourceConvolutionPairRawSource :=
  binarySourceSkipFieldsComputable 3


-- @@ L117-120 verbatim
private def factor400BinarySourceConvolutionPairDegreeUnary :
    List Bool → List Bool :=
  binarySourceCoefficientDegreeUnary ∘
    binarySourceConvolutionPairRawSource


-- @@ L122-127 verbatim
private noncomputable def factor400BinarySourceConvolutionPairDegreeUnaryComputable :
    BitTM
      factor400BinarySourceConvolutionPairDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    binarySourceConvolutionPairRawSourceComputable
    factor400BinarySourceCoefficientDegreeUnaryComputable


-- @@ L129-131 verbatim
private def binarySourceConvolutionPairRankUnary :
    List Bool → List Bool :=
  firstFieldContents


-- @@ L133-136 verbatim
private noncomputable def factor400BinarySourceConvolutionPairRankUnaryComputable :
    BitTM
      binarySourceConvolutionPairRankUnary :=
  firstFieldContentsComputable


-- @@ L138-142 verbatim
private def binarySourceConvolutionPairDivisionQuery
    (input : List Bool) : List Bool :=
  binarySourceConvolutionPairRankUnary input ++ false ::
    (factor400BinarySourceConvolutionPairDegreeUnary input ++ false ::
      binarySourceConvolutionPairRawSource input)


-- @@ L144-155 verbatim
private noncomputable def factor400BinarySourceConvolutionPairDivisionQueryComputable :
    BitTM
      binarySourceConvolutionPairDivisionQuery := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    binarySourceConvolutionPairRawSourceComputable
    (prependBitComputable false)
  have hdegree := pointwiseAppendComputable
    factor400BinarySourceConvolutionPairDegreeUnaryComputable hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    hdegree (prependBitComputable false)
  exact pointwiseAppendComputable
    factor400BinarySourceConvolutionPairRankUnaryComputable hseparator


-- @@ L157-160 verbatim
private def binarySourceConvolutionPairOdometer :
    List Bool → List Bool :=
  sourceMixedRadixRowMajorPairOutput ∘
    binarySourceConvolutionPairDivisionQuery


-- @@ L162-167 verbatim
private noncomputable def factor400BinarySourceConvolutionPairOdometerComputable :
    BitTM
      binarySourceConvolutionPairOdometer :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionPairDivisionQueryComputable
    sourceMixedRadixRowMajorPairComputable


-- @@ L169-172 verbatim
private def binarySourceConvolutionPairFirstUnary
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (binarySourceConvolutionPairOdometer input)).tail


-- @@ L174-181 verbatim
private noncomputable def factor400BinarySourceConvolutionPairFirstUnaryComputable :
    BitTM
      binarySourceConvolutionPairFirstUnary := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionPairOdometerComputable
    unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable


-- @@ L183-187 verbatim
private def binarySourceConvolutionPairSecondUnary
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (binarySourceConvolutionPairOdometer input))).tail


-- @@ L189-198 verbatim
private noncomputable def factor400BinarySourceConvolutionPairSecondUnaryComputable :
    BitTM
      binarySourceConvolutionPairSecondUnary := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionPairOdometerComputable
    actualUnaryPrefixSuffixComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hsuffix unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable


-- @@ L200-203 verbatim
private def binarySourceConvolutionPairLeftWord :
    List Bool → List Bool :=
  factor400BinarySourceLeftBits ∘
    binarySourceConvolutionPairRawSource


-- @@ L205-210 verbatim
private noncomputable def factor400BinarySourceConvolutionPairLeftWordComputable :
    BitTM
      binarySourceConvolutionPairLeftWord :=
  GapCVP.TMComposition.computableInPolyTime
    binarySourceConvolutionPairRawSourceComputable
    binarySourceLeftBitsComputable


-- @@ L212-215 verbatim
private def binarySourceConvolutionPairRightWord :
    List Bool → List Bool :=
  factor400BinarySourceRightBits ∘
    binarySourceConvolutionPairRawSource


-- @@ L217-222 verbatim
private noncomputable def factor400BinarySourceConvolutionPairRightWordComputable :
    BitTM
      binarySourceConvolutionPairRightWord :=
  GapCVP.TMComposition.computableInPolyTime
    binarySourceConvolutionPairRawSourceComputable
    binarySourceRightBitsComputable


-- @@ L224-228 verbatim
private def binarySourceConvolutionPairLeftBit :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    binarySourceConvolutionPairFirstUnary
    binarySourceConvolutionPairLeftWord


-- @@ L230-235 verbatim
private noncomputable def factor400BinarySourceConvolutionPairLeftBitComputable :
    BitTM
      binarySourceConvolutionPairLeftBit :=
  fiveOriginalDynamicBitComputable
    factor400BinarySourceConvolutionPairFirstUnaryComputable
    factor400BinarySourceConvolutionPairLeftWordComputable


-- @@ L237-241 verbatim
private def binarySourceConvolutionPairRightBit :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    binarySourceConvolutionPairSecondUnary
    binarySourceConvolutionPairRightWord


-- @@ L243-248 verbatim
private noncomputable def factor400BinarySourceConvolutionPairRightBitComputable :
    BitTM
      binarySourceConvolutionPairRightBit :=
  fiveOriginalDynamicBitComputable
    factor400BinarySourceConvolutionPairSecondUnaryComputable
    factor400BinarySourceConvolutionPairRightWordComputable


-- @@ L250-252 verbatim
private def binarySourceConvolutionPairCoefficientUnary :
    List Bool → List Bool :=
  firstFieldContents ∘ factor400BinarySourceSkipFields 2


-- @@ L254-259 verbatim
private noncomputable def factor400BinarySourceConvolutionPairCoefficientUnaryComputable :
    BitTM
      binarySourceConvolutionPairCoefficientUnary :=
  GapCVP.TMComposition.computableInPolyTime
    (binarySourceSkipFieldsComputable 2)
    firstFieldContentsComputable


-- @@ L261-265 verbatim
private def binarySourceConvolutionPairSumUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    binarySourceConvolutionPairFirstUnary
    binarySourceConvolutionPairSecondUnary


-- @@ L267-272 verbatim
private noncomputable def factor400BinarySourceConvolutionPairSumUnaryComputable :
    BitTM
      binarySourceConvolutionPairSumUnary :=
  fourFamilyComputedUnarySumComputable
    factor400BinarySourceConvolutionPairFirstUnaryComputable
    factor400BinarySourceConvolutionPairSecondUnaryComputable


-- @@ L274-279 verbatim
private def binarySourceConvolutionPairMatchInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (binarySourceConvolutionPairSumUnary input) ++
    lengthPrefixedWord
      (binarySourceConvolutionPairCoefficientUnary input)


-- @@ L281-290 verbatim
private noncomputable def factor400BinarySourceConvolutionPairMatchInputComputable :
    BitTM
      binarySourceConvolutionPairMatchInput := by
  have hleft := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionPairSumUnaryComputable
    structuralPrefixWriterComputable
  have hright := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionPairCoefficientUnaryComputable
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable hleft hright


-- @@ L292-295 verbatim
private def binarySourceConvolutionEqualOrderingBit
    (input : List Bool) : List Bool :=
  fixedDelimitedWordEqualityBitWord [true, false]
    (lengthPrefixedWord input)


-- @@ L297-303 verbatim
private noncomputable def factor400BinarySourceConvolutionEqualOrderingBitComputable :
    BitTM
      binarySourceConvolutionEqualOrderingBit := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    structuralPrefixWriterComputable
    (fixedDelimitedWordEqualityBitComputable [true, false])
  exact hphysical


-- @@ L305-310 verbatim
private def binarySourceConvolutionPairMatchBit :
    List Bool → List Bool :=
  binarySourceConvolutionEqualOrderingBit ∘
    fourFamilyNaturalOrderingBitsOutput ∘
    fourFamilyDelimitedUnaryComparisonInput ∘
    binarySourceConvolutionPairMatchInput


-- @@ L312-321 verbatim
private noncomputable def factor400BinarySourceConvolutionPairMatchBitComputable :
    BitTM
      binarySourceConvolutionPairMatchBit := by
  exact GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (GapCVP.TMComposition.computableInPolyTime
        factor400BinarySourceConvolutionPairMatchInputComputable
        sourceFourFamilyDelimitedUnaryComparisonInputComputable)
      sourceFourFamilyNaturalOrderingBitsComputable)
    factor400BinarySourceConvolutionEqualOrderingBitComputable


-- @@ L323-326 verbatim
private def factor400BinarySourceConvolutionPairProductTail
    (input : List Bool) : List Bool :=
  binarySourceConvolutionPairLeftBit input ++
    binarySourceConvolutionPairRightBit input


-- @@ L328-333 verbatim
private noncomputable def factor400BinarySourceConvolutionPairProductTailComputable :
    BitTM
      factor400BinarySourceConvolutionPairProductTail :=
  pointwiseAppendComputable
    factor400BinarySourceConvolutionPairLeftBitComputable
    factor400BinarySourceConvolutionPairRightBitComputable


-- @@ L335-338 verbatim
private def factor400BinarySourceConvolutionPairProductQuery
    (input : List Bool) : List Bool :=
  binarySourceConvolutionPairMatchBit input ++
    factor400BinarySourceConvolutionPairProductTail input


-- @@ L340-345 verbatim
private noncomputable def factor400BinarySourceConvolutionPairProductQueryComputable :
    BitTM
      factor400BinarySourceConvolutionPairProductQuery :=
  pointwiseAppendComputable
    factor400BinarySourceConvolutionPairMatchBitComputable
    factor400BinarySourceConvolutionPairProductTailComputable


-- @@ L347-349 verbatim
private def factor400BinarySourceConvolutionCoefficientRawSource :
    List Bool → List Bool :=
  firstFieldSuffix


-- @@ L351-355 verbatim
/-- Read the convolution pair width from the coefficient query's raw source. -/
def binarySourceConvolutionCoefficientPairWidthOutput :
    List Bool → List Bool :=
  binarySourceConvolutionPairWidthOutput ∘
    factor400BinarySourceConvolutionCoefficientRawSource


-- @@ L357-362 verbatim
private noncomputable def factor400BinarySourceConvolutionCoefficientPairWidthComputable :
    BitTM
      binarySourceConvolutionCoefficientPairWidthOutput :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable
    factor400BinarySourceConvolutionPairWidthComputable


-- @@ L364-367 verbatim
private noncomputable def binarySourceConvolutionPairWidth :
    SourceQaryMaskDynamicGridWidth where
  output := binarySourceConvolutionCoefficientPairWidthOutput
  computer := factor400BinarySourceConvolutionCoefficientPairWidthComputable


-- @@ L369-373 verbatim
private def binarySourceConvolutionPairCatalogue :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    binarySourceConvolutionPairWidth
    factor400BinarySourceConvolutionPairProductQueryComputable


-- @@ L375-380 verbatim
private noncomputable def factor400BinarySourceConvolutionPairCatalogueComputable :
    BitTM
      binarySourceConvolutionPairCatalogue :=
  maskDynamicGridCandidateCatalogueComputable
    binarySourceConvolutionPairWidth
    factor400BinarySourceConvolutionPairProductQueryComputable


-- @@ L382-388 verbatim
private def binarySourceConvolutionCoefficientPackedQuery
    (input : List Bool) : List Bool :=
  binarySourceConvolutionCoefficientPairWidthOutput input ++
    false ::
      (binarySourceConvolutionPairCatalogue input ++
        (binarySourceConvolutionCoefficientPairWidthOutput input ++
          [false, false]))


-- @@ L390-402 verbatim
private noncomputable def factor400BinarySourceConvolutionCoefficientPackedQueryComputable :
    BitTM
      binarySourceConvolutionCoefficientPackedQuery := by
  have hparity := pointwiseAppendComputable
    factor400BinarySourceConvolutionCoefficientPairWidthComputable
    (sourceFixedWordComputable [false, false])
  have hrecords := pointwiseAppendComputable
    factor400BinarySourceConvolutionPairCatalogueComputable hparity
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hrecords (prependBitComputable false)
  exact pointwiseAppendComputable
    factor400BinarySourceConvolutionCoefficientPairWidthComputable
    hdelimited


-- @@ L404-407 verbatim
private def binarySourceConvolutionCoefficientBit :
    List Bool → List Bool :=
  convolutionCoefficientOutput ∘
    binarySourceConvolutionCoefficientPackedQuery


-- @@ L409-414 verbatim
private noncomputable def factor400BinarySourceConvolutionCoefficientBitComputable :
    BitTM
      binarySourceConvolutionCoefficientBit :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceConvolutionCoefficientPackedQueryComputable
    convolutionCoefficientComputable


-- @@ L416-419 verbatim
private def binarySourceRawConvolutionWidthOutput
    (input : List Bool) : List Bool :=
  List.replicate
    (2 * (factor400BinarySourceLeftBits input).length) true


-- @@ L421-431 verbatim
private noncomputable def factor400BinarySourceRawConvolutionWidthComputable :
    BitTM
      binarySourceRawConvolutionWidthOutput := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    binarySourceLeftBitsComputable
    (polynomialValueUnaryComputable (2 * Polynomial.X))
  change BitTM
    (fun input => List.replicate
      (2 * (factor400BinarySourceLeftBits input).length) true)
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Function.comp_def]
      using hphysical


-- @@ L433-436 verbatim
private noncomputable def binarySourceRawConvolutionWidth :
    SourceQaryMaskDynamicGridWidth where
  output := binarySourceRawConvolutionWidthOutput
  computer := factor400BinarySourceRawConvolutionWidthComputable


-- @@ L438-440 verbatim
private def factor400BinarySourceRawConvolutionRankSource :
    List Bool → List Bool :=
  factor400BinarySourceSkipFields 2


-- @@ L442-445 verbatim
private noncomputable def factor400BinarySourceRawConvolutionRankSourceComputable :
    BitTM
      factor400BinarySourceRawConvolutionRankSource :=
  binarySourceSkipFieldsComputable 2


-- @@ L447-450 verbatim
private def binarySourceRawConvolutionCoefficientInput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input) ++
    factor400BinarySourceRawConvolutionRankSource input


-- @@ L452-458 verbatim
private noncomputable def factor400BinarySourceRawConvolutionCoefficientInputComputable :
    BitTM
      binarySourceRawConvolutionCoefficientInput := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  exact pointwiseAppendComputable hrank
    factor400BinarySourceRawConvolutionRankSourceComputable


-- @@ L460-463 verbatim
private def binarySourceRawConvolutionCoefficientCandidate :
    List Bool → List Bool :=
  binarySourceConvolutionCoefficientBit ∘
    binarySourceRawConvolutionCoefficientInput


-- @@ L465-470 verbatim
private noncomputable def factor400BinarySourceRawConvolutionCoefficientCandidateComputable :
    BitTM
      binarySourceRawConvolutionCoefficientCandidate :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceRawConvolutionCoefficientInputComputable
    factor400BinarySourceConvolutionCoefficientBitComputable


-- @@ L472-476 verbatim
private def binarySourceRawConvolutionCoefficientCatalogue :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    binarySourceRawConvolutionWidth
    factor400BinarySourceRawConvolutionCoefficientCandidateComputable


-- @@ L478-483 verbatim
private noncomputable def factor400BinarySourceRawConvolutionCoefficientCatalogueComputable :
    BitTM
      binarySourceRawConvolutionCoefficientCatalogue :=
  maskDynamicGridCandidateCatalogueComputable
    binarySourceRawConvolutionWidth
    factor400BinarySourceRawConvolutionCoefficientCandidateComputable


-- @@ L485-488 verbatim
private def binarySourceRawConvolutionPackedOutput
    (input : List Bool) : List Bool :=
  binarySourceRawConvolutionWidthOutput input ++ false ::
    binarySourceRawConvolutionCoefficientCatalogue input


-- @@ L490-497 verbatim
private noncomputable def factor400BinarySourceRawConvolutionPackedOutputComputable :
    BitTM
      binarySourceRawConvolutionPackedOutput := by
  have hrecords := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceRawConvolutionCoefficientCatalogueComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    factor400BinarySourceRawConvolutionWidthComputable hrecords


-- @@ L499-504 verbatim
private theorem factor400BinarySourceRawConvolutionHeadMarker_length
    (input : List Bool) :
    (fiveFamilyOriginalHeadBitWord input).length ≤ 1 := by
  simp only [fiveFamilyOriginalHeadBitWord_eq, List.headD_eq_head?_getD, List.length_cons,
      List.length_nil,
      zero_add, Std.le_refl]


-- @@ L506-512 verbatim
/-- GapCVP reduction support. -/
def binarySourceRawConvolutionWord :
    List Bool → List Bool :=
  boundedRecordFoldOutput
      (fourFamilyOriginalMarkerRotationOutput
        fiveFamilyOriginalHeadBitWord) ∘
    binarySourceRawConvolutionPackedOutput


-- @@ L514-522 verbatim
/-- GapCVP reduction support. -/
noncomputable def factor400BinarySourceRawConvolutionComputable :
    BitTM
      binarySourceRawConvolutionWord := by
  have hfold := fourFamilyOriginalMarkerFoldComputable
    fiveFamilyOriginalHeadBitComputable
    factor400BinarySourceRawConvolutionHeadMarker_length
  exact GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceRawConvolutionPackedOutputComputable hfold


-- @@ L524-524 verbatim
end BinarySourceConvolutionTM


-- @@ L526-526 verbatim
namespace BinarySourceConvolutionCorrectness


-- @@ L528-528 verbatim
section


-- @@ L530-530 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L531-531 verbatim
open GapCVP.SourceStructuralTuringTM GapCVP.OutputBoundedDependentRecordFold

-- @@ L532-532 verbatim
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

-- @@ L533-533 verbatim
open GapCVP.SourceMixedRadixDimensionRowMajorIndexTM

-- @@ L534-534 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L535-535 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

-- @@ L536-536 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L537-537 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM

-- @@ L538-538 verbatim
open GapCVP.CNFCappedUnaryPairArithmeticTM GapCVP.CNFEncodedClauseSort

-- @@ L539-539 verbatim
open GapCVP.CNFNaturalOrderComparator GapCVP.CNFNaturalOrderTotalComparator

-- @@ L540-540 verbatim
open GapCVP.CNFGuardedFiveFamilyTagDispatchTM GapCVP.BinaryCoefficientTM

-- @@ L541-541 verbatim
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM

-- @@ L542-542 verbatim
open GapCVP.BinarySourceConvolutionTM


-- @@ L544-549 verbatim
private def binarySourceConvolutionPhysicalPairQuery
    (rank : ℕ) (width : List Bool) (coefficient : ℕ)
    (raw : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    lengthPrefixedWord width ++
      lengthPrefixedWord (List.replicate coefficient true) ++ raw


-- @@ L551-560 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairRawSource_query
    (rank : ℕ) (width : List Bool) (coefficient : ℕ)
    (raw : List Bool) :
    binarySourceConvolutionPairRawSource
      (binarySourceConvolutionPhysicalPairQuery
        rank width coefficient raw) = raw := by
  simp only [binarySourceConvolutionPairRawSource, factor400BinarySourceSkipFields,
      CompTriple.comp_eq,
      binarySourceConvolutionPhysicalPairQuery, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid]


-- @@ L562-571 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairRankUnary_query
    (rank : ℕ) (width : List Bool) (coefficient : ℕ)
    (raw : List Bool) :
    binarySourceConvolutionPairRankUnary
      (binarySourceConvolutionPhysicalPairQuery
        rank width coefficient raw) =
      List.replicate rank true := by
  simp only [binarySourceConvolutionPairRankUnary, binarySourceConvolutionPhysicalPairQuery,
      List.append_assoc,
      firstFieldContents_valid]


-- @@ L573-584 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairCoefficientUnary_query
    (rank : ℕ) (width : List Bool) (coefficient : ℕ)
    (raw : List Bool) :
    binarySourceConvolutionPairCoefficientUnary
      (binarySourceConvolutionPhysicalPairQuery
        rank width coefficient raw) =
      List.replicate coefficient true := by
  simp only [binarySourceConvolutionPairCoefficientUnary, factor400BinarySourceSkipFields,
      CompTriple.comp_eq,
      binarySourceConvolutionPhysicalPairQuery, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid,
      firstFieldContents_valid]


-- @@ L586-597 verbatim
@[simp] private theorem factor400BinarySourceCoefficientDegreeUnary_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceCoefficientDegreeUnary
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      List.replicate degree true := by
  simp only [binarySourceCoefficientDegreeUnary, factor400BinarySourceLeftBits_query,
      factor400BinaryFiniteWordBits_length]


-- @@ L599-610 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairWidthOutput_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceConvolutionPairWidthOutput
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      List.replicate (degree ^ 2) true := by
  simp only [binarySourceConvolutionPairWidthOutput, factor400BinarySourceLeftBits_query,
      factor400BinaryFiniteWordBits_length]


-- @@ L612-632 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairDivisionQuery_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairDivisionQuery
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      sourceUnaryDivisionQuery rank degree
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source) := by
  simp only [binarySourceConvolutionPairDivisionQuery,
      factor400BinarySourceConvolutionPairRankUnary_query,
      factor400BinarySourceConvolutionPairDegreeUnary, Function.comp_apply,
      factor400BinarySourceConvolutionPairRawSource_query,
          factor400BinarySourceCoefficientDegreeUnary_query,
      sourceUnaryDivisionQuery]


-- @@ L634-655 verbatim
private theorem factor400BinarySourceConvolutionPairOdometer_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairOdometer
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      List.replicate (rank / degree) true ++ false ::
        (List.replicate (rank % degree) true ++ false ::
          sourceUnaryDivisionQuery rank degree
            (factor400BinarySourceFieldQuery
              (finiteWordBits lower)
              (finiteWordBits left)
              (finiteWordBits right) source)) := by
  unfold binarySourceConvolutionPairOdometer
  rw [Function.comp_apply,
    factor400BinarySourceConvolutionPairDivisionQuery_query,
    sourceMixedRadixRowMajorPairOutput_valid rank degree _ hdegree]


-- @@ L657-673 verbatim
private theorem factor400BinarySourceConvolutionPairFirstUnary_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairFirstUnary
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      List.replicate (rank / degree) true := by
  unfold binarySourceConvolutionPairFirstUnary
  rw [factor400BinarySourceConvolutionPairOdometer_query
    hdegree lower left right source width coefficient rank,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L675-692 verbatim
private theorem factor400BinarySourceConvolutionPairSecondUnary_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairSecondUnary
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      List.replicate (rank % degree) true := by
  unfold binarySourceConvolutionPairSecondUnary
  rw [factor400BinarySourceConvolutionPairOdometer_query
    hdegree lower left right source width coefficient rank,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L694-705 verbatim
theorem factor400BinaryFiniteWordBits_drop_head
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (hposition : position < degree) :
    ((finiteWordBits word).drop position).headD false =
      word ⟨position, hposition⟩ := by
  have hlength : position < (finiteWordBits word).length := by
    simpa only [factor400BinaryFiniteWordBits_length] using hposition
  rw [List.drop_eq_getElem_cons hlength]
  simp only [finiteWordBits, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      List.headD_eq_head?_getD,
      List.head?_cons, Option.getD_some]


-- @@ L707-719 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairLeftWord_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairLeftWord
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      finiteWordBits left := by
  simp only [binarySourceConvolutionPairLeftWord, Function.comp_apply,
      factor400BinarySourceConvolutionPairRawSource_query, factor400BinarySourceLeftBits_query]


-- @@ L721-733 verbatim
@[simp] private theorem factor400BinarySourceConvolutionPairRightWord_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairRightWord
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      finiteWordBits right := by
  simp only [binarySourceConvolutionPairRightWord, Function.comp_apply,
      factor400BinarySourceConvolutionPairRawSource_query, factor400BinarySourceRightBits_query]


-- @@ L735-772 verbatim
private theorem factor400BinarySourceConvolutionPairLeftBit_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ)
    (hrank : rank < degree ^ 2) :
    binarySourceConvolutionPairLeftBit
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      [left ⟨rank / degree, by
        apply (Nat.div_lt_iff_lt_mul hdegree).2
        simpa only [pow_two] using hrank⟩] := by
  let input := binarySourceConvolutionPhysicalPairQuery
    rank width coefficient
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source)
  have hfirst := factor400BinarySourceConvolutionPairFirstUnary_query
    hdegree lower left right source width coefficient rank
  have hlookup := fiveOriginalDynamicBitWord_valid
    binarySourceConvolutionPairFirstUnary
    binarySourceConvolutionPairLeftWord
    input (rank / degree) hfirst
  unfold binarySourceConvolutionPairLeftBit
  change fiveFamilyOriginalDynamicBitWord
    binarySourceConvolutionPairFirstUnary
    binarySourceConvolutionPairLeftWord input = _
  rw [hlookup,
    factor400BinarySourceConvolutionPairLeftWord_query]
  congr 1
  exact factor400BinaryFiniteWordBits_drop_head
    left (rank / degree)
      ((Nat.div_lt_iff_lt_mul hdegree).2
        (by simpa only [pow_two] using hrank))


-- @@ L774-806 verbatim
private theorem factor400BinarySourceConvolutionPairRightBit_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairRightBit
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      [right ⟨rank % degree, Nat.mod_lt rank hdegree⟩] := by
  let input := binarySourceConvolutionPhysicalPairQuery
    rank width coefficient
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source)
  have hsecond := factor400BinarySourceConvolutionPairSecondUnary_query
    hdegree lower left right source width coefficient rank
  have hlookup := fiveOriginalDynamicBitWord_valid
    binarySourceConvolutionPairSecondUnary
    binarySourceConvolutionPairRightWord
    input (rank % degree) hsecond
  unfold binarySourceConvolutionPairRightBit
  change fiveFamilyOriginalDynamicBitWord
    binarySourceConvolutionPairSecondUnary
    binarySourceConvolutionPairRightWord input = _
  rw [hlookup,
    factor400BinarySourceConvolutionPairRightWord_query]
  congr 1
  exact factor400BinaryFiniteWordBits_drop_head
    right (rank % degree) (Nat.mod_lt rank hdegree)


-- @@ L808-819 verbatim
@[simp] private theorem factor400BinarySourceConvolutionEqualOrderingBit_ordering
    (outcome : EncodedWordOrdering) :
    binarySourceConvolutionEqualOrderingBit
      (encodedWordOrderingWord outcome) =
      [decide (outcome = .equal)] := by
  unfold binarySourceConvolutionEqualOrderingBit
  rw [fixedDelimitedWordEqualityBitWord_eq]
  have hselector := fixedDelimitedWordEqualitySelector_valid
    [true, false] (encodedWordOrderingWord outcome) []
  simp only [List.append_nil] at hselector
  rw [hselector]
  cases outcome <;> rfl


-- @@ L821-841 verbatim
private theorem factor400BinarySourceConvolutionPairSumUnary_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairSumUnary
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      List.replicate (rank / degree + rank % degree) true := by
  unfold binarySourceConvolutionPairSumUnary
  apply fourFamilyComputedUnarySumOutput_valid
    binarySourceConvolutionPairFirstUnary
    binarySourceConvolutionPairSecondUnary
    _ (rank / degree) (rank % degree)
  · exact factor400BinarySourceConvolutionPairFirstUnary_query
      hdegree lower left right source width coefficient rank
  · exact factor400BinarySourceConvolutionPairSecondUnary_query
      hdegree lower left right source width coefficient rank


-- @@ L843-861 verbatim
private theorem factor400BinarySourceConvolutionPairMatchInput_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairMatchInput
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      lengthPrefixedWord
          (List.replicate (rank / degree + rank % degree) true) ++
        lengthPrefixedWord
          (List.replicate coefficient true) := by
  unfold binarySourceConvolutionPairMatchInput
  rw [factor400BinarySourceConvolutionPairSumUnary_query
    hdegree lower left right source width coefficient rank,
    factor400BinarySourceConvolutionPairCoefficientUnary_query]


-- @@ L863-901 verbatim
private theorem factor400BinarySourceConvolutionPairMatchBit_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ) :
    binarySourceConvolutionPairMatchBit
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      [decide (rank / degree + rank % degree = coefficient)] := by
  unfold binarySourceConvolutionPairMatchBit
  simp only [Function.comp_apply]
  rw [factor400BinarySourceConvolutionPairMatchInput_query
    hdegree lower left right source width coefficient rank]
  rw [show lengthPrefixedWord
        (List.replicate (rank / degree + rank % degree) true) ++
        lengthPrefixedWord (List.replicate coefficient true) =
      lengthPrefixedWord
        (List.replicate (rank / degree + rank % degree) true) ++
        lengthPrefixedWord (List.replicate coefficient true) ++ [] by
      simp only [List.append_nil]]
  rw [sourceFourFamilyDelimitedUnaryComparisonInput_valid]
  unfold fourFamilyNaturalOrderingBitsOutput
  rw [show lengthPrefixedWord
        (Computability.encodeNat (rank / degree + rank % degree)) ++
        lengthPrefixedWord (Computability.encodeNat coefficient) =
      lengthPrefixedWord
        (Computability.encodeNat (rank / degree + rank % degree)) ++
        lengthPrefixedWord (Computability.encodeNat coefficient) ++ [] by
      simp only [List.append_nil]]
  rw [sourcePreservingNaturalComparison_valid
    (Computability.encodeNat (rank / degree + rank % degree))
    (Computability.encodeNat coefficient) [],
    firstFieldSuffix_valid,
    factor400BinarySourceConvolutionEqualOrderingBit_ordering,
    littleEndianNaturalOrdering_encodeNat]
  split_ifs <;> simp_all <;> omega


-- @@ L903-928 verbatim
private theorem factor400BinarySourceConvolutionPairProductQuery_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source width : List Bool) (coefficient rank : ℕ)
    (hrank : rank < degree ^ 2) :
    factor400BinarySourceConvolutionPairProductQuery
      (binarySourceConvolutionPhysicalPairQuery rank width coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      [decide (rank / degree + rank % degree = coefficient),
        left ⟨rank / degree, by
          apply (Nat.div_lt_iff_lt_mul hdegree).2
          simpa only [pow_two] using hrank⟩,
        right ⟨rank % degree, Nat.mod_lt rank hdegree⟩] := by
  unfold factor400BinarySourceConvolutionPairProductQuery
    factor400BinarySourceConvolutionPairProductTail
  rw [factor400BinarySourceConvolutionPairMatchBit_query
    hdegree lower left right source width coefficient rank,
    factor400BinarySourceConvolutionPairLeftBit_query
      hdegree lower left right source width coefficient rank hrank,
    factor400BinarySourceConvolutionPairRightBit_query
      hdegree lower left right source width coefficient rank]
  rfl


-- @@ L930-940 verbatim
theorem factor400BinarySourceConvolution_range_mul_flatMap
    (outer inner : ℕ) :
    List.range (outer * inner) =
      (List.range outer).flatMap
        (fun row => (List.range inner).map
          (fun column => row * inner + column)) := by
  induction outer with
  | zero => simp only [zero_mul, List.range_zero, List.flatMap_nil]
  | succ outer ih =>
      rw [Nat.succ_mul, List.range_add, ih, List.range_succ]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]


-- @@ L942-957 verbatim
@[simp] theorem
    factor400BinarySourceConvolutionCoefficientPairWidthOutput_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (coefficient : ℕ) (source : List Bool) :
    binarySourceConvolutionCoefficientPairWidthOutput
      (binarySourceConvolutionCoefficientQuery coefficient
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      List.replicate (degree ^ 2) true := by
  simp only [binarySourceConvolutionCoefficientPairWidthOutput,
      factor400BinarySourceConvolutionCoefficientRawSource,
          binarySourceConvolutionCoefficientQuery, Function.comp_apply,
      firstFieldSuffix_valid, factor400BinarySourceConvolutionPairWidthOutput_query]


-- @@ L959-1028 verbatim
private theorem factor400BinarySourceConvolutionPairCatalogue_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (coefficient : Fin (2 * degree)) (source : List Bool) :
    binarySourceConvolutionPairCatalogue
      (binarySourceConvolutionCoefficientQuery coefficient.val
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      sourceMixedRadixOriginalSourceQueryStream
        (wordConvolutionQueries left right coefficient) := by
  let raw := factor400BinarySourceFieldQuery
    (finiteWordBits lower)
    (finiteWordBits left)
    (finiteWordBits right) source
  let input := binarySourceConvolutionCoefficientQuery
    coefficient.val raw
  have hwidth : binarySourceConvolutionPairWidth.output input =
      List.replicate (degree ^ 2) true := by
    exact factor400BinarySourceConvolutionCoefficientPairWidthOutput_query
      lower left right coefficient.val source
  have hcatalogue := maskDynamicGridCandidateCatalogueOutput_valid
    binarySourceConvolutionPairWidth
    factor400BinarySourceConvolutionPairProductQueryComputable
    input (degree ^ 2) hwidth
  change binarySourceConvolutionPairCatalogue input = _
  unfold binarySourceConvolutionPairCatalogue
  rw [hcatalogue]
  rw [pow_two, factor400BinarySourceConvolution_range_mul_flatMap]
  have hfin : List.range degree =
      (List.finRange degree).map (fun index => index.val) :=
    List.map_coe_finRange_eq_range.symm
  simp_rw [hfin]
  simp only [List.flatMap_map]
  unfold sourceMixedRadixOriginalSourceQueryStream
    wordConvolutionQueries
  simp only [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro row _
  apply List.flatMap_congr
  intro column _
  have hrank : row.val * degree + column.val < degree ^ 2 := by
    have hrow := row.isLt
    have hcolumn := column.isLt
    nlinarith
  have hdiv : (row.val * degree + column.val) / degree = row.val := by
    simpa only [Nat.mul_comm, Nat.div_eq_of_lt column.isLt, add_zero] using
        Nat.mul_add_div hdegree row.val column.val
  have hmod : (row.val * degree + column.val) % degree = column.val := by
    exact Nat.mul_add_mod_of_lt column.isLt
  have hquery := factor400BinarySourceConvolutionPairProductQuery_query
    hdegree lower left right source (List.replicate (degree ^ 2) true)
    coefficient.val (row.val * degree + column.val) hrank
  have hbase :
      lengthPrefixedWord
          (List.replicate (row.val * degree + column.val) true) ++
        sourceQaryMaskDynamicGridBaseSource
          binarySourceConvolutionPairWidth input =
      binarySourceConvolutionPhysicalPairQuery
        (row.val * degree + column.val)
        (List.replicate (degree ^ 2) true)
        coefficient.val raw := by
    unfold sourceQaryMaskDynamicGridBaseSource
    rw [hwidth]
    simp only [binarySourceConvolutionCoefficientQuery, binarySourceConvolutionPhysicalPairQuery,
        List.append_assoc, input, raw]
  rw [hbase, hquery]
  simp only [hdiv, hmod]


-- @@ L1030-1049 verbatim
private theorem factor400BinarySourceConvolutionCoefficientPackedQuery_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (coefficient : Fin (2 * degree)) (source : List Bool) :
    binarySourceConvolutionCoefficientPackedQuery
      (binarySourceConvolutionCoefficientQuery coefficient.val
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      wordConvolutionCoefficientQuery left right coefficient := by
  unfold binarySourceConvolutionCoefficientPackedQuery
  simp only [factor400BinarySourceConvolutionCoefficientPairWidthOutput_query]
  rw [factor400BinarySourceConvolutionPairCatalogue_query
    hdegree lower left right coefficient source]
  unfold wordConvolutionCoefficientQuery convolutionCoefficientQuery
    unaryBoundedFoldWord
  rw [wordConvolutionQueries_length]
  simp only [pow_two]


-- @@ L1051-1068 verbatim
private theorem factor400BinarySourceConvolutionCoefficientBit_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (coefficient : Fin (2 * degree)) (source : List Bool) :
    binarySourceConvolutionCoefficientBit
      (binarySourceConvolutionCoefficientQuery coefficient.val
        (factor400BinarySourceFieldQuery
          (finiteWordBits lower)
          (finiteWordBits left)
          (finiteWordBits right) source)) =
      [GapCVP.Core.EffectiveBinaryField.multiplyWords
        left right coefficient] := by
  unfold binarySourceConvolutionCoefficientBit
  rw [Function.comp_apply,
    factor400BinarySourceConvolutionCoefficientPackedQuery_query
      hdegree lower left right coefficient source,
    convolutionCoefficientOutput_word]


-- @@ L1070-1081 verbatim
@[simp] private theorem factor400BinarySourceRawConvolutionWidthOutput_query
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceRawConvolutionWidthOutput
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      List.replicate (2 * degree) true := by
  simp only [binarySourceRawConvolutionWidthOutput, factor400BinarySourceLeftBits_query,
      factor400BinaryFiniteWordBits_length]


-- @@ L1083-1094 verbatim
@[simp] private theorem factor400BinarySourceRawConvolutionCoefficientInput_query
    (rank : ℕ) (raw : List Bool) :
    binarySourceRawConvolutionCoefficientInput
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          binarySourceRawConvolutionWidth raw) =
      binarySourceConvolutionCoefficientQuery rank raw := by
  simp only [binarySourceRawConvolutionCoefficientInput, sourceQaryMaskDynamicGridBaseSource,
      firstFieldContents_valid, factor400BinarySourceRawConvolutionRankSource,
          factor400BinarySourceSkipFields,
      CompTriple.comp_eq, Function.comp_apply, firstFieldSuffix_valid,
          binarySourceConvolutionCoefficientQuery]


-- @@ L1096-1096 verbatim
end


-- @@ L1098-1098 verbatim
section


-- @@ L1100-1100 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.OutputBoundedDependentRecordFold

-- @@ L1101-1101 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L1102-1102 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

-- @@ L1103-1103 verbatim
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.CNFFiveFamilyOriginalIndexedBitTM

-- @@ L1104-1104 verbatim
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM

-- @@ L1105-1105 verbatim
open GapCVP.BinarySourceConvolutionTM


-- @@ L1107-1121 verbatim
private theorem factor400BinarySourceRawConvolutionCoefficientCatalogue_width
    (raw : List Bool) (count : ℕ)
    (hwidth : binarySourceRawConvolutionWidth.output raw =
      List.replicate count true) :
    binarySourceRawConvolutionCoefficientCatalogue raw =
      (List.range count).flatMap fun rank =>
        lengthPrefixedWord
          (binarySourceRawConvolutionCoefficientCandidate
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                binarySourceRawConvolutionWidth raw)) := by
  exact maskDynamicGridCandidateCatalogueOutput_valid
    binarySourceRawConvolutionWidth
    factor400BinarySourceRawConvolutionCoefficientCandidateComputable
    raw count hwidth


-- @@ L1123-1142 verbatim
private theorem factor400BinarySourceRawConvolutionCoefficientCandidate_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (coefficient : Fin (2 * degree)) (source : List Bool) :
    binarySourceRawConvolutionCoefficientCandidate
      (lengthPrefixedWord (List.replicate coefficient.val true) ++
        sourceQaryMaskDynamicGridBaseSource
          binarySourceRawConvolutionWidth
          (factor400BinarySourceFieldQuery
            (finiteWordBits lower)
            (finiteWordBits left)
            (finiteWordBits right) source)) =
      [GapCVP.Core.EffectiveBinaryField.multiplyWords
        left right coefficient] := by
  unfold binarySourceRawConvolutionCoefficientCandidate
  rw [Function.comp_apply,
    factor400BinarySourceRawConvolutionCoefficientInput_query]
  exact factor400BinarySourceConvolutionCoefficientBit_query
    hdegree lower left right coefficient source


-- @@ L1144-1180 verbatim
private theorem factor400BinarySourceRawConvolutionCoefficientCatalogue_query
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceRawConvolutionCoefficientCatalogue
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      sourceMixedRadixOriginalSourceQueryStream
        ((List.finRange (2 * degree)).map fun coefficient =>
          [GapCVP.Core.EffectiveBinaryField.multiplyWords
            left right coefficient]) := by
  let raw := factor400BinarySourceFieldQuery
    (finiteWordBits lower)
    (finiteWordBits left)
    (finiteWordBits right) source
  have hwidth : binarySourceRawConvolutionWidth.output raw =
      List.replicate (2 * degree) true :=
    factor400BinarySourceRawConvolutionWidthOutput_query
      lower left right source
  change binarySourceRawConvolutionCoefficientCatalogue raw = _
  rw [factor400BinarySourceRawConvolutionCoefficientCatalogue_width
    raw (2 * degree) hwidth]
  have hfin : List.range (2 * degree) =
      (List.finRange (2 * degree)).map
        (fun coefficient => coefficient.val) :=
    List.map_coe_finRange_eq_range.symm
  rw [hfin]
  unfold sourceMixedRadixOriginalSourceQueryStream
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro coefficient _
  exact congrArg lengthPrefixedWord
    (factor400BinarySourceRawConvolutionCoefficientCandidate_query
      hdegree lower left right coefficient source)


-- @@ L1182-1230 verbatim
private theorem factor400BinarySourceRawConvolutionWord_valid_of_pos
    {degree : ℕ}
    (hdegree : 0 < degree)
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceRawConvolutionWord
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyWords left right) := by
  let queries : List (List Bool) :=
    (List.finRange (2 * degree)).map fun coefficient =>
      [GapCVP.Core.EffectiveBinaryField.multiplyWords
        left right coefficient]
  unfold binarySourceRawConvolutionWord
    binarySourceRawConvolutionPackedOutput
  rw [Function.comp_apply,
    factor400BinarySourceRawConvolutionWidthOutput_query
      lower left right source,
    factor400BinarySourceRawConvolutionCoefficientCatalogue_query
      hdegree lower left right source]
  have hfold := boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries
    fiveFamilyOriginalHeadBitWord queries []
  calc
    _ = fourFamilyOriginalMarkerStream
        fiveFamilyOriginalHeadBitWord queries := by
          simpa only [unaryBoundedFoldWord, List.length_map, List.length_finRange, List.append_nil,
              List.nil_append,
              queries] using hfold
    _ = _ := by
          unfold fourFamilyOriginalMarkerStream finiteWordBits
          dsimp [queries]
          rw [List.flatMap_map]
          simp_rw [fiveFamilyOriginalHeadBitWord_eq]
          change
            (List.finRange (2 * degree)).flatMap
              (fun coefficient =>
                [GapCVP.Core.EffectiveBinaryField.multiplyWords
                  left right coefficient]) =
              (List.finRange (2 * degree)).map
                (GapCVP.Core.EffectiveBinaryField.multiplyWords left right)
          calc
            _ = ((List.finRange (2 * degree)).map
                (GapCVP.Core.EffectiveBinaryField.multiplyWords left right)).flatMap
                  (fun bit => [bit]) := by
                    rw [List.flatMap_map]
            _ = _ := List.flatMap_singleton' _


-- @@ L1232-1274 verbatim
theorem factor400BinarySourceRawConvolutionWord_valid
    {degree : ℕ}
    (lower left right : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceRawConvolutionWord
      (factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyWords left right) := by
  cases degree with
  | zero =>
      let raw := factor400BinarySourceFieldQuery
        (finiteWordBits lower)
        (finiteWordBits left)
        (finiteWordBits right) source
      have hwidth : binarySourceRawConvolutionWidth.output raw =
          List.replicate 0 true := by
        change binarySourceRawConvolutionWidthOutput
          (factor400BinarySourceFieldQuery
            (finiteWordBits lower)
            (finiteWordBits left)
            (finiteWordBits right) source) = []
        exact factor400BinarySourceRawConvolutionWidthOutput_query
          lower left right source
      have hcatalogue :
          binarySourceRawConvolutionCoefficientCatalogue raw = [] := by
        rw [factor400BinarySourceRawConvolutionCoefficientCatalogue_width
          raw 0 hwidth]
        rfl
      change binarySourceRawConvolutionWord raw = _
      unfold binarySourceRawConvolutionWord
        binarySourceRawConvolutionPackedOutput
      change binarySourceRawConvolutionWidthOutput raw = []
        at hwidth
      rw [Function.comp_apply, hwidth, hcatalogue]
      simp only [boundedRecordFoldOutput, List.nil_append, parseUnaryBoundedFold,
          Function.iterate_zero, id_eq,
          finiteWordBits, Nat.mul_zero, List.finRange_zero, List.map_nil]
  | succ degree =>
      exact factor400BinarySourceRawConvolutionWord_valid_of_pos
        (Nat.zero_lt_succ degree) lower left right source


-- @@ L1276-1276 verbatim
end


-- @@ L1278-1278 verbatim
end BinarySourceConvolutionCorrectness


-- @@ L1280-1280 verbatim
namespace BinarySourceFieldMultiplicationTM


-- @@ L1282-1282 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L1283-1283 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L1284-1284 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM

-- @@ L1285-1285 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryModularReductionTM

-- @@ L1286-1286 verbatim
open GapCVP.BinarySourceConvolutionTM


-- @@ L1288-1291 verbatim
private noncomputable def binarySourceFieldOperandDegreeWidth :
    SourceQaryMaskDynamicGridWidth where
  output := binarySourceCoefficientDegreeUnary
  computer := factor400BinarySourceCoefficientDegreeUnaryComputable


-- @@ L1293-1295 verbatim
private def binarySourceDegreePaddedBitSource
    (field : List Bool → List Bool) : List Bool → List Bool :=
  field ∘ factor400BinarySourceSkipFields 2


-- @@ L1297-1303 verbatim
private noncomputable def factor400BinarySourceDegreePaddedBitSourceComputable
    {field : List Bool → List Bool}
    (computer : BitTM field) :
    BitTM
      (binarySourceDegreePaddedBitSource field) :=
  GapCVP.TMComposition.computableInPolyTime
    (binarySourceSkipFieldsComputable 2) computer


-- @@ L1305-1308 verbatim
private def factor400BinarySourceDegreePaddedBitWord
    (field : List Bool → List Bool) : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    firstFieldContents (binarySourceDegreePaddedBitSource field)


-- @@ L1310-1317 verbatim
private noncomputable def factor400BinarySourceDegreePaddedBitComputable
    {field : List Bool → List Bool}
    (computer : BitTM field) :
    BitTM
      (factor400BinarySourceDegreePaddedBitWord field) :=
  fiveOriginalDynamicBitComputable
    firstFieldContentsComputable
    (factor400BinarySourceDegreePaddedBitSourceComputable computer)


-- @@ L1319-1342 verbatim
@[simp] private theorem factor400BinarySourceDegreePaddedBitWord_query
    (field : List Bool → List Bool)
    (input : List Bool) (rank : ℕ) :
    factor400BinarySourceDegreePaddedBitWord field
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          binarySourceFieldOperandDegreeWidth input) =
      [(field input).getD rank false] := by
  let query := lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      binarySourceFieldOperandDegreeWidth input
  have hindex : firstFieldContents query =
      List.replicate rank true := by
    simp only [firstFieldContents_valid, query]
  unfold factor400BinarySourceDegreePaddedBitWord
  rw [fiveOriginalDynamicBitWord_valid
    firstFieldContents
    (binarySourceDegreePaddedBitSource field)
    query rank hindex]
  simp only [binarySourceDegreePaddedBitSource, factor400BinarySourceSkipFields,
      CompTriple.comp_eq,
      sourceQaryMaskDynamicGridBaseSource, Function.comp_apply, firstFieldSuffix_valid,
          List.headD_eq_head?_getD,
      List.head?_drop, List.getD_eq_getElem?_getD, query]


-- @@ L1344-1349 verbatim
private def binarySourceDegreePaddedFieldBits
    {field : List Bool → List Bool}
    (computer : BitTM field) : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    binarySourceFieldOperandDegreeWidth
    (factor400BinarySourceDegreePaddedBitComputable computer)


-- @@ L1351-1358 verbatim
private noncomputable def binarySourceDegreePaddedFieldComputable
    {field : List Bool → List Bool}
    (computer : BitTM field) :
    BitTM
      (binarySourceDegreePaddedFieldBits computer) :=
  maskDynamicGridRecordCatalogueComputable
    binarySourceFieldOperandDegreeWidth
    (factor400BinarySourceDegreePaddedBitComputable computer)


-- @@ L1360-1393 verbatim
private theorem factor400BinarySourceDegreePaddedFieldBits_eq
    {field : List Bool → List Bool}
    (computer : BitTM field)
    (input : List Bool) :
    binarySourceDegreePaddedFieldBits computer input =
      finiteWordBits
        (factor400BinarySourcePaddedWord
          (factor400BinarySourceLeftBits input).length (field input)) := by
  let degree := (factor400BinarySourceLeftBits input).length
  have hwidth :
      binarySourceFieldOperandDegreeWidth.output input =
        List.replicate degree true := by
    rfl
  unfold binarySourceDegreePaddedFieldBits
  rw [maskDynamicGridRecordCatalogueOutput_valid
    binarySourceFieldOperandDegreeWidth
    (factor400BinarySourceDegreePaddedBitComputable computer)
    input degree hwidth]
  simp_rw [factor400BinarySourceDegreePaddedBitWord_query]
  have hfin : List.range degree =
      (List.finRange degree).map (fun index => index.val) :=
    List.map_coe_finRange_eq_range.symm
  rw [hfin, List.flatMap_map]
  change
    (List.finRange degree).flatMap
      (fun index => [(field input).getD index.val false]) =
      (List.finRange degree).map
        (fun index => (field input).getD index.val false)
  calc
    _ = ((List.finRange degree).map
        (fun index => (field input).getD index.val false)).flatMap
          (fun bit => [bit]) := by
            rw [List.flatMap_map]
    _ = _ := List.flatMap_singleton' _


-- @@ L1395-1404 verbatim
private def binarySourceNormalizedFieldQuery
    (input : List Bool) : List Bool :=
  factor400BinarySourceFieldQuery
    (binarySourceDegreePaddedFieldBits
      binarySourceLowerBitsComputable input)
    (binarySourceDegreePaddedFieldBits
      binarySourceLeftBitsComputable input)
    (binarySourceDegreePaddedFieldBits
      binarySourceRightBitsComputable input)
    input


-- @@ L1406-1437 verbatim
private noncomputable def factor400BinarySourceNormalizedFieldQueryComputable :
    BitTM
      binarySourceNormalizedFieldQuery := by
  have hlower := GapCVP.TMComposition.computableInPolyTime
    (binarySourceDegreePaddedFieldComputable
      binarySourceLowerBitsComputable)
    structuralPrefixWriterComputable
  have hleft := GapCVP.TMComposition.computableInPolyTime
    (binarySourceDegreePaddedFieldComputable
      binarySourceLeftBitsComputable)
    structuralPrefixWriterComputable
  have hright := GapCVP.TMComposition.computableInPolyTime
    (binarySourceDegreePaddedFieldComputable
      binarySourceRightBitsComputable)
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hlower
    (pointwiseAppendComputable hleft
      (pointwiseAppendComputable hright
        (Turing.idComputableInPolyTime bitEncoding)))
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (binarySourceDegreePaddedFieldBits
            binarySourceLowerBitsComputable input) ++
        lengthPrefixedWord
          (binarySourceDegreePaddedFieldBits
            binarySourceLeftBitsComputable input) ++
        lengthPrefixedWord
          (binarySourceDegreePaddedFieldBits
            binarySourceRightBitsComputable input) ++ input)
  simpa only [Function.comp_apply, id_eq, List.append_assoc]
    using hphysical


-- @@ L1439-1439 verbatim
end BinarySourceFieldMultiplicationTM


-- @@ L1441-1441 verbatim
namespace BinarySourceModularReductionFoldTM


-- @@ L1443-1443 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder

-- @@ L1444-1444 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.CLStructuralPrefixWriter

-- @@ L1445-1445 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L1446-1446 verbatim
open GapCVP.BinaryDimensionTM GapCVP.BinaryModularReductionTM

-- @@ L1447-1447 verbatim
open GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L1449-1452 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceModularReductionQuery
    (lower product source : List Bool) : List Bool :=
  lengthPrefixedWord lower ++ lengthPrefixedWord product ++ source


-- @@ L1454-1456 verbatim
private def binarySourceModularReductionLowerBits :
    List Bool → List Bool :=
  firstFieldContents


-- @@ L1458-1461 verbatim
private noncomputable def factor400BinarySourceModularReductionLowerBitsComputable :
    BitTM
      binarySourceModularReductionLowerBits :=
  firstFieldContentsComputable


-- @@ L1463-1465 verbatim
private def binarySourceModularReductionProductBits :
    List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix


-- @@ L1467-1471 verbatim
private noncomputable def factor400BinarySourceModularReductionProductBitsComputable :
    BitTM
      binarySourceModularReductionProductBits :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L1473-1475 verbatim
private def binarySourceModularReductionOriginalSource :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L1477-1481 verbatim
private noncomputable def factor400BinarySourceModularReductionOriginalSourceComputable :
    BitTM
      binarySourceModularReductionOriginalSource :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable


-- @@ L1483-1490 verbatim
@[simp] private theorem factor400BinarySourceModularReductionLowerBits_query
    (lower product source : List Bool) :
    binarySourceModularReductionLowerBits
      (binarySourceModularReductionQuery lower product source) =
      lower := by
  simp only [binarySourceModularReductionLowerBits,
    binarySourceModularReductionQuery,
    List.append_assoc, firstFieldContents_valid]


-- @@ L1492-1499 verbatim
@[simp] private theorem factor400BinarySourceModularReductionProductBits_query
    (lower product source : List Bool) :
    binarySourceModularReductionProductBits
      (binarySourceModularReductionQuery lower product source) =
      product := by
  simp only [binarySourceModularReductionProductBits,
    Function.comp_apply, binarySourceModularReductionQuery,
    List.append_assoc, firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L1501-1508 verbatim
@[simp] private theorem factor400BinarySourceModularReductionOriginalSource_query
    (lower product source : List Bool) :
    binarySourceModularReductionOriginalSource
      (binarySourceModularReductionQuery lower product source) =
      source := by
  simp only [binarySourceModularReductionOriginalSource,
    Function.comp_apply, binarySourceModularReductionQuery,
    List.append_assoc, firstFieldSuffix_valid]


-- @@ L1510-1514 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceModularReductionDegreeUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    binarySourceModularReductionLowerBits


-- @@ L1516-1522 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularReductionDegreeUnaryComputable :
    BitTM
      binarySourceModularReductionDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularReductionLowerBitsComputable
    sourceInputLengthUnaryComputable


-- @@ L1524-1537 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularReductionDegreeUnary_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (product source : List Bool) :
    binarySourceModularReductionDegreeUnary
      (binarySourceModularReductionQuery
        (finiteWordBits lower) product source) =
      List.replicate degree true := by
  simp only [binarySourceModularReductionDegreeUnary,
    Function.comp_apply,
    factor400BinarySourceModularReductionLowerBits_query,
    sourceInputLengthUnary,
    factor400BinaryFiniteWordBits_length]


-- @@ L1539-1542 verbatim
private def factor400BinarySourceModularReductionPrefixedLower :
    List Bool → List Bool :=
  (fun word : List Bool => lengthPrefixedWord word) ∘
    binarySourceModularReductionLowerBits


-- @@ L1544-1549 verbatim
private noncomputable def factor400BinarySourceModularReductionPrefixedLowerComputable :
    BitTM
      factor400BinarySourceModularReductionPrefixedLower :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularReductionLowerBitsComputable
    structuralPrefixWriterComputable


-- @@ L1551-1554 verbatim
private def factor400BinarySourceModularReductionPrefixedProduct :
    List Bool → List Bool :=
  (fun word : List Bool => lengthPrefixedWord word) ∘
    binarySourceModularReductionProductBits


-- @@ L1556-1561 verbatim
private noncomputable def factor400BinarySourceModularReductionPrefixedProductComputable :
    BitTM
      factor400BinarySourceModularReductionPrefixedProduct :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularReductionProductBitsComputable
    structuralPrefixWriterComputable


-- @@ L1563-1568 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularReductionInitialState
    (lower product source : List Bool) : List Bool :=
  lengthPrefixedWord [] ++
    (lengthPrefixedWord lower ++
      (lengthPrefixedWord product ++ source))


-- @@ L1570-1575 verbatim
private def binarySourceModularReductionSeed
    (input : List Bool) : List Bool :=
  lengthPrefixedWord [] ++
    (factor400BinarySourceModularReductionPrefixedLower input ++
      (factor400BinarySourceModularReductionPrefixedProduct input ++
        binarySourceModularReductionOriginalSource input))


-- @@ L1577-1586 verbatim
private noncomputable def factor400BinarySourceModularReductionSeedComputable :
    BitTM
      binarySourceModularReductionSeed :=
  pointwiseAppendComputable
    (sourceFixedWordComputable (lengthPrefixedWord []))
    (pointwiseAppendComputable
      factor400BinarySourceModularReductionPrefixedLowerComputable
      (pointwiseAppendComputable
        factor400BinarySourceModularReductionPrefixedProductComputable
        factor400BinarySourceModularReductionOriginalSourceComputable))


-- @@ L1588-1601 verbatim
@[simp] private theorem factor400BinarySourceModularReductionSeed_query
    (lower product source : List Bool) :
    binarySourceModularReductionSeed
      (binarySourceModularReductionQuery lower product source) =
      binarySourceModularReductionInitialState
        lower product source := by
  simp only [binarySourceModularReductionSeed,
    factor400BinarySourceModularReductionPrefixedLower,
    factor400BinarySourceModularReductionPrefixedProduct,
    Function.comp_apply,
    factor400BinarySourceModularReductionLowerBits_query,
    factor400BinarySourceModularReductionProductBits_query,
    factor400BinarySourceModularReductionOriginalSource_query,
    binarySourceModularReductionInitialState]


-- @@ L1603-1607 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceModularReductionFoldPreparation
    (input : List Bool) : List Bool :=
  binarySourceModularReductionDegreeUnary input ++ false ::
    binarySourceModularReductionSeed input


-- @@ L1609-1617 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularReductionFoldPreparationComputable :
    BitTM
      binarySourceModularReductionFoldPreparation :=
  pointwiseAppendComputable
    factor400BinarySourceModularReductionDegreeUnaryComputable
    (GapCVP.TMComposition.computableInPolyTime
      factor400BinarySourceModularReductionSeedComputable
      (prependBitComputable false))


-- @@ L1619-1634 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularReductionFoldPreparation_valid
    {degree : ℕ}
    (lower : GapCVP.Core.EffectiveBinaryField.Word degree)
    (product : GapCVP.Core.EffectiveBinaryField.Word (2 * degree))
    (source : List Bool) :
    binarySourceModularReductionFoldPreparation
      (binarySourceModularReductionQuery
        (finiteWordBits lower) (finiteWordBits product) source) =
      unaryBoundedFoldWord degree
        (binarySourceModularReductionInitialState
          (finiteWordBits lower) (finiteWordBits product) source) := by
  rw [binarySourceModularReductionFoldPreparation,
    factor400BinarySourceModularReductionDegreeUnary_valid,
    factor400BinarySourceModularReductionSeed_query]
  rfl


-- @@ L1636-1636 verbatim
end BinarySourceModularReductionFoldTM


-- @@ L1638-1638 verbatim
namespace BinarySourceFieldMultiplicationTM


-- @@ L1640-1640 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.CLStructuralPrefixWriter

-- @@ L1641-1641 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryModularReductionTM

-- @@ L1642-1642 verbatim
open GapCVP.BinarySourceConvolutionTM GapCVP.BinarySourceConvolutionCorrectness

-- @@ L1643-1643 verbatim
open GapCVP.BinarySourceModularReductionFoldTM


-- @@ L1645-1653 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceProductReductionQuery
    (input : List Bool) : List Bool :=
  binarySourceModularReductionQuery
    (binarySourceDegreePaddedFieldBits
      binarySourceLowerBitsComputable input)
    (binarySourceRawConvolutionWord
      (binarySourceNormalizedFieldQuery input))
    input


-- @@ L1655-1680 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceProductReductionQueryComputable :
    BitTM
      binarySourceProductReductionQuery := by
  have hlower := GapCVP.TMComposition.computableInPolyTime
    (binarySourceDegreePaddedFieldComputable
      binarySourceLowerBitsComputable)
    structuralPrefixWriterComputable
  have hproduct := GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      factor400BinarySourceNormalizedFieldQueryComputable
      factor400BinarySourceRawConvolutionComputable)
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hlower
    (pointwiseAppendComputable hproduct
      (Turing.idComputableInPolyTime bitEncoding))
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (binarySourceDegreePaddedFieldBits
            binarySourceLowerBitsComputable input) ++
        lengthPrefixedWord
          (binarySourceRawConvolutionWord
            (binarySourceNormalizedFieldQuery input)) ++ input)
  simpa only [Function.comp_apply, id_eq, List.append_assoc]
    using hphysical


-- @@ L1682-1703 verbatim
@[simp] private theorem factor400BinarySourceDegreePaddedLowerBits_query
    (lower left right source : List Bool) :
    binarySourceDegreePaddedFieldBits
        binarySourceLowerBitsComputable
        (factor400BinarySourceFieldQuery lower left right source) =
      finiteWordBits
        (factor400BinarySourcePaddedWord left.length lower) := by
  calc
    _ = finiteWordBits
        (factor400BinarySourcePaddedWord
          (factor400BinarySourceLeftBits
            (factor400BinarySourceFieldQuery
              lower left right source)).length
          (factor400BinarySourceLowerBits
            (factor400BinarySourceFieldQuery
              lower left right source))) :=
      factor400BinarySourceDegreePaddedFieldBits_eq
        binarySourceLowerBitsComputable
        (factor400BinarySourceFieldQuery lower left right source)
    _ = _ := by
      rw [factor400BinarySourceLeftBits_query,
        factor400BinarySourceLowerBits_query]


-- @@ L1705-1725 verbatim
@[simp] private theorem factor400BinarySourceDegreePaddedLeftBits_query
    (lower left right source : List Bool) :
    binarySourceDegreePaddedFieldBits
        binarySourceLeftBitsComputable
        (factor400BinarySourceFieldQuery lower left right source) =
      finiteWordBits
        (factor400BinarySourcePaddedWord left.length left) := by
  calc
    _ = finiteWordBits
        (factor400BinarySourcePaddedWord
          (factor400BinarySourceLeftBits
            (factor400BinarySourceFieldQuery
              lower left right source)).length
          (factor400BinarySourceLeftBits
            (factor400BinarySourceFieldQuery
              lower left right source))) :=
      factor400BinarySourceDegreePaddedFieldBits_eq
        binarySourceLeftBitsComputable
        (factor400BinarySourceFieldQuery lower left right source)
    _ = _ := by
      rw [factor400BinarySourceLeftBits_query]


-- @@ L1727-1748 verbatim
@[simp] private theorem factor400BinarySourceDegreePaddedRightBits_query
    (lower left right source : List Bool) :
    binarySourceDegreePaddedFieldBits
        binarySourceRightBitsComputable
        (factor400BinarySourceFieldQuery lower left right source) =
      finiteWordBits
        (factor400BinarySourcePaddedWord left.length right) := by
  calc
    _ = finiteWordBits
        (factor400BinarySourcePaddedWord
          (factor400BinarySourceLeftBits
            (factor400BinarySourceFieldQuery
              lower left right source)).length
          (factor400BinarySourceRightBits
            (factor400BinarySourceFieldQuery
              lower left right source))) :=
      factor400BinarySourceDegreePaddedFieldBits_eq
        binarySourceRightBitsComputable
        (factor400BinarySourceFieldQuery lower left right source)
    _ = _ := by
      rw [factor400BinarySourceLeftBits_query,
        factor400BinarySourceRightBits_query]


-- @@ L1750-1765 verbatim
private theorem factor400BinarySourceNormalizedFieldQuery_query
    (lower left right source : List Bool) :
    binarySourceNormalizedFieldQuery
        (factor400BinarySourceFieldQuery lower left right source) =
      factor400BinarySourceFieldQuery
        (finiteWordBits
          (factor400BinarySourcePaddedWord left.length lower))
        (finiteWordBits
          (factor400BinarySourcePaddedWord left.length left))
        (finiteWordBits
          (factor400BinarySourcePaddedWord left.length right))
        (factor400BinarySourceFieldQuery lower left right source) := by
  unfold binarySourceNormalizedFieldQuery
  rw [factor400BinarySourceDegreePaddedLowerBits_query,
    factor400BinarySourceDegreePaddedLeftBits_query,
    factor400BinarySourceDegreePaddedRightBits_query]


-- @@ L1767-1777 verbatim
private theorem factor400BinarySourceNormalizedRawConvolution_query
    (lower left right source : List Bool) :
    binarySourceRawConvolutionWord
        (binarySourceNormalizedFieldQuery
          (factor400BinarySourceFieldQuery lower left right source)) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyWords
          (factor400BinarySourcePaddedWord left.length left)
          (factor400BinarySourcePaddedWord left.length right)) := by
  rw [factor400BinarySourceNormalizedFieldQuery_query,
    factor400BinarySourceRawConvolutionWord_valid]


-- @@ L1779-1794 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
theorem factor400BinarySourceProductReductionQuery_query
    (lower left right source : List Bool) :
    binarySourceProductReductionQuery
        (factor400BinarySourceFieldQuery lower left right source) =
      binarySourceModularReductionQuery
        (finiteWordBits
          (factor400BinarySourcePaddedWord left.length lower))
        (finiteWordBits
          (GapCVP.Core.EffectiveBinaryField.multiplyWords
            (factor400BinarySourcePaddedWord left.length left)
            (factor400BinarySourcePaddedWord left.length right)))
        (factor400BinarySourceFieldQuery lower left right source) := by
  unfold binarySourceProductReductionQuery
  rw [factor400BinarySourceDegreePaddedLowerBits_query,
    factor400BinarySourceNormalizedRawConvolution_query]


-- @@ L1796-1796 verbatim
end BinarySourceFieldMultiplicationTM


-- @@ L1798-1798 verbatim
namespace BinarySourceModularDegreeStepTM


-- @@ L1800-1800 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder

-- @@ L1801-1801 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L1802-1802 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L1803-1803 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L1804-1804 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM

-- @@ L1805-1805 verbatim
open GapCVP.BinarySourceConvolutionTM GapCVP.BinaryModularReductionTM


-- @@ L1807-1812 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularDegreeState
    (offset : ℕ) (lower current source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate offset true) ++
    lengthPrefixedWord lower ++
      lengthPrefixedWord current ++ source


-- @@ L1814-1816 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularOffsetUnary : List Bool → List Bool :=
  firstFieldContents


-- @@ L1818-1822 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularOffsetUnaryComputable :
    BitTM
      binarySourceModularOffsetUnary :=
  firstFieldContentsComputable


-- @@ L1824-1826 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularLowerWord : List Bool → List Bool :=
  firstFieldContents ∘ factor400BinarySourceSkipFields 1


-- @@ L1828-1834 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularLowerWordComputable :
    BitTM
      binarySourceModularLowerWord :=
  GapCVP.TMComposition.computableInPolyTime
    (binarySourceSkipFieldsComputable 1)
    firstFieldContentsComputable


-- @@ L1836-1838 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularCurrentWord : List Bool → List Bool :=
  firstFieldContents ∘ factor400BinarySourceSkipFields 2


-- @@ L1840-1846 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularCurrentWordComputable :
    BitTM
      binarySourceModularCurrentWord :=
  GapCVP.TMComposition.computableInPolyTime
    (binarySourceSkipFieldsComputable 2)
    firstFieldContentsComputable


-- @@ L1848-1850 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularOriginalSource : List Bool → List Bool :=
  factor400BinarySourceSkipFields 3


-- @@ L1852-1856 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularOriginalSourceComputable :
    BitTM
      binarySourceModularOriginalSource :=
  binarySourceSkipFieldsComputable 3


-- @@ L1858-1865 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularOffsetUnary_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularOffsetUnary
      (binarySourceModularDegreeState offset lower current source) =
      List.replicate offset true := by
  simp only [binarySourceModularOffsetUnary, binarySourceModularDegreeState, List.append_assoc,
      firstFieldContents_valid]


-- @@ L1867-1876 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularLowerWord_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularLowerWord
      (binarySourceModularDegreeState offset lower current source) =
      lower := by
  simp only [binarySourceModularLowerWord, factor400BinarySourceSkipFields, CompTriple.comp_eq,
      binarySourceModularDegreeState, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid,
      firstFieldContents_valid]


-- @@ L1878-1887 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularCurrentWord_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularCurrentWord
      (binarySourceModularDegreeState offset lower current source) =
      current := by
  simp only [binarySourceModularCurrentWord, factor400BinarySourceSkipFields, CompTriple.comp_eq,
      binarySourceModularDegreeState, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid,
      firstFieldContents_valid]


-- @@ L1889-1898 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularOriginalSource_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularOriginalSource
      (binarySourceModularDegreeState offset lower current source) =
      source := by
  simp only [binarySourceModularOriginalSource, factor400BinarySourceSkipFields,
      CompTriple.comp_eq,
      binarySourceModularDegreeState, List.append_assoc, Function.comp_apply,
          firstFieldSuffix_valid]


-- @@ L1900-1903 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceModularLowerDegreeUnary
    (input : List Bool) : List Bool :=
  sourceInputLengthUnary (binarySourceModularLowerWord input)


-- @@ L1905-1910 verbatim
private noncomputable def factor400BinarySourceModularLowerDegreeUnaryComputable :
    BitTM
      binarySourceModularLowerDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularLowerWordComputable
    sourceInputLengthUnaryComputable


-- @@ L1912-1915 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularCurrentWidthUnary
    (input : List Bool) : List Bool :=
  sourceInputLengthUnary (binarySourceModularCurrentWord input)


-- @@ L1917-1923 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularCurrentWidthUnaryComputable :
    BitTM
      binarySourceModularCurrentWidthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularCurrentWordComputable
    sourceInputLengthUnaryComputable


-- @@ L1925-1927 verbatim
private def binarySourceModularLastDegreeUnary
    (input : List Bool) : List Bool :=
  (binarySourceModularCurrentWidthUnary input).tail


-- @@ L1929-1934 verbatim
private noncomputable def factor400BinarySourceModularLastDegreeUnaryComputable :
    BitTM
      binarySourceModularLastDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceModularCurrentWidthUnaryComputable
    dropHeadComputable


-- @@ L1936-1941 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
def binarySourceModularDescendingDegreeUnary :
    List Bool → List Bool :=
  unarySubtractionOutput
    binarySourceModularLastDegreeUnary
    binarySourceModularOffsetUnary


-- @@ L1943-1949 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularDescendingDegreeUnaryComputable :
    BitTM
      binarySourceModularDescendingDegreeUnary :=
  unarySubtractionComputable
    factor400BinarySourceModularLastDegreeUnaryComputable
    factor400BinarySourceModularOffsetUnaryComputable


-- @@ L1951-1955 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularShiftStartUnary : List Bool → List Bool :=
  unarySubtractionOutput
    binarySourceModularDescendingDegreeUnary
    binarySourceModularLowerDegreeUnary


-- @@ L1957-1963 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularShiftStartUnaryComputable :
    BitTM
      binarySourceModularShiftStartUnary :=
  unarySubtractionComputable
    factor400BinarySourceModularDescendingDegreeUnaryComputable
    factor400BinarySourceModularLowerDegreeUnaryComputable


-- @@ L1965-1969 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[expose] def binarySourceModularLeadingGate : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    binarySourceModularDescendingDegreeUnary
    binarySourceModularCurrentWord


-- @@ L1971-1977 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def factor400BinarySourceModularLeadingGateComputable :
    BitTM
      binarySourceModularLeadingGate :=
  fiveOriginalDynamicBitComputable
    factor400BinarySourceModularDescendingDegreeUnaryComputable
    factor400BinarySourceModularCurrentWordComputable


-- @@ L1979-1986 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularLowerDegreeUnary_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularLowerDegreeUnary
      (binarySourceModularDegreeState offset lower current source) =
      List.replicate lower.length true := by
  simp only [binarySourceModularLowerDegreeUnary, sourceInputLengthUnary,
      factor400BinarySourceModularLowerWord_state]


-- @@ L1988-2003 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
@[simp] theorem factor400BinarySourceModularDescendingDegreeUnary_state
    (offset : ℕ) (lower current source : List Bool) :
    binarySourceModularDescendingDegreeUnary
      (binarySourceModularDegreeState offset lower current source) =
      List.replicate (current.length - 1 - offset) true := by
  unfold binarySourceModularDescendingDegreeUnary
  apply unarySubtractionOutput_valid
    binarySourceModularLastDegreeUnary
    binarySourceModularOffsetUnary
    (binarySourceModularDegreeState offset lower current source)
    (current.length - 1) offset
  · simp only [binarySourceModularLastDegreeUnary, binarySourceModularCurrentWidthUnary,
      sourceInputLengthUnary,
        factor400BinarySourceModularCurrentWord_state, List.tail_replicate]
  · simp only [factor400BinarySourceModularOffsetUnary_state]


-- @@ L2005-2005 verbatim
end BinarySourceModularDegreeStepTM


-- @@ L2007-2007 verbatim
end GapCVP


-- @@ L2009-2009 verbatim
end
