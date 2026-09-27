/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part12


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 13 -/


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
namespace GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM


-- @@ L26-26 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L27-27 verbatim
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L28-28 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceStructuralTuringTM

-- @@ L29-29 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFCappedUnaryPairArithmeticTM

-- @@ L30-30 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

-- @@ L31-31 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L32-32 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows

-- @@ L33-33 verbatim
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.BinaryPhysicalWordQueryCatalogueTM

-- @@ L34-34 verbatim
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L35-35 verbatim
open GapCVP.GaussianAdaptivePhysicalStateCellTM

-- @@ L36-36 verbatim
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM

-- @@ L37-37 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnStateTM

-- @@ L38-38 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateTM


-- @@ L40-42 verbatim
private def gaussianPhysicalUpdatedRowsUnary : List Bool → List Bool :=
  gaussianDenseStateRowCountUnary ∘
    gaussianPhysicalColumnCurrentState


-- @@ L44-49 verbatim
private noncomputable def gaussianPhysicalUpdatedRowsUnaryComputable :
    BitTM
      gaussianPhysicalUpdatedRowsUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    gaussianDenseStateRowCountUnaryComputable


-- @@ L51-55 verbatim
private def gaussianPhysicalUpdatedCheckWidthOutput :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    gaussianPhysicalUpdatedRowsUnary
    gaussianPhysicalColumnPivotWidthOutput


-- @@ L57-62 verbatim
private noncomputable def gaussianPhysicalUpdatedCheckWidthComputable :
    BitTM
      gaussianPhysicalUpdatedCheckWidthOutput :=
  fourFamilyComputedUnaryProductComputable
    gaussianPhysicalUpdatedRowsUnaryComputable
    gaussianPhysicalColumnPivotWidthComputable


-- @@ L64-67 verbatim
private noncomputable def gaussianPhysicalUpdatedCheckWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalUpdatedCheckWidthOutput
  computer := gaussianPhysicalUpdatedCheckWidthComputable


-- @@ L69-72 verbatim
private noncomputable def gaussianPhysicalUpdatedRhsWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalUpdatedRowsUnary
  computer := gaussianPhysicalUpdatedRowsUnaryComputable


-- @@ L74-76 verbatim
private def gaussianPhysicalUpdatedRankDimension : List Bool → List Bool :=
  gaussianDenseStateDimensionUnary ∘
    gaussianPhysicalPivotRecordState


-- @@ L78-83 verbatim
private noncomputable def gaussianPhysicalUpdatedRankDimensionComputable :
    BitTM
      gaussianPhysicalUpdatedRankDimension :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordStateComputable
    gaussianDenseStateDimensionUnaryComputable


-- @@ L85-89 verbatim
private def gaussianPhysicalUpdatedRankDivisionInput
    (input : List Bool) : List Bool :=
  gaussianPhysicalPivotRecordRow input ++ false ::
    (gaussianPhysicalUpdatedRankDimension input ++ false ::
      gaussianPhysicalColumnPivotRecordOuter input)


-- @@ L91-108 verbatim
private noncomputable def gaussianPhysicalUpdatedRankDivisionInputComputable :
    BitTM
      gaussianPhysicalUpdatedRankDivisionInput := by
  have hsource := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnPivotRecordOuterComputable
    (prependBitComputable false)
  have hdimension := pointwiseAppendComputable
    gaussianPhysicalUpdatedRankDimensionComputable hsource
  have hseparator := GapCVP.TMComposition.computableInPolyTime
    hdimension (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    gaussianPhysicalPivotRecordRowComputable hseparator
  change BitTM
    (fun input =>
      gaussianPhysicalPivotRecordRow input ++ false ::
        (gaussianPhysicalUpdatedRankDimension input ++ false ::
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L110-113 verbatim
private def gaussianPhysicalUpdatedRankDivisionOutput :
    List Bool → List Bool :=
  sourceUnaryDivisionOutput ∘
    gaussianPhysicalUpdatedRankDivisionInput


-- @@ L115-120 verbatim
private noncomputable def gaussianPhysicalUpdatedRankDivisionComputable :
    BitTM
      gaussianPhysicalUpdatedRankDivisionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionInputComputable
    sourceUnaryDivisionComputable


-- @@ L122-125 verbatim
private def gaussianPhysicalUpdatedRankRow
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (gaussianPhysicalUpdatedRankDivisionOutput input)).tail


-- @@ L127-134 verbatim
private noncomputable def gaussianPhysicalUpdatedRankRowComputable :
    BitTM
      gaussianPhysicalUpdatedRankRow := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionComputable
    unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable


-- @@ L136-140 verbatim
private def gaussianPhysicalUpdatedRankColumn
    (input : List Bool) : List Bool :=
  (unaryPrefixOutput
    (unaryPrefixSuffixOutput
      (gaussianPhysicalUpdatedRankDivisionOutput input))).tail


-- @@ L142-151 verbatim
private noncomputable def gaussianPhysicalUpdatedRankColumnComputable :
    BitTM
      gaussianPhysicalUpdatedRankColumn := by
  have hsuffix := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankDivisionComputable
    actualUnaryPrefixSuffixComputable
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hsuffix unaryPrefixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hprefix dropHeadComputable


-- @@ L153-157 verbatim
private def gaussianPhysicalUpdatedCheckCellQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalUpdatedRankRow input) ++
    (lengthPrefixedWord (gaussianPhysicalUpdatedRankColumn input) ++
      gaussianPhysicalColumnPivotRecordOuter input)


-- @@ L159-176 verbatim
private noncomputable def gaussianPhysicalUpdatedCheckCellQueryComputable :
    BitTM
      gaussianPhysicalUpdatedCheckCellQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankRowComputable
    structuralPrefixWriterComputable
  have hcolumn := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRankColumnComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hrow
    (pointwiseAppendComputable hcolumn
      gaussianPhysicalColumnPivotRecordOuterComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalUpdatedRankRow input) ++
        (lengthPrefixedWord (gaussianPhysicalUpdatedRankColumn input) ++
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L178-181 verbatim
private def gaussianPhysicalUpdatedCheckRecordOutput :
    List Bool → List Bool :=
  gaussianPhysicalColumnUpdatedCheckWord ∘
    gaussianPhysicalUpdatedCheckCellQuery


-- @@ L183-188 verbatim
private noncomputable def gaussianPhysicalUpdatedCheckRecordComputable :
    BitTM
      gaussianPhysicalUpdatedCheckRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedCheckCellQueryComputable
    gaussianPhysicalColumnUpdatedCheckComputable


-- @@ L190-194 verbatim
private def gaussianPhysicalUpdatedRhsCellQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
    (lengthPrefixedWord [] ++
      gaussianPhysicalColumnPivotRecordOuter input)


-- @@ L196-212 verbatim
private noncomputable def gaussianPhysicalUpdatedRhsCellQueryComputable :
    BitTM
      gaussianPhysicalUpdatedRhsCellQuery := by
  have hrow := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordRowComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrow
    (pointwiseAppendComputable hzero
      gaussianPhysicalColumnPivotRecordOuterComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalColumnPivotRecordOuter input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L214-217 verbatim
private def gaussianPhysicalUpdatedRhsRecordOutput :
    List Bool → List Bool :=
  gaussianPhysicalColumnUpdatedRhsWord ∘
    gaussianPhysicalUpdatedRhsCellQuery


-- @@ L219-224 verbatim
private noncomputable def gaussianPhysicalUpdatedRhsRecordComputable :
    BitTM
      gaussianPhysicalUpdatedRhsRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRhsCellQueryComputable
    gaussianPhysicalColumnUpdatedRhsComputable


-- @@ L226-230 verbatim
private def gaussianPhysicalUpdatedCheckBitsOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable


-- @@ L232-237 verbatim
private noncomputable def gaussianPhysicalUpdatedCheckBitsComputable :
    BitTM
      gaussianPhysicalUpdatedCheckBitsOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable


-- @@ L239-243 verbatim
private def gaussianPhysicalUpdatedRhsBitsOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable


-- @@ L245-250 verbatim
private noncomputable def gaussianPhysicalUpdatedRhsBitsComputable :
    BitTM
      gaussianPhysicalUpdatedRhsBitsOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable


-- @@ L252-262 verbatim
@[simp] private theorem gaussianPhysicalUpdatedRowsUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRowsUnary
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  unfold gaussianPhysicalUpdatedRowsUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnCurrentState_query,
    gaussianDenseStateRowCountUnary_effective]


-- @@ L264-281 verbatim
private theorem gaussianPhysicalUpdatedCheckWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (m * n) true := by
  apply fourFamilyComputedUnaryProductOutput_valid
    gaussianPhysicalUpdatedRowsUnary
    gaussianPhysicalColumnPivotWidthOutput
    (gaussianPhysicalPivotColumnQuery active.val
      (effectiveGaussianPackedStateWord state source)) m n
  · exact gaussianPhysicalUpdatedRowsUnary_effective
      state source active
  · simpa only [gaussianPhysicalColumnPivotWidth_output] using
      gaussianPhysicalColumnPivotWidth_effective
        state source active hrows


-- @@ L283-291 verbatim
private theorem gaussianPhysicalUpdatedRhsWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRhsWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate m true := by
  exact gaussianPhysicalUpdatedRowsUnary_effective
    state source active


-- @@ L293-305 verbatim
private theorem gaussianPhysicalUpdatedRankDimension_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDimension
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate n true := by
  unfold gaussianPhysicalUpdatedRankDimension
  rw [Function.comp_apply,
    gaussianPhysicalPivotRecordState_word]
  exact gaussianDenseStateDimensionUnary_effective
    state source hrows


-- @@ L307-322 verbatim
private theorem gaussianPhysicalUpdatedRankDivisionInput_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDivisionInput
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      sourceUnaryDivisionQuery rank n
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) := by
  unfold gaussianPhysicalUpdatedRankDivisionInput
  rw [gaussianPhysicalPivotRecordRow_word,
    gaussianPhysicalUpdatedRankDimension_word
      state source active rank width hrows,
    gaussianPhysicalColumnPivotRecordOuter_word]
  rfl


-- @@ L324-344 verbatim
private theorem gaussianPhysicalUpdatedRankDivisionOutput_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankDivisionOutput
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank / n) true ++ false ::
        (List.replicate (rank % n) true ++ false ::
          sourceUnaryDivisionQuery rank n
            (gaussianPhysicalPivotColumnQuery active.val
              (effectiveGaussianPackedStateWord state source))) := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  unfold gaussianPhysicalUpdatedRankDivisionOutput
  rw [Function.comp_apply,
    gaussianPhysicalUpdatedRankDivisionInput_word
      state source active rank width hrows,
    sourceUnaryDivisionOutput_valid rank n
      (gaussianPhysicalPivotColumnQuery active.val
        (effectiveGaussianPackedStateWord state source)) hn]


-- @@ L346-358 verbatim
private theorem gaussianPhysicalUpdatedRankRow_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankRow
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank / n) true := by
  unfold gaussianPhysicalUpdatedRankRow
  rw [gaussianPhysicalUpdatedRankDivisionOutput_word
    state source active rank width hrows,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L360-373 verbatim
private theorem gaussianPhysicalUpdatedRankColumn_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedRankColumn
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (rank % n) true := by
  unfold gaussianPhysicalUpdatedRankColumn
  rw [gaussianPhysicalUpdatedRankDivisionOutput_word
    state source active rank width hrows,
    unaryPrefixSuffixOutput_valid,
    unaryPrefixOutput_replicate_delimiter]
  rfl


-- @@ L375-393 verbatim
private theorem gaussianPhysicalUpdatedCheckCellQuery_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckCellQuery
        (gaussianPhysicalPivotRecordWord rank width active.val
          (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalColumnCellQuery
        (rank / n) (rank % n) active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold gaussianPhysicalUpdatedCheckCellQuery
    gaussianPhysicalColumnCellQuery
    affineCellQuery
  rw [gaussianPhysicalUpdatedRankRow_word
    state source active rank width hrows,
    gaussianPhysicalUpdatedRankColumn_word
      state source active rank width hrows,
    gaussianPhysicalColumnPivotRecordOuter_word]
  simp only [List.append_assoc]


-- @@ L395-409 verbatim
private theorem gaussianPhysicalUpdatedRhsCellQuery_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row width : ℕ) :
    gaussianPhysicalUpdatedRhsCellQuery
        (gaussianPhysicalPivotRecordWord row width active.val
          (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalColumnCellQuery row 0 active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold gaussianPhysicalUpdatedRhsCellQuery
    gaussianPhysicalColumnCellQuery
    affineCellQuery
  rw [gaussianPhysicalPivotRecordRow_word,
    gaussianPhysicalColumnPivotRecordOuter_word]
  simp only [List.append_assoc, List.replicate_zero]


-- @@ L411-423 verbatim
private theorem gaussianPhysicalUpdatedCheckBitsOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalUpdatedCheckWidth.output input =
      List.replicate count true) :
    gaussianPhysicalUpdatedCheckBitsOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalUpdatedCheckRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalUpdatedCheckWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalUpdatedCheckWidth
    gaussianPhysicalUpdatedCheckRecordComputable input count hwidth


-- @@ L425-437 verbatim
private theorem gaussianPhysicalUpdatedRhsBitsOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalUpdatedRhsWidth.output input =
      List.replicate count true) :
    gaussianPhysicalUpdatedRhsBitsOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalUpdatedRhsRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalUpdatedRhsWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalUpdatedRhsWidth
    gaussianPhysicalUpdatedRhsRecordComputable input count hwidth


-- @@ L439-454 verbatim
private theorem gaussianPhysicalUpdatedCheckGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank : ℕ) (hrows : 0 < m) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalUpdatedCheckWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord rank (m * n) active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalUpdatedCheckWidth_effective
    state source active hrows]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]


-- @@ L456-471 verbatim
private theorem gaussianPhysicalUpdatedRhsGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : ℕ) :
    lengthPrefixedWord (List.replicate row true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalUpdatedRhsWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord row m active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalUpdatedRhsWidth_effective
    state source active]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]


-- @@ L473-501 verbatim
private theorem gaussianPhysicalUpdatedCheckRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : Fin m) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckRecordOutput
        (gaussianPhysicalPivotRecordWord
          (row.val * n + column.val) (m * n) active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((columnStep state active).system.check row column =
          (1 : ZMod 2))] := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  have hquotient :
      (row.val * n + column.val) / n = row.val := by
    simpa only [Nat.mul_comm, Nat.div_eq_of_lt column.isLt, add_zero] using Nat.mul_add_div hn
        row.val column.val
  have hremainder :
      (row.val * n + column.val) % n = column.val := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt column.isLt, zero_add]
  have hquery := gaussianPhysicalUpdatedCheckCellQuery_word
    state source active (row.val * n + column.val)
    (m * n) hrows
  rw [hquotient, hremainder] at hquery
  unfold gaussianPhysicalUpdatedCheckRecordOutput
  rw [Function.comp_apply, hquery]
  exact gaussianPhysicalColumnUpdatedCheckWord_effective
    state source row column active


-- @@ L503-520 verbatim
private theorem gaussianPhysicalUpdatedRhsRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (row : Fin m) :
    gaussianPhysicalUpdatedRhsRecordOutput
        (gaussianPhysicalPivotRecordWord row.val m active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((columnStep state active).system.rhs row =
          (1 : ZMod 2))] := by
  have hn : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le active.val) active.isLt
  let zero : Fin n := ⟨0, hn⟩
  unfold gaussianPhysicalUpdatedRhsRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalUpdatedRhsCellQuery_word]
  exact gaussianPhysicalColumnUpdatedRhsWord_effective
    state source row zero active


-- @@ L522-588 verbatim
private theorem gaussianPhysicalUpdatedCheckBitsOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalUpdatedCheckBitsOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedCheckBits
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalUpdatedCheckWidth.output input =
      List.replicate (m * n) true :=
    gaussianPhysicalUpdatedCheckWidth_effective
      state source active hrows
  have hcatalogue := gaussianPhysicalUpdatedCheckBitsOutput_valid
    input (m * n) hwidth
  calc
    gaussianPhysicalUpdatedCheckBitsOutput input =
        (List.range (m * n)).flatMap (fun rank =>
          gaussianPhysicalUpdatedCheckRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalUpdatedCheckWidth input)) :=
      hcatalogue
    _ = (List.range (m * n)).flatMap (fun rank =>
          gaussianPhysicalUpdatedCheckRecordOutput
            (gaussianPhysicalPivotRecordWord rank (m * n)
              active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalUpdatedCheckRecordOutput
        (gaussianPhysicalUpdatedCheckGeneratedRecord_effective
          state source active rank hrows)
    _ = (List.range m).flatMap (fun row =>
          (List.range n).flatMap (fun column =>
            gaussianPhysicalUpdatedCheckRecordOutput
              (gaussianPhysicalPivotRecordWord
                (row * n + column) (m * n) active.val
                (effectiveGaussianPackedStateWord state source)))) := by
      rw [sourcePhysicalWordCanonical_range_mul_flatMap]
      simp only [List.flatMap_assoc, List.flatMap_map]
    _ = (List.finRange m).flatMap (fun row =>
          (List.finRange n).flatMap (fun column =>
            [decide
              ((columnStep state active).system.check row column =
                (1 : ZMod 2))])) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro column _
      exact gaussianPhysicalUpdatedCheckRecordOutput_effective
        state source active row column hrows
    _ = effectiveGaussianPackedCheckBits
          (columnStep state active) := by
      unfold effectiveGaussianPackedCheckBits
      apply List.flatMap_congr
      intro row _
      exact sourcePhysicalWordPackedFlatMap_singleton
        (List.finRange n)
        (fun column =>
          decide
            ((columnStep state active).system.check row column =
              (1 : ZMod 2)))


-- @@ L590-640 verbatim
private theorem gaussianPhysicalUpdatedRhsBitsOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedRhsBitsOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedRhsBits
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalUpdatedRhsWidth.output input =
      List.replicate m true :=
    gaussianPhysicalUpdatedRhsWidth_effective
      state source active
  have hcatalogue := gaussianPhysicalUpdatedRhsBitsOutput_valid
    input m hwidth
  calc
    gaussianPhysicalUpdatedRhsBitsOutput input =
        (List.range m).flatMap (fun row =>
          gaussianPhysicalUpdatedRhsRecordOutput
            (lengthPrefixedWord (List.replicate row true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalUpdatedRhsWidth input)) :=
      hcatalogue
    _ = (List.range m).flatMap (fun row =>
          gaussianPhysicalUpdatedRhsRecordOutput
            (gaussianPhysicalPivotRecordWord row m active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro row _
      exact congrArg gaussianPhysicalUpdatedRhsRecordOutput
        (gaussianPhysicalUpdatedRhsGeneratedRecord_effective
          state source active row)
    _ = (List.finRange m).flatMap (fun row =>
          [decide
            ((columnStep state active).system.rhs row =
              (1 : ZMod 2))]) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      exact gaussianPhysicalUpdatedRhsRecordOutput_effective
        state source active row
    _ = effectiveGaussianPackedRhsBits
          (columnStep state active) := by
      unfold effectiveGaussianPackedRhsBits
      exact sourcePhysicalWordPackedFlatMap_singleton
        (List.finRange m)
        (fun row =>
          decide
            ((columnStep state active).system.rhs row =
              (1 : ZMod 2)))


-- @@ L642-644 verbatim
private def gaussianPhysicalUpdatedOriginalSource : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ gaussianPhysicalColumnCurrentState


-- @@ L646-657 verbatim
private noncomputable def gaussianPhysicalUpdatedOriginalSourceComputable :
    BitTM
      gaussianPhysicalUpdatedOriginalSource := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hnext firstFieldSuffixComputable


-- @@ L659-669 verbatim
@[simp] private theorem gaussianPhysicalUpdatedOriginalSource_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n) :
    gaussianPhysicalUpdatedOriginalSource
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      source := by
  simp only [gaussianPhysicalUpdatedOriginalSource, gaussianPhysicalColumnCurrentState,
      gaussianPhysicalPivotColumnQuery, effectiveGaussianPackedStateWord, List.append_assoc,
          Function.comp_apply,
      firstFieldSuffix_valid]


-- @@ L671-679 verbatim
private def gaussianPhysicalColumnStateOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalUpdatedCheckBitsOutput input) ++
    lengthPrefixedWord (gaussianPhysicalUpdatedRhsBitsOutput input) ++
    lengthPrefixedWord
      (GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary input) ++
    lengthPrefixedWord
      (gaussianPhysicalColumnUpdatedPivotCatalogueOutput input) ++
    gaussianPhysicalUpdatedOriginalSource input


-- @@ L681-710 verbatim
private noncomputable def gaussianPhysicalColumnStateComputable :
    BitTM
      gaussianPhysicalColumnStateOutput := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedCheckBitsComputable
    structuralPrefixWriterComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalUpdatedRhsBitsComputable
    structuralPrefixWriterComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnaryComputable
    structuralPrefixWriterComputable
  have hpivots := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnUpdatedPivotCatalogueComputable
    structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hcheck
    (pointwiseAppendComputable hrhs
      (pointwiseAppendComputable hnext
        (pointwiseAppendComputable hpivots
          gaussianPhysicalUpdatedOriginalSourceComputable)))
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalUpdatedCheckBitsOutput input) ++
        lengthPrefixedWord (gaussianPhysicalUpdatedRhsBitsOutput input) ++
        lengthPrefixedWord
          (GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary input) ++
        lengthPrefixedWord
          (gaussianPhysicalColumnUpdatedPivotCatalogueOutput input) ++
        gaussianPhysicalUpdatedOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical


-- @@ L712-731 verbatim
private theorem gaussianPhysicalColumnStateOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnStateOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedStateWord
        (columnStep state active) source := by
  unfold gaussianPhysicalColumnStateOutput
  rw [gaussianPhysicalUpdatedCheckBitsOutput_effective
    state source active hrows,
    gaussianPhysicalUpdatedRhsBitsOutput_effective
      state source active,
    GaussianAdaptivePhysicalColumnStateTM.gaussianPhysicalColumnNextPivotUnary_effective
      state source active hrows,
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput_effective
      state source active hrows,
    gaussianPhysicalUpdatedOriginalSource_effective]
  rfl


-- @@ L733-733 verbatim
end GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM


-- @@ L735-735 verbatim
namespace GaussianAdaptivePhysicalInitialStateTM


-- @@ L737-737 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L738-738 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceStructuralTuringTM

-- @@ L739-739 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L740-740 verbatim
open GapCVP.SourceMixedRadixUnaryQuotientRemainderTM

-- @@ L741-741 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.BinaryDimensionTM

-- @@ L742-742 verbatim
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptiveEliminationCorrectness

-- @@ L743-743 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L744-744 verbatim
open GapCVP.GaussianAdaptivePhysicalStateCellTM


-- @@ L746-749 verbatim
private noncomputable def gaussianPhysicalInitialPivotWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianDenseStateDimensionUnary
  computer := gaussianDenseStateDimensionUnaryComputable


-- @@ L751-754 verbatim
private def gaussianPhysicalInitialPivotCatalogue : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable (lengthPrefixedWord [false]))


-- @@ L756-761 verbatim
private noncomputable def gaussianPhysicalInitialPivotCatalogueComputable :
    BitTM
      gaussianPhysicalInitialPivotCatalogue :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable (lengthPrefixedWord [false]))


-- @@ L763-770 verbatim
private def gaussianPhysicalPackedFullInitialStateOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPackedStateCheckBits input) ++
    lengthPrefixedWord (gaussianPackedStateRhsBits input) ++
    lengthPrefixedWord [] ++
    lengthPrefixedWord
      (gaussianPhysicalInitialPivotCatalogue input) ++
    gaussianPackedInitialOriginalSource input


-- @@ L772-799 verbatim
private noncomputable def gaussianPhysicalPackedFullInitialStateComputable :
    BitTM
      gaussianPhysicalPackedFullInitialStateOutput := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateCheckBitsComputable
    structuralPrefixWriterComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    gaussianPackedStateRhsBitsComputable
    structuralPrefixWriterComputable
  have hpivot := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalInitialPivotCatalogueComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hcheck
    (pointwiseAppendComputable hrhs
      (pointwiseAppendComputable hzero
        (pointwiseAppendComputable hpivot
          gaussianPackedInitialOriginalSourceComputable)))
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPackedStateCheckBits input) ++
        lengthPrefixedWord (gaussianPackedStateRhsBits input) ++
        lengthPrefixedWord [] ++
        lengthPrefixedWord
          (gaussianPhysicalInitialPivotCatalogue input) ++
        gaussianPackedInitialOriginalSource input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical


-- @@ L801-813 verbatim
private theorem gaussianDenseStateCheckLengthUnary_matrixWord
    (checks rhs source : List Bool) :
    gaussianDenseStateCheckLengthUnary
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) =
      List.replicate checks.length true := by
  change
    sourceInputLengthUnary
      (gaussianPackedStateCheckBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source)) = _
  rw [gaussianPackedStateCheckBits_matrixWord]
  rfl


-- @@ L815-827 verbatim
private theorem gaussianDenseStateRowCountUnary_matrixWord
    (checks rhs source : List Bool) :
    gaussianDenseStateRowCountUnary
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source) =
      List.replicate rhs.length true := by
  change
    sourceInputLengthUnary
      (gaussianPackedStateRhsBits
        (lengthPrefixedWord checks ++
          lengthPrefixedWord rhs ++ source)) = _
  rw [gaussianPackedStateRhsBits_matrixWord]
  rfl


-- @@ L829-861 verbatim
private theorem gaussianDenseStateDimensionUnary_matrixWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianDenseStateDimensionUnary
        (lengthPrefixedWord (effectiveGaussianPackedCheckBits state) ++
          lengthPrefixedWord (effectiveGaussianPackedRhsBits state) ++
          source) =
      List.replicate n true := by
  let word :=
    lengthPrefixedWord (effectiveGaussianPackedCheckBits state) ++
      lengthPrefixedWord (effectiveGaussianPackedRhsBits state) ++
      source
  have hcheck : gaussianDenseStateCheckLengthUnary word =
      List.replicate (m * n) true := by
    dsimp [word]
    rw [gaussianDenseStateCheckLengthUnary_matrixWord,
      effectiveGaussianPackedCheckBits_length]
  have hrhs : gaussianDenseStateRowCountUnary word =
      List.replicate m true := by
    dsimp [word]
    rw [gaussianDenseStateRowCountUnary_matrixWord,
      effectiveGaussianPackedRhsBits_length]
  have hquery : gaussianDenseStateDimensionDivisionQuery word =
      sourceUnaryDivisionQuery (m * n) m word := by
    simp only [gaussianDenseStateDimensionDivisionQuery, hcheck, hrhs, sourceUnaryDivisionQuery]
  change gaussianDenseStateDimensionUnary word = _
  unfold gaussianDenseStateDimensionUnary
  simp only [Function.comp_apply]
  rw [hquery, sourceUnaryDivisionOutput_valid
    (m * n) m word hrows]
  rw [unaryPrefixOutput_replicate_delimiter]
  simp only [List.tail_cons]
  rw [Nat.mul_div_cancel_left n hrows]


-- @@ L863-886 verbatim
private theorem gaussianPhysicalInitialPivotCatalogue_valid
    (input : List Bool) (dimension : ℕ)
    (hdimension : gaussianDenseStateDimensionUnary input =
      List.replicate dimension true) :
    gaussianPhysicalInitialPivotCatalogue input =
      binaryGaussianPivotBatchStream
        (List.replicate dimension [false]) := by
  change
    maskDynamicGridRecordCatalogueOutput
      gaussianPhysicalInitialPivotWidth
      (sourceFixedWordComputable
        (lengthPrefixedWord [false])) input = _
  rw [maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalInitialPivotWidth
    (sourceFixedWordComputable
      (lengthPrefixedWord [false]))
    input dimension hdimension]
  change
    (List.range dimension).flatMap
        (fun _ => lengthPrefixedWord [false]) =
      (List.replicate dimension [false]).flatMap
        lengthPrefixedWord
  rw [← List.flatMap_map]
  simp only [List.map_const', List.length_range]


-- @@ L888-926 verbatim
private theorem gaussianPhysicalPackedFullInitialStateOutput_effective
    (system : BinaryAffineSystem)
    (source : List Bool) (hrows : 0 < system.rowCount) :
    gaussianPhysicalPackedFullInitialStateOutput
        (lengthPrefixedWord
          (sourcePhysicalWordPackedCheckBits system) ++
          lengthPrefixedWord
            (sourcePhysicalWordPackedRhsBits system) ++ source) =
      effectiveGaussianPackedStateWord
        (initialState system.effectiveGaussianSystem) source := by
  let initial := initialState system.effectiveGaussianSystem
  let word :=
    lengthPrefixedWord
      (sourcePhysicalWordPackedCheckBits system) ++
      lengthPrefixedWord
        (sourcePhysicalWordPackedRhsBits system) ++ source
  have hcheck : sourcePhysicalWordPackedCheckBits system =
      effectiveGaussianPackedCheckBits initial :=
    sourcePhysicalWordPackedCheckBits_eq_effective_initial system
  have hrhs : sourcePhysicalWordPackedRhsBits system =
      effectiveGaussianPackedRhsBits initial :=
    sourcePhysicalWordPackedRhsBits_eq_effective_initial system
  have hdimension : gaussianDenseStateDimensionUnary word =
      List.replicate system.dimension true := by
    dsimp [word]
    rw [hcheck, hrhs]
    exact gaussianDenseStateDimensionUnary_matrixWord_effective
      initial source hrows
  have hpivots := gaussianPhysicalInitialPivotCatalogue_valid
    word system.dimension hdimension
  change gaussianPhysicalPackedFullInitialStateOutput word = _
  unfold gaussianPhysicalPackedFullInitialStateOutput
    effectiveGaussianPackedStateWord
  rw [gaussianPackedStateCheckBits_matrixWord,
    gaussianPackedStateRhsBits_matrixWord,
    gaussianPackedInitialOriginalSource_matrixWord,
    hpivots, effectiveGaussianPackedPivotCatalogue_initial]
  rw [hcheck, hrhs]
  rfl


-- @@ L928-928 verbatim
end GaussianAdaptivePhysicalInitialStateTM


-- @@ L930-930 verbatim
namespace GaussianAdaptivePhysicalColumnIterationBoundTM


-- @@ L932-932 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert

-- @@ L933-933 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputBoundedDependentRecordFold

-- @@ L934-934 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L935-935 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.CLStructuralPrefixWriter

-- @@ L936-936 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFBoundedRecordFoldTM

-- @@ L937-937 verbatim
open GapCVP.CNFAnnotatedSourceClauseBubblePassTM GapCVP.BinaryDimensionTM

-- @@ L938-938 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalStateCellTM

-- @@ L939-939 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnStateTM

-- @@ L940-940 verbatim
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM

-- @@ L941-941 verbatim
open GapCVP.GaussianAdaptivePhysicalInitialStateTM


-- @@ L943-946 verbatim
/-- Encode the column iteration budget as a unary word. -/
def gaussianPhysicalColumnIterationBudgetWord
    (packed : List Bool) : List Bool :=
  List.replicate (64 * (packed.length + 1) ^ 2) true


-- @@ L948-960 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationBudgetWordComputable :
    BitTM
      gaussianPhysicalColumnIterationBudgetWord := by
  have hphysical := polynomialValueUnaryComputable
    (64 * (Polynomial.X + 1) ^ 2)
  change BitTM
    (fun packed : List Bool =>
      List.replicate (64 * (packed.length + 1) ^ 2) true)
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] using hphysical


-- @@ L962-964 verbatim
private abbrev gaussianPhysicalColumnIterationBudgetArchive :
    List Bool → List Bool :=
  firstFieldContents


-- @@ L966-968 verbatim
private abbrev gaussianPhysicalColumnIterationCurrentQuery :
    List Bool → List Bool :=
  firstFieldSuffix


-- @@ L970-974 verbatim
/-- Extract the active column index in unary form. -/
def gaussianPhysicalColumnIterationActiveUnary :
    List Bool → List Bool :=
  gaussianPhysicalColumnActiveUnary ∘
    gaussianPhysicalColumnIterationCurrentQuery


-- @@ L976-983 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationActiveUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationActiveUnary :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable
    gaussianPhysicalColumnActiveUnaryComputable


-- @@ L985-991 verbatim
/-- Extract the candidate pivot column from the iteration state. -/
def gaussianPhysicalColumnIterationCandidate
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (true :: gaussianPhysicalColumnIterationActiveUnary input) ++
    gaussianPhysicalColumnStateOutput
      (gaussianPhysicalColumnIterationCurrentQuery input)


-- @@ L993-1005 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationCandidateComputable :
    BitTM
      gaussianPhysicalColumnIterationCandidate := by
  have hactive := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationActiveUnaryComputable
    (prependBitComputable true)
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    hactive structuralPrefixWriterComputable
  have hstate := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable gaussianPhysicalColumnStateComputable
  exact pointwiseAppendComputable hprefix hstate


-- @@ L1007-1011 verbatim
/-- Encode the archived column budget length in unary form. -/
def gaussianPhysicalColumnIterationBudgetLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    gaussianPhysicalColumnIterationBudgetArchive


-- @@ L1013-1019 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationBudgetLengthUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationBudgetLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable sourceInputLengthUnaryComputable


-- @@ L1021-1025 verbatim
/-- Encode the candidate column length in unary form. -/
def gaussianPhysicalColumnIterationCandidateLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    gaussianPhysicalColumnIterationCandidate


-- @@ L1027-1034 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationCandidateLengthUnaryComputable :
    BitTM
      gaussianPhysicalColumnIterationCandidateLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationCandidateComputable
    sourceInputLengthUnaryComputable


-- @@ L1036-1041 verbatim
/-- Mark whether the column iteration exceeds its budget. -/
def gaussianPhysicalColumnIterationOverflowMarker :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    gaussianPhysicalColumnIterationBudgetLengthUnary
    gaussianPhysicalColumnIterationCandidateLengthUnary


-- @@ L1043-1050 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationOverflowMarkerComputable :
    BitTM
      gaussianPhysicalColumnIterationOverflowMarker :=
  fourFamilyComputedUnaryLessBitComputable
    gaussianPhysicalColumnIterationBudgetLengthUnaryComputable
    gaussianPhysicalColumnIterationCandidateLengthUnaryComputable


-- @@ L1052-1056 verbatim
/-- Mark whether the current pivot candidate is accepted. -/
def gaussianPhysicalColumnIterationAcceptMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    gaussianPhysicalColumnIterationOverflowMarker


-- @@ L1058-1064 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptMarkerComputable :
    BitTM
      gaussianPhysicalColumnIterationAcceptMarker :=
  fourFamilyBooleanNotOutputComputable
    gaussianPhysicalColumnIterationOverflowMarkerComputable


-- @@ L1066-1069 verbatim
/-- Select the accepted column iteration state. -/
def gaussianPhysicalColumnIterationAccepted
    (input : List Bool) : Bool :=
  (gaussianPhysicalColumnIterationAcceptMarker input).headD false


-- @@ L1071-1078 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptedComputable :
    BitTM
      (fun input =>
        gaussianPhysicalColumnIterationAccepted input :: input) :=
  gaussianPhysicalComputedMarkerPreservingComputable
    gaussianPhysicalColumnIterationAcceptMarkerComputable


-- @@ L1080-1085 verbatim
/-- Produce the output of an accepted column iteration. -/
def gaussianPhysicalColumnIterationAcceptedOutput
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (gaussianPhysicalColumnIterationBudgetArchive input) ++
    gaussianPhysicalColumnIterationCandidate input


-- @@ L1087-1095 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationAcceptedOutputComputable :
    BitTM
      gaussianPhysicalColumnIterationAcceptedOutput := by
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  exact pointwiseAppendComputable hbudget
    gaussianPhysicalColumnIterationCandidateComputable


-- @@ L1097-1102 verbatim
/-- Advance the physical Gaussian column iteration by one candidate. -/
def gaussianPhysicalColumnIterationStep :
    List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnIterationAccepted
    gaussianPhysicalColumnIterationAcceptedOutput id


-- @@ L1104-1112 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationStepComputable :
    BitTM
      gaussianPhysicalColumnIterationStep :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnIterationAcceptedComputable
    gaussianPhysicalColumnIterationAcceptedOutputComputable
    (Turing.idComputableInPolyTime bitEncoding)


-- @@ L1114-1127 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationOverflowMarker_valid
    (input : List Bool) :
    gaussianPhysicalColumnIterationOverflowMarker input =
      [decide
        ((gaussianPhysicalColumnIterationBudgetArchive input).length <
          (gaussianPhysicalColumnIterationCandidate input).length)] := by
  unfold gaussianPhysicalColumnIterationOverflowMarker
  apply fourFamilyComputedUnaryLessBitOutput_valid
    gaussianPhysicalColumnIterationBudgetLengthUnary
    gaussianPhysicalColumnIterationCandidateLengthUnary input
    (gaussianPhysicalColumnIterationBudgetArchive input).length
    (gaussianPhysicalColumnIterationCandidate input).length
  · rfl
  · rfl


-- @@ L1129-1143 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationAccepted_valid
    (input : List Bool) :
    gaussianPhysicalColumnIterationAccepted input =
      decide
        ((gaussianPhysicalColumnIterationCandidate input).length ≤
          (gaussianPhysicalColumnIterationBudgetArchive input).length) := by
  unfold gaussianPhysicalColumnIterationAccepted
    gaussianPhysicalColumnIterationAcceptMarker
  rw [fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnIterationOverflowMarker input
    (decide
      ((gaussianPhysicalColumnIterationBudgetArchive input).length <
        (gaussianPhysicalColumnIterationCandidate input).length))
    (gaussianPhysicalColumnIterationOverflowMarker_valid input)]
  simp only [List.headD_cons, ← decide_not, Nat.not_lt]


-- @@ L1145-1156 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationBudgetArchive_step
    (input : List Bool) :
    gaussianPhysicalColumnIterationBudgetArchive
        (gaussianPhysicalColumnIterationStep input) =
      gaussianPhysicalColumnIterationBudgetArchive input := by
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  cases haccept : gaussianPhysicalColumnIterationAccepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, id_eq]
  | true =>
      simp only [↓reduceIte, gaussianPhysicalColumnIterationAcceptedOutput,
          firstFieldContents_valid]


-- @@ L1158-1180 verbatim
private theorem gaussianPhysicalColumnIterationStep_length_le
    (input : List Bool) :
    (gaussianPhysicalColumnIterationStep input).length ≤
      max input.length
        (3 * (gaussianPhysicalColumnIterationBudgetArchive input).length + 1) := by
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  cases haccept : gaussianPhysicalColumnIterationAccepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, id_eq, le_sup_left]
  | true =>
      have hfits :
          (gaussianPhysicalColumnIterationCandidate input).length ≤
            (gaussianPhysicalColumnIterationBudgetArchive input).length := by
        have hdecision :=
          gaussianPhysicalColumnIterationAccepted_valid input
        rw [haccept] at hdecision
        exact of_decide_eq_true hdecision.symm
      change
        (lengthPrefixedWord
          (gaussianPhysicalColumnIterationBudgetArchive input) ++
          gaussianPhysicalColumnIterationCandidate input).length ≤ _
      simp only [List.length_append, lengthPrefixedWord_length]
      omega


-- @@ L1182-1191 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationBudgetArchive_iterate
    (input : List Bool) (stage : ℕ) :
    gaussianPhysicalColumnIterationBudgetArchive
        ((gaussianPhysicalColumnIterationStep^[stage]) input) =
      gaussianPhysicalColumnIterationBudgetArchive input := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ stage ih =>
      rw [Function.iterate_succ_apply',
        gaussianPhysicalColumnIterationBudgetArchive_step, ih]


-- @@ L1193-1205 verbatim
private theorem gaussianPhysicalColumnIteration_iterate_length_le
    (seed : List Bool) (stage : ℕ) :
    ((gaussianPhysicalColumnIterationStep^[stage]) seed).length ≤
      max seed.length
        (3 * (gaussianPhysicalColumnIterationBudgetArchive seed).length + 1) := by
  induction stage with
  | zero => simp only [Function.iterate_zero, id_eq, le_sup_left]
  | succ stage ih =>
      rw [Function.iterate_succ_apply']
      have hstep := gaussianPhysicalColumnIterationStep_length_le
        ((gaussianPhysicalColumnIterationStep^[stage]) seed)
      rw [gaussianPhysicalColumnIterationBudgetArchive_iterate] at hstep
      omega


-- @@ L1207-1230 verbatim
private theorem gaussianPhysicalColumnIterationStep_polynomiallyBoundedFoldStates :
    PolynomiallyBoundedFoldStates
      gaussianPhysicalColumnIterationStep (4 * Polynomial.X + 1) := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq]
  intro input count seed hparse stage _
  have hword := parseUnaryBoundedFold_eq_word
    input count seed hparse
  have hseed : seed.length ≤ input.length := by
    rw [hword]
    simp only [unaryBoundedFoldWord, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  have hbudget := annotatedStructuralFieldAccounting seed
  have harchive :
      (gaussianPhysicalColumnIterationBudgetArchive seed).length ≤
        seed.length := by
    change (firstFieldContents seed).length ≤ seed.length
    omega
  have hstate := gaussianPhysicalColumnIteration_iterate_length_le
    seed stage
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  omega


-- @@ L1232-1240 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationFoldComputable :
    BitTM
      (boundedRecordFoldOutput gaussianPhysicalColumnIterationStep) :=
  boundedDependentRecordFoldComputable
    gaussianPhysicalColumnIterationStepComputable
    (4 * Polynomial.X + 1)
    gaussianPhysicalColumnIterationStep_polynomiallyBoundedFoldStates


-- @@ L1242-1247 verbatim
/-- Initialize the physical Gaussian column iteration state. -/
def gaussianPhysicalColumnIterationSeed
    (packed : List Bool) : List Bool :=
  lengthPrefixedWord
    (gaussianPhysicalColumnIterationBudgetWord packed) ++
    lengthPrefixedWord ([] : List Bool) ++ packed


-- @@ L1249-1267 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationSeedComputable :
    BitTM
      gaussianPhysicalColumnIterationSeed := by
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationBudgetWordComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hbudget
    (pointwiseAppendComputable hzero
      (Turing.idComputableInPolyTime bitEncoding))
  change BitTM
    (fun packed : List Bool =>
      lengthPrefixedWord
          (gaussianPhysicalColumnIterationBudgetWord packed) ++
        lengthPrefixedWord ([] : List Bool) ++ packed)
  simpa only [Function.comp_apply, List.append_assoc, id_eq] using hphysical


-- @@ L1269-1273 verbatim
/-- Prepare the packed state for physical column iteration. -/
def gaussianPhysicalColumnIterationPreparation
    (packed : List Bool) : List Bool :=
  gaussianDenseStateDimensionUnary packed ++
    false :: gaussianPhysicalColumnIterationSeed packed


-- @@ L1275-1284 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationPreparationComputable :
    BitTM
      gaussianPhysicalColumnIterationPreparation := by
  have hseed := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationSeedComputable
    (prependBitComputable false)
  exact pointwiseAppendComputable
    gaussianDenseStateDimensionUnaryComputable hseed


-- @@ L1286-1290 verbatim
/-- Compute the final physical column iteration output. -/
def gaussianPhysicalColumnIterationOutput : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘
    boundedRecordFoldOutput gaussianPhysicalColumnIterationStep ∘
    gaussianPhysicalColumnIterationPreparation


-- @@ L1292-1303 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalColumnIterationComputable :
    BitTM
      gaussianPhysicalColumnIterationOutput := by
  have hfold := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnIterationPreparationComputable
    gaussianPhysicalColumnIterationFoldComputable
  have hbudget := GapCVP.TMComposition.computableInPolyTime
    hfold firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hbudget firstFieldSuffixComputable


-- @@ L1305-1308 verbatim
/-- Compute the physical Gaussian source elimination output. -/
def gaussianPhysicalSourceEliminationOutput : List Bool → List Bool :=
  gaussianPhysicalColumnIterationOutput ∘
    gaussianPhysicalPackedFullInitialStateOutput


-- @@ L1310-1317 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPhysicalSourceEliminationComputable :
    BitTM
      gaussianPhysicalSourceEliminationOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPackedFullInitialStateComputable
    gaussianPhysicalColumnIterationComputable


-- @@ L1319-1319 verbatim
end GaussianAdaptivePhysicalColumnIterationBoundTM


-- @@ L1321-1321 verbatim
namespace GaussianAdaptivePhysicalPackedStateBoundTM


-- @@ L1323-1323 verbatim
open GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L1324-1324 verbatim
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L1325-1325 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM

-- @@ L1326-1326 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM


-- @@ L1328-1333 verbatim
private theorem gaussianPhysicalPackedCheckBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedCheckBits state).length = m * n := by
  simp only [effectiveGaussianPackedCheckBits, List.length_flatMap, List.length_map,
      List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]


-- @@ L1335-1338 verbatim
private theorem gaussianPhysicalPackedRhsBits_length
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedRhsBits state).length = m := by
  simp only [effectiveGaussianPackedRhsBits, List.length_map, List.length_finRange]


-- @@ L1340-1351 verbatim
private theorem gaussianPhysicalPackedPivotWord_length_le
    {m n : ℕ} (state : State m n) (column : Fin n) :
    (effectiveGaussianStatePivotWord state column).length ≤ m + 1 := by
  cases hpivot : effectiveGaussianStatePivotRowOption state column with
  | none => simp only [effectiveGaussianStatePivotWord, hpivot, List.length_cons, List.length_nil,
      zero_add,
                le_add_iff_nonneg_left, zero_le]
  | some row =>
      simp only [effectiveGaussianStatePivotWord, hpivot,
        List.length_cons, List.length_replicate]
      have hrow := row.isLt
      omega


-- @@ L1353-1360 verbatim
private theorem gaussianPhysicalPackedPrefixedPivotWord_length_le
    {m n : ℕ} (state : State m n) (column : Fin n) :
    (lengthPrefixedWord
      (effectiveGaussianStatePivotWord state column)).length ≤
      2 * m + 3 := by
  rw [lengthPrefixedWord_length]
  have hpivot := gaussianPhysicalPackedPivotWord_length_le state column
  omega


-- @@ L1362-1389 verbatim
private theorem gaussianPhysicalPackedPivotRecords_length_le
    {m n : ℕ} (state : State m n)
    (columns : List (Fin n)) :
    ((columns.map
      (effectiveGaussianStatePivotWord state)).flatMap
        lengthPrefixedWord).length ≤
      columns.length * (2 * m + 3) := by
  induction columns with
  | nil => simp only [List.map_nil, List.flatMap_nil, List.length_nil, zero_mul, Std.le_refl]
  | cons column remaining ih =>
      have hpivot :=
        gaussianPhysicalPackedPrefixedPivotWord_length_le state column
      calc
        (((column :: remaining).map
          (effectiveGaussianStatePivotWord state)).flatMap
            lengthPrefixedWord).length =
            (lengthPrefixedWord
              (effectiveGaussianStatePivotWord state column)).length +
              ((remaining.map
                (effectiveGaussianStatePivotWord state)).flatMap
                  lengthPrefixedWord).length := by
                    simp only [List.map_cons, List.flatMap_cons, List.length_append,
                      lengthPrefixedWord_length, List.length_flatMap, List.map_map]
        _ ≤ (2 * m + 3) + remaining.length * (2 * m + 3) :=
          Nat.add_le_add hpivot ih
        _ = (column :: remaining).length * (2 * m + 3) := by
          simp only [List.length_cons, Nat.succ_mul]
          omega


-- @@ L1391-1400 verbatim
private theorem gaussianPhysicalPackedPivotCatalogue_length_le
    {m n : ℕ} (state : State m n) :
    (effectiveGaussianPackedPivotCatalogue state).length ≤
      n * (2 * m + 3) := by
  unfold effectiveGaussianPackedPivotCatalogue
    binaryGaussianPivotBatchStream
    sourceMixedRadixOriginalSourceQueryStream
  simpa only [List.length_finRange] using
    gaussianPhysicalPackedPivotRecords_length_le
      state (List.finRange n)


-- @@ L1402-1407 verbatim
private theorem gaussianPhysicalPackedPrefixedPivotWord_length_pos
    {m n : ℕ} (state : State m n) (column : Fin n) :
    0 < (lengthPrefixedWord
      (effectiveGaussianStatePivotWord state column)).length := by
  rw [lengthPrefixedWord_length]
  omega


-- @@ L1409-1423 verbatim
private theorem gaussianPhysicalPackedPivotRecords_length_ge
    {m n : ℕ} (state : State m n)
    (columns : List (Fin n)) :
    columns.length ≤
      ((columns.map
        (effectiveGaussianStatePivotWord state)).flatMap
          lengthPrefixedWord).length := by
  induction columns with
  | nil => simp only [List.length_nil, List.map_nil, List.flatMap_nil, Std.le_refl]
  | cons column remaining ih =>
      have hpivot :=
        gaussianPhysicalPackedPrefixedPivotWord_length_pos state column
      simp only [List.map_cons, List.flatMap_cons,
        List.length_append, List.length_cons]
      omega


-- @@ L1425-1433 verbatim
private theorem gaussianPhysicalPackedPivotCatalogue_length_ge
    {m n : ℕ} (state : State m n) :
    n ≤ (effectiveGaussianPackedPivotCatalogue state).length := by
  unfold effectiveGaussianPackedPivotCatalogue
    binaryGaussianPivotBatchStream
    sourceMixedRadixOriginalSourceQueryStream
  simpa only [List.length_finRange] using
    gaussianPhysicalPackedPivotRecords_length_ge
      state (List.finRange n)


-- @@ L1435-1441 verbatim
private theorem gaussianPhysicalPackedState_rows_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    m ≤ (effectiveGaussianPackedStateWord state source).length := by
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append, lengthPrefixedWord_length,
    gaussianPhysicalPackedRhsBits_length, List.length_replicate]
  omega


-- @@ L1443-1450 verbatim
private theorem gaussianPhysicalPackedState_columns_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    n ≤ (effectiveGaussianPackedStateWord state source).length := by
  have hpivots := gaussianPhysicalPackedPivotCatalogue_length_ge state
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append, lengthPrefixedWord_length,
    List.length_replicate]
  omega


-- @@ L1452-1458 verbatim
private theorem gaussianPhysicalPackedState_source_le_length
    {m n : ℕ} (state : State m n) (source : List Bool) :
    source.length ≤
      (effectiveGaussianPackedStateWord state source).length := by
  unfold effectiveGaussianPackedStateWord
  simp only [List.length_append]
  omega


-- @@ L1460-1463 verbatim
private def gaussianPhysicalPackedStateSizeBound
    (rows columns sourceLength : ℕ) : ℕ :=
  2 * (rows * columns) + 4 * rows +
    2 * (columns * (2 * rows + 3)) + 4 + sourceLength


-- @@ L1465-1477 verbatim
private theorem gaussianPhysicalPackedStateWord_length_le
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hnext : state.nextPivot ≤ m) :
    (effectiveGaussianPackedStateWord state source).length ≤
      gaussianPhysicalPackedStateSizeBound m n source.length := by
  unfold effectiveGaussianPackedStateWord
    gaussianPhysicalPackedStateSizeBound
  simp only [List.length_append, lengthPrefixedWord_length,
    gaussianPhysicalPackedCheckBits_length,
    gaussianPhysicalPackedRhsBits_length,
    List.length_replicate]
  have hpivots := gaussianPhysicalPackedPivotCatalogue_length_le state
  omega


-- @@ L1479-1489 verbatim
private theorem gaussianPhysicalColumnStep_nextPivot_le
    {m n : ℕ} (state : State m n) (column : Fin n)
    (hnext : state.nextPivot ≤ m) :
    (columnStep state column).nextPivot ≤ m := by
  by_cases hrow : state.nextPivot < m
  · cases hpivot : findPivotOption state column with
    | none => simpa only [columnStep, hrow, ↓reduceDIte, hpivot] using hnext
    | some candidate =>
        simp only [columnStep, hrow, ↓reduceDIte, hpivot]
        omega
  · simpa only [columnStep, hrow, ↓reduceDIte] using hnext


-- @@ L1491-1501 verbatim
private theorem gaussianPhysicalRunColumns_nextPivot_le
    {m n : ℕ} (columns : List (Fin n)) (state : State m n)
    (hnext : state.nextPivot ≤ m) :
    (runColumns columns state).nextPivot ≤ m := by
  induction columns generalizing state with
  | nil => simpa only [runColumns, List.foldl_nil] using hnext
  | cons column remaining ih =>
      change
        (runColumns remaining (columnStep state column)).nextPivot ≤ m
      exact ih (columnStep state column)
        (gaussianPhysicalColumnStep_nextPivot_le state column hnext)


-- @@ L1503-1506 verbatim
private theorem gaussianPhysicalInitialState_nextPivot_le
    {m n : ℕ} (system : System m n) :
    (initialState system).nextPivot ≤ m := by
  simp only [initialState, zero_le]


-- @@ L1508-1556 verbatim
private theorem gaussianPhysicalPackedColumnCandidate_length_le
    {m n : ℕ}
    (reference state : State m n) (source : List Bool)
    (column : Fin n) (hnext : state.nextPivot ≤ m) :
    (gaussianPhysicalPivotColumnQuery (column.val + 1)
      (effectiveGaussianPackedStateWord
        (columnStep state column) source)).length ≤
      64 *
        ((effectiveGaussianPackedStateWord reference source).length + 1) ^ 2 := by
  let originalLength :=
    (effectiveGaussianPackedStateWord reference source).length
  have hrows : m ≤ originalLength :=
    gaussianPhysicalPackedState_rows_le_length reference source
  have hcolumns : n ≤ originalLength :=
    gaussianPhysicalPackedState_columns_le_length reference source
  have hsource : source.length ≤ originalLength :=
    gaussianPhysicalPackedState_source_le_length reference source
  have hproduct : m * n ≤ originalLength * originalLength :=
    Nat.mul_le_mul hrows hcolumns
  have hstep := gaussianPhysicalPackedStateWord_length_le
    (columnStep state column) source
    (gaussianPhysicalColumnStep_nextPivot_le state column hnext)
  have hcolumn := column.isLt
  have hshape :
      (effectiveGaussianPackedStateWord
        (columnStep state column) source).length ≤
        6 * (m * n) + 4 * m + 6 * n + 4 + source.length := by
    calc
      _ ≤ gaussianPhysicalPackedStateSizeBound
          m n source.length := hstep
      _ = _ := by
        unfold gaussianPhysicalPackedStateSizeBound
        ring
  have hcandidate :
      (gaussianPhysicalPivotColumnQuery (column.val + 1)
        (effectiveGaussianPackedStateWord
          (columnStep state column) source)).length ≤
        6 * (originalLength * originalLength) +
          13 * originalLength + 7 := by
    unfold gaussianPhysicalPivotColumnQuery
    simp only [List.length_append, lengthPrefixedWord_length,
      List.length_replicate]
    omega
  calc
    _ ≤ 6 * (originalLength * originalLength) +
        13 * originalLength + 7 := hcandidate
    _ ≤ 64 * (originalLength + 1) ^ 2 := by
      linarith
    _ = _ := by rfl


-- @@ L1558-1558 verbatim
end GaussianAdaptivePhysicalPackedStateBoundTM


-- @@ L1560-1560 verbatim
namespace GaussianAdaptivePhysicalColumnIterationBoundTM


-- @@ L1562-1562 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L1563-1563 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryPhysicalWordPackedMatrixTM

-- @@ L1564-1564 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L1565-1565 verbatim
open GapCVP.GaussianAdaptivePhysicalStateCellTM

-- @@ L1566-1566 verbatim
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM

-- @@ L1567-1567 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnStateTM

-- @@ L1568-1568 verbatim
open GapCVP.GaussianAdaptivePhysicalUpdatedMatrixCatalogueTM

-- @@ L1569-1569 verbatim
open GapCVP.GaussianAdaptivePhysicalInitialStateTM

-- @@ L1570-1570 verbatim
open GapCVP.GaussianAdaptivePhysicalPackedStateBoundTM


-- @@ L1572-1580 verbatim
private def gaussianPhysicalColumnIterationExpectedState
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) : List Bool :=
  lengthPrefixedWord
      (gaussianPhysicalColumnIterationBudgetWord
        (effectiveGaussianPackedStateWord reference source)) ++
    gaussianPhysicalPivotColumnQuery active
      (effectiveGaussianPackedStateWord current source)


-- @@ L1582-1592 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_archive
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationBudgetArchive
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      gaussianPhysicalColumnIterationBudgetWord
        (effectiveGaussianPackedStateWord reference source) := by
  simp only [gaussianPhysicalColumnIterationExpectedState,
      SourceFormulaStructuralDecoder.firstFieldContents_valid]


-- @@ L1594-1604 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_query
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationCurrentQuery
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      gaussianPhysicalPivotColumnQuery active
        (effectiveGaussianPackedStateWord current source) := by
  simp only [gaussianPhysicalColumnIterationExpectedState,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]


-- @@ L1606-1617 verbatim
@[simp] private theorem gaussianPhysicalColumnIterationExpectedState_active
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (active : ℕ) :
    gaussianPhysicalColumnIterationActiveUnary
        (gaussianPhysicalColumnIterationExpectedState
          reference current source active) =
      List.replicate active true := by
  unfold gaussianPhysicalColumnIterationActiveUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnIterationExpectedState_query,
    gaussianPhysicalColumnActiveUnary_query]


-- @@ L1619-1635 verbatim
private theorem gaussianPhysicalColumnIterationCandidate_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnIterationCandidate
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) =
      gaussianPhysicalPivotColumnQuery (column.val + 1)
        (effectiveGaussianPackedStateWord
          (columnStep current column) source) := by
  unfold gaussianPhysicalColumnIterationCandidate
  rw [gaussianPhysicalColumnIterationExpectedState_active,
    gaussianPhysicalColumnIterationExpectedState_query,
    gaussianPhysicalColumnStateOutput_effective
      current source column hrows]
  simp only [gaussianPhysicalPivotColumnQuery, List.replicate_succ]


-- @@ L1637-1661 verbatim
private theorem gaussianPhysicalColumnIterationAccepted_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m)
    (hnext : current.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationAccepted
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) = true := by
  let input := gaussianPhysicalColumnIterationExpectedState
    reference current source column.val
  have hbound := gaussianPhysicalPackedColumnCandidate_length_le
    reference current source column hnext
  have hcandidate := gaussianPhysicalColumnIterationCandidate_effective
    reference current source column hrows
  have harchive := gaussianPhysicalColumnIterationExpectedState_archive
    reference current source column.val
  rw [gaussianPhysicalColumnIterationAccepted_valid]
  change decide
    ((gaussianPhysicalColumnIterationCandidate input).length ≤
      (gaussianPhysicalColumnIterationBudgetArchive input).length) = true
  rw [hcandidate, harchive]
  simp only [gaussianPhysicalColumnIterationBudgetWord,
    List.length_replicate]
  exact decide_eq_true hbound


-- @@ L1663-1689 verbatim
private theorem gaussianPhysicalColumnIterationStep_effective
    {m n : ℕ}
    (reference current : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m)
    (hnext : current.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationStep
        (gaussianPhysicalColumnIterationExpectedState
          reference current source column.val) =
      gaussianPhysicalColumnIterationExpectedState
        reference (columnStep current column)
        source (column.val + 1) := by
  let input := gaussianPhysicalColumnIterationExpectedState
    reference current source column.val
  have haccept := gaussianPhysicalColumnIterationAccepted_effective
    reference current source column hrows hnext
  have harchive := gaussianPhysicalColumnIterationExpectedState_archive
    reference current source column.val
  have hcandidate := gaussianPhysicalColumnIterationCandidate_effective
    reference current source column hrows
  change gaussianPhysicalColumnIterationStep input = _
  unfold gaussianPhysicalColumnIterationStep
    binaryGaussianDynamicBranchOutput
  rw [haccept, ite_eq_left rfl]
  unfold gaussianPhysicalColumnIterationAcceptedOutput
  rw [harchive, hcandidate]
  rfl


-- @@ L1691-1700 verbatim
private theorem gaussianPhysicalEffectiveRunColumns_append
    {m n : ℕ} (first second : List (Fin n))
    (state : State m n) :
    runColumns (first ++ second) state =
      runColumns second (runColumns first state) := by
  induction first generalizing state with
  | nil => simp only [runColumns, List.nil_append, List.foldl_nil]
  | cons column rest ih =>
      simp only [List.cons_append, runColumns]
      exact ih (columnStep state column)


-- @@ L1702-1711 verbatim
private theorem gaussianPhysicalColumnIterationSeed_effective
    {m n : ℕ} (reference : State m n)
    (source : List Bool) :
    gaussianPhysicalColumnIterationSeed
        (effectiveGaussianPackedStateWord reference source) =
      gaussianPhysicalColumnIterationExpectedState
        reference reference source 0 := by
  simp only [gaussianPhysicalColumnIterationSeed, List.append_assoc,
      gaussianPhysicalColumnIterationExpectedState, gaussianPhysicalPivotColumnQuery,
          List.replicate_zero]


-- @@ L1713-1752 verbatim
private theorem gaussianPhysicalColumnIteration_iterate_effective
    {m n : ℕ} (reference : State m n)
    (source : List Bool) (hrows : 0 < m)
    (hnext : reference.nextPivot ≤ m)
    (stage : ℕ) (hstage : stage ≤ n) :
    ((gaussianPhysicalColumnIterationStep^[stage])
      (gaussianPhysicalColumnIterationSeed
        (effectiveGaussianPackedStateWord reference source))) =
      gaussianPhysicalColumnIterationExpectedState
        reference
        (runColumns ((List.finRange n).take stage) reference)
        source stage := by
  induction stage with
  | zero =>
      simpa only [Function.iterate_zero, id_eq, runColumns, List.take_zero, List.foldl_nil] using
          gaussianPhysicalColumnIterationSeed_effective reference source
  | succ stage ih =>
      have hlt : stage < n := by omega
      have hprev : stage ≤ n := by omega
      let active : Fin n := ⟨stage, hlt⟩
      let current :=
        runColumns ((List.finRange n).take stage) reference
      have hcurrent : current.nextPivot ≤ m :=
        gaussianPhysicalRunColumns_nextPivot_le
          ((List.finRange n).take stage) reference hnext
      rw [Function.iterate_succ_apply']
      rw [ih hprev]
      have hstep := gaussianPhysicalColumnIterationStep_effective
        reference current source active hrows hcurrent
      have hactiveval : active.val = stage := rfl
      rw [hactiveval] at hstep
      rw [hstep]
      have hindex : stage < (List.finRange n).length := by
        simpa only [List.length_finRange] using hlt
      have hget : (List.finRange n)[stage] = active := by
        apply Fin.ext
        simpa only [List.getElem_finRange, Fin.cast_mk] using hactiveval.symm
      rw [List.take_succ_eq_append_getElem hindex,
        hget, gaussianPhysicalEffectiveRunColumns_append]
      simp only [runColumns, List.foldl_cons, List.foldl_nil, current]


-- @@ L1754-1765 verbatim
private theorem gaussianPhysicalColumnIterationPreparation_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianPhysicalColumnIterationPreparation
        (effectiveGaussianPackedStateWord state source) =
      unaryBoundedFoldWord n
        (gaussianPhysicalColumnIterationSeed
          (effectiveGaussianPackedStateWord state source)) := by
  unfold gaussianPhysicalColumnIterationPreparation
    unaryBoundedFoldWord
  rw [gaussianDenseStateDimensionUnary_effective
    state source hrows]


-- @@ L1767-1789 verbatim
private theorem gaussianPhysicalColumnIterationOutput_state_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (hrows : 0 < m)
    (hnext : state.nextPivot ≤ m) :
    gaussianPhysicalColumnIterationOutput
        (effectiveGaussianPackedStateWord state source) =
      effectiveGaussianPackedStateWord
        (runColumns (List.finRange n) state) source := by
  unfold gaussianPhysicalColumnIterationOutput
  simp only [Function.comp_apply]
  rw [gaussianPhysicalColumnIterationPreparation_effective
    state source hrows]
  simp only [boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  rw [gaussianPhysicalColumnIteration_iterate_effective
    state source hrows hnext n (Nat.le_refl n)]
  have htake : (List.finRange n).take n =
      List.finRange n := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange n))
  rw [htake]
  simp only [gaussianPhysicalColumnIterationExpectedState, gaussianPhysicalPivotColumnQuery,
      SourceFormulaStructuralDecoder.firstFieldSuffix_valid]


-- @@ L1791-1802 verbatim
private theorem gaussianPhysicalColumnIterationOutput_effective
    {m n : ℕ} (system : System m n)
    (source : List Bool) (hrows : 0 < m) :
    gaussianPhysicalColumnIterationOutput
        (effectiveGaussianPackedStateWord
          (initialState system) source) =
      effectiveGaussianPackedStateWord
        (eliminate system) source := by
  have hnext := gaussianPhysicalInitialState_nextPivot_le system
  simpa only [eliminate] using
      gaussianPhysicalColumnIterationOutput_state_effective (initialState system) source hrows
          hnext


-- @@ L1804-1819 verbatim
private theorem gaussianPhysicalSourceEliminationOutput_effective
    (system : BinaryAffineSystem) (source : List Bool)
    (hrows : 0 < system.rowCount) :
    gaussianPhysicalSourceEliminationOutput
        (lengthPrefixedWord
          (sourcePhysicalWordPackedCheckBits system) ++
          lengthPrefixedWord
            (sourcePhysicalWordPackedRhsBits system) ++ source) =
      effectiveGaussianPackedStateWord
        system.effectiveGaussianState source := by
  unfold gaussianPhysicalSourceEliminationOutput
  rw [Function.comp_apply,
    gaussianPhysicalPackedFullInitialStateOutput_effective
      system source hrows]
  exact gaussianPhysicalColumnIterationOutput_effective
    system.effectiveGaussianSystem source hrows


-- @@ L1821-1821 verbatim
end GaussianAdaptivePhysicalColumnIterationBoundTM


-- @@ L1823-1823 verbatim
namespace GaussianSourceInitializer


-- @@ L1825-1825 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem

-- @@ L1826-1826 verbatim
open GapCVP.FormulaBridge GapCVP.PhysicalColumnOrder GapCVP.SourceOrder

-- @@ L1827-1827 verbatim
open GapCVP.BinaryPhysicalWordPackedMatrixTM GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L1828-1828 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnIterationBoundTM


-- @@ L1830-1858 verbatim
private theorem paperVariableArityPhysicalWordBinarySystem_rowCount_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < (physicalWordBinarySystem
      encodingLength formula).rowCount := by
  let normalized := srcFormula formula
  let degree := sourceFieldExponent
    (sourceSizeParameter encodingLength normalized)
  have hdegree : 0 < degree :=
    sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength normalized)
  have hgrid : 0 < Fintype.card
      (ExplicitGridPoint encodingLength normalized) := by
    simpa [ExplicitGridPoint] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_pos
        encodingLength normalized
  let global : ExplicitConstraintFamily encodingLength normalized := .inl ()
  have hglobal : 0 < explicitFamilyRowCount
      encodingLength normalized global := by
    simpa [global, explicitFamilyRowCount] using hgrid
  let actual : assembledBinaryRow
      (explicitFamilyRowCount encodingLength normalized) degree :=
    ⟨global, (⟨0, hglobal⟩, ⟨0, hdegree⟩)⟩
  let physical :=
    (paperVariableArityExplicitBinaryRowWordOrder
      encodingLength formula).symm actual
  have hphysical := physical.isLt
  change 0 < paperExplicitBinaryRowWordCount
    encodingLength formula
  omega


-- @@ L1860-1876 verbatim
/-- A computer for a packed matrix derived from a variable-arity source. -/
structure PaperVariableArityPhysicalPackedMatrixSourceComputer where
  /-- The serialized matrix produced from an encoded source formula. -/
  output : List Bool → List Bool
  /-- A polynomial-time machine computing the serialized matrix. -/
  computer : BitTM output
  output_valid : ∀ formula : ThreeCNF,
    output (encodeThreeCNF formula) =
      lengthPrefixedWord
        (sourcePhysicalWordPackedCheckBits
          (physicalWordBinarySystem
            (encodeThreeCNF formula).length formula)) ++
        lengthPrefixedWord
          (sourcePhysicalWordPackedRhsBits
            (physicalWordBinarySystem
              (encodeThreeCNF formula).length formula)) ++
        encodeThreeCNF formula


-- @@ L1878-1881 verbatim
private def gaussianPaperVariableAritySourceReducedStateOutput
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    List Bool → List Bool :=
  gaussianPhysicalSourceEliminationOutput ∘ matrix.output


-- @@ L1883-1888 verbatim
private noncomputable def gaussianPaperVariableAritySourceReducedStateComputable
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    BitTM
      (gaussianPaperVariableAritySourceReducedStateOutput matrix) :=
  GapCVP.TMComposition.computableInPolyTime
    matrix.computer gaussianPhysicalSourceEliminationComputable


-- @@ L1890-1906 verbatim
private theorem gaussianPaperVariableAritySourceReducedStateOutput_effective
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer)
    (formula : ThreeCNF) :
    gaussianPaperVariableAritySourceReducedStateOutput matrix
        (encodeThreeCNF formula) =
      effectiveGaussianPackedStateWord
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) := by
  unfold gaussianPaperVariableAritySourceReducedStateOutput
  rw [Function.comp_apply, matrix.output_valid formula]
  exact gaussianPhysicalSourceEliminationOutput_effective
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula)
    (encodeThreeCNF formula)
    (paperVariableArityPhysicalWordBinarySystem_rowCount_pos
      (encodeThreeCNF formula).length formula)


-- @@ L1908-1908 verbatim
end GaussianSourceInitializer


-- @@ L1910-1910 verbatim
namespace GaussianAdaptivePhysicalReducedConsistencyCatalogueTM


-- @@ L1912-1912 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L1913-1913 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter

-- @@ L1914-1914 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L1915-1915 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L1916-1916 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L1917-1917 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM

-- @@ L1918-1918 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.BinaryExplicitAffineRows

-- @@ L1919-1919 verbatim
open GapCVP.GaussianPackedPivotColumnTM GapCVP.GaussianReducedConsistencyTM

-- @@ L1920-1920 verbatim
open GapCVP.GaussianAdaptiveEliminationCorrectness GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L1921-1921 verbatim
open GapCVP.GaussianAdaptivePhysicalStateCellTM GapCVP.GaussianAdaptivePackedStateLookupTM

-- @@ L1922-1922 verbatim
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM


-- @@ L1924-1927 verbatim
private def gaussianPhysicalReducedRowRecordWord
    (row width : ℕ) (state : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate row true) ++
    lengthPrefixedWord (List.replicate width true) ++ state


-- @@ L1929-1930 verbatim
private def gaussianPhysicalReducedRowRank : List Bool → List Bool :=
  firstFieldContents


-- @@ L1932-1935 verbatim
private noncomputable def gaussianPhysicalReducedRowRankComputable :
    BitTM
      gaussianPhysicalReducedRowRank :=
  firstFieldContentsComputable


-- @@ L1937-1938 verbatim
private def gaussianPhysicalReducedRowState : List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L1940-1944 verbatim
private noncomputable def gaussianPhysicalReducedRowStateComputable :
    BitTM
      gaussianPhysicalReducedRowState :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable


-- @@ L1946-1948 verbatim
private def gaussianPhysicalReducedNextUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalReducedRowState


-- @@ L1950-1959 verbatim
private noncomputable def gaussianPhysicalReducedNextUnaryComputable :
    BitTM
      gaussianPhysicalReducedNextUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable


-- @@ L1961-1966 verbatim
private def gaussianPhysicalReducedRowEligibleWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    (fourFamilyComputedUnaryLessBitOutput
      gaussianPhysicalReducedRowRank
      gaussianPhysicalReducedNextUnary)


-- @@ L1968-1974 verbatim
private noncomputable def gaussianPhysicalReducedRowEligibleComputable :
    BitTM
      gaussianPhysicalReducedRowEligibleWord :=
  fourFamilyBooleanNotOutputComputable
    (fourFamilyComputedUnaryLessBitComputable
      gaussianPhysicalReducedRowRankComputable
      gaussianPhysicalReducedNextUnaryComputable)


-- @@ L1976-1979 verbatim
private def gaussianPhysicalReducedRowRhsQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalReducedRowRank input) ++
    (lengthPrefixedWord [] ++ gaussianPhysicalReducedRowState input)


-- @@ L1981-1998 verbatim
private noncomputable def gaussianPhysicalReducedRowRhsQueryComputable :
    BitTM
      gaussianPhysicalReducedRowRhsQuery := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowRankComputable
    structuralPrefixWriterComputable
  have hzero :=
    GapCVP.SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hzero
      gaussianPhysicalReducedRowStateComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalReducedRowRank input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalReducedRowState input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L2000-2002 verbatim
private def gaussianPhysicalReducedRowRhsWord : List Bool → List Bool :=
  gaussianPackedStateRhsCellWord ∘
    gaussianPhysicalReducedRowRhsQuery


-- @@ L2004-2009 verbatim
private noncomputable def gaussianPhysicalReducedRowRhsComputable :
    BitTM
      gaussianPhysicalReducedRowRhsWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowRhsQueryComputable
    gaussianPackedStateRhsCellComputable


-- @@ L2011-2014 verbatim
private def gaussianPhysicalReducedRowOriginalSource :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    firstFieldSuffix ∘ gaussianPhysicalReducedRowState


-- @@ L2016-2027 verbatim
private noncomputable def gaussianPhysicalReducedRowOriginalSourceComputable :
    BitTM
      gaussianPhysicalReducedRowOriginalSource := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  have hnext := GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hnext firstFieldSuffixComputable


-- @@ L2029-2033 verbatim
private def gaussianPhysicalReducedRowPayload
    (input : List Bool) : List Bool :=
  gaussianPhysicalReducedRowEligibleWord input ++
    (gaussianPhysicalReducedRowRhsWord input ++
      gaussianPhysicalReducedRowOriginalSource input)


-- @@ L2035-2048 verbatim
private noncomputable def gaussianPhysicalReducedRowPayloadComputable :
    BitTM
      gaussianPhysicalReducedRowPayload := by
  have hphysical := pointwiseAppendComputable
    gaussianPhysicalReducedRowEligibleComputable
    (pointwiseAppendComputable
      gaussianPhysicalReducedRowRhsComputable
      gaussianPhysicalReducedRowOriginalSourceComputable)
  change BitTM
    (fun input =>
      gaussianPhysicalReducedRowEligibleWord input ++
        (gaussianPhysicalReducedRowRhsWord input ++
          gaussianPhysicalReducedRowOriginalSource input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L2050-2053 verbatim
private def gaussianPhysicalReducedRowRecordOutput :
    List Bool → List Bool :=
  (fun payload => lengthPrefixedWord payload) ∘
    gaussianPhysicalReducedRowPayload


-- @@ L2055-2060 verbatim
private noncomputable def gaussianPhysicalReducedRowRecordComputable :
    BitTM
      gaussianPhysicalReducedRowRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowPayloadComputable
    structuralPrefixWriterComputable


-- @@ L2062-2065 verbatim
private noncomputable def gaussianPhysicalReducedRowWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianDenseStateRowCountUnary
  computer := gaussianDenseStateRowCountUnaryComputable


-- @@ L2067-2071 verbatim
private def gaussianPhysicalReducedRowCatalogueOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable


-- @@ L2073-2078 verbatim
private noncomputable def gaussianPhysicalReducedRowCatalogueComputable :
    BitTM
      gaussianPhysicalReducedRowCatalogueOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable


-- @@ L2080-2083 verbatim
private def gaussianPhysicalReducedConsistencyQueryOutput
    (input : List Bool) : List Bool :=
  gaussianDenseStateRowCountUnary input ++
    (false :: gaussianPhysicalReducedRowCatalogueOutput input)


-- @@ L2085-2097 verbatim
private noncomputable def gaussianPhysicalReducedConsistencyQueryComputable :
    BitTM
      gaussianPhysicalReducedConsistencyQueryOutput := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalReducedRowCatalogueComputable
    (GapCVP.SourceMachineCert.prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    gaussianDenseStateRowCountUnaryComputable htail
  change BitTM
    (fun input =>
      gaussianDenseStateRowCountUnary input ++
        (false :: gaussianPhysicalReducedRowCatalogueOutput input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L2099-2106 verbatim
@[simp] private theorem gaussianPhysicalReducedRowRank_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowRank
        (gaussianPhysicalReducedRowRecordWord row width state) =
      List.replicate row true := by
  simp only [gaussianPhysicalReducedRowRank, gaussianPhysicalReducedRowRecordWord,
      List.append_assoc,
      firstFieldContents_valid]


-- @@ L2108-2115 verbatim
@[simp] private theorem gaussianPhysicalReducedRowState_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowState
        (gaussianPhysicalReducedRowRecordWord row width state) =
      state := by
  simp only [gaussianPhysicalReducedRowState, gaussianPhysicalReducedRowRecordWord,
      List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid]


-- @@ L2117-2126 verbatim
@[simp] private theorem gaussianPhysicalReducedNextUnary_word
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedNextUnary
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalReducedNextUnary, effectiveGaussianPackedStateWord, List.append_assoc,
      Function.comp_apply, gaussianPhysicalReducedRowState_word, firstFieldSuffix_valid,
          firstFieldContents_valid]


-- @@ L2128-2151 verbatim
private theorem gaussianPhysicalReducedRowEligibleWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedRowEligibleWord
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.nextPivot ≤ row)] := by
  let input := gaussianPhysicalReducedRowRecordWord row width
    (effectiveGaussianPackedStateWord state source)
  have hless := fourFamilyComputedUnaryLessBitOutput_valid
    gaussianPhysicalReducedRowRank
    gaussianPhysicalReducedNextUnary input row state.nextPivot
    (gaussianPhysicalReducedRowRank_word row width
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalReducedNextUnary_word
      state source row width)
  change gaussianPhysicalReducedRowEligibleWord input = _
  unfold gaussianPhysicalReducedRowEligibleWord
  rw [fourFamilyBooleanNotOutput_bit _ input _ hless]
  by_cases hlt : row < state.nextPivot
  · have hnot : ¬ state.nextPivot ≤ row := by omega
    simp only [hlt, decide_true, Bool.not_true, hnot, decide_false]
  · have hle : state.nextPivot ≤ row := by omega
    simp only [hlt, decide_false, Bool.not_false, hle, decide_true]


-- @@ L2153-2160 verbatim
@[simp] private theorem gaussianPhysicalReducedRowRhsQuery_word
    (row width : ℕ) (state : List Bool) :
    gaussianPhysicalReducedRowRhsQuery
        (gaussianPhysicalReducedRowRecordWord row width state) =
      affineCellQuery row 0 state := by
  simp only [gaussianPhysicalReducedRowRhsQuery, gaussianPhysicalReducedRowRank_word,
      gaussianPhysicalReducedRowState_word, affineCellQuery, List.replicate_zero,
          List.append_assoc]


-- @@ L2162-2173 verbatim
private theorem gaussianPhysicalReducedRowRhsWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowRhsWord
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      [decide (state.system.rhs row = (1 : ZMod 2))] := by
  unfold gaussianPhysicalReducedRowRhsWord
  rw [Function.comp_apply,
    gaussianPhysicalReducedRowRhsQuery_word]
  exact gaussianPackedStateRhsCellWord_query
    state source row 0


-- @@ L2175-2184 verbatim
@[simp] private theorem gaussianPhysicalReducedRowOriginalSource_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row width : ℕ) :
    gaussianPhysicalReducedRowOriginalSource
        (gaussianPhysicalReducedRowRecordWord row width
          (effectiveGaussianPackedStateWord state source)) =
      source := by
  simp only [gaussianPhysicalReducedRowOriginalSource, effectiveGaussianPackedStateWord,
      List.append_assoc,
      Function.comp_apply, gaussianPhysicalReducedRowState_word, firstFieldSuffix_valid]


-- @@ L2186-2202 verbatim
private theorem gaussianPhysicalReducedRowPayload_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowPayload
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      binaryGaussianPackedPivotRowQuery
        (decide (state.nextPivot ≤ row.val))
        (decide (state.system.rhs row = (1 : ZMod 2))) source := by
  unfold gaussianPhysicalReducedRowPayload
    binaryGaussianPackedPivotRowQuery
  rw [gaussianPhysicalReducedRowEligibleWord_effective
    state source row.val width,
    gaussianPhysicalReducedRowRhsWord_effective
      state source row width,
    gaussianPhysicalReducedRowOriginalSource_effective]
  rfl


-- @@ L2204-2217 verbatim
private theorem gaussianPhysicalReducedRowRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (row : Fin m) (width : ℕ) :
    gaussianPhysicalReducedRowRecordOutput
        (gaussianPhysicalReducedRowRecordWord row.val width
          (effectiveGaussianPackedStateWord state source)) =
      lengthPrefixedWord
        (binaryGaussianPackedPivotRowQuery
          (decide (state.nextPivot ≤ row.val))
          (decide (state.system.rhs row = (1 : ZMod 2))) source) := by
  unfold gaussianPhysicalReducedRowRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalReducedRowPayload_effective
      state source row width]


-- @@ L2219-2226 verbatim
private theorem gaussianPhysicalReducedRowWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedRowWidth.output
        (effectiveGaussianPackedStateWord state source) =
      List.replicate m true := by
  exact gaussianDenseStateRowCountUnary_effective
    state source


-- @@ L2228-2241 verbatim
private theorem gaussianPhysicalReducedRowCatalogueOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalReducedRowWidth.output input =
      List.replicate count true) :
    gaussianPhysicalReducedRowCatalogueOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalReducedRowRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalReducedRowWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalReducedRowWidth
    gaussianPhysicalReducedRowRecordComputable
    input count hwidth


-- @@ L2243-2255 verbatim
private theorem gaussianPhysicalReducedGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (rank : ℕ) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalReducedRowWidth
          (effectiveGaussianPackedStateWord state source) =
      gaussianPhysicalReducedRowRecordWord rank m
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalReducedRowWidth_effective state source]
  simp only [gaussianPhysicalReducedRowRecordWord,
    List.append_assoc]


-- @@ L2257-2307 verbatim
private theorem gaussianPhysicalReducedRowCatalogueOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedRowCatalogueOutput
        (effectiveGaussianPackedStateWord state source) =
      sourceMixedRadixOriginalSourceQueryStream
        ((effectiveGaussianStateReducedConsistencyRows state).map
          (fun row => binaryGaussianPackedPivotRowQuery
            row.1 row.2 source)) := by
  let input := effectiveGaussianPackedStateWord state source
  have hwidth : gaussianPhysicalReducedRowWidth.output input =
      List.replicate m true :=
    gaussianPhysicalReducedRowWidth_effective state source
  have hcatalogue := gaussianPhysicalReducedRowCatalogueOutput_valid
    input m hwidth
  calc
    gaussianPhysicalReducedRowCatalogueOutput input =
        (List.range m).flatMap (fun rank =>
          gaussianPhysicalReducedRowRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalReducedRowWidth input)) :=
      hcatalogue
    _ = (List.range m).flatMap (fun rank =>
          gaussianPhysicalReducedRowRecordOutput
            (gaussianPhysicalReducedRowRecordWord rank m
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalReducedRowRecordOutput
        (gaussianPhysicalReducedGeneratedRecord_effective
          state source rank)
    _ = (List.finRange m).flatMap (fun row =>
          lengthPrefixedWord
            (binaryGaussianPackedPivotRowQuery
              (decide (state.nextPivot ≤ row.val))
              (decide (state.system.rhs row = (1 : ZMod 2)))
              source)) := by
      rw [gaussianPhysicalPivot_range_flatMap_finRange]
      apply List.flatMap_congr
      intro row _
      exact gaussianPhysicalReducedRowRecordOutput_effective
        state source row m
    _ = sourceMixedRadixOriginalSourceQueryStream
          ((effectiveGaussianStateReducedConsistencyRows state).map
            (fun row => binaryGaussianPackedPivotRowQuery
              row.1 row.2 source)) := by
      unfold sourceMixedRadixOriginalSourceQueryStream
        effectiveGaussianStateReducedConsistencyRows
      simp only [List.flatMap_map, List.map_map,
        Function.comp_apply]


-- @@ L2309-2322 verbatim
private theorem gaussianPhysicalReducedConsistencyQueryOutput_state_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) :
    gaussianPhysicalReducedConsistencyQueryOutput
        (effectiveGaussianPackedStateWord state source) =
      effectiveGaussianStateReducedConsistencyQuery state source := by
  unfold gaussianPhysicalReducedConsistencyQueryOutput
  rw [gaussianDenseStateRowCountUnary_effective,
    gaussianPhysicalReducedRowCatalogueOutput_effective]
  unfold effectiveGaussianStateReducedConsistencyQuery
    binaryGaussianPackedPivotColumnWord
    unaryBoundedFoldWord
  simp only [effectiveGaussianStateReducedConsistencyRows,
    List.length_map, List.length_finRange]


-- @@ L2324-2332 verbatim
private theorem gaussianPhysicalReducedConsistencyQueryOutput_effective
    (system : BinaryAffineSystem) (source : List Bool) :
    gaussianPhysicalReducedConsistencyQueryOutput
        (effectiveGaussianPackedStateWord
          system.effectiveGaussianState source) =
      effectiveGaussianReducedConsistencyQuery system source := by
  simpa only [effectiveGaussianStateReducedConsistencyQuery_effective] using
    gaussianPhysicalReducedConsistencyQueryOutput_state_effective
      system.effectiveGaussianState source


-- @@ L2334-2334 verbatim
end GaussianAdaptivePhysicalReducedConsistencyCatalogueTM


-- @@ L2336-2336 verbatim
namespace GaussianSourceReducedConsistency


-- @@ L2338-2338 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.PhysicalColumnOrder GapCVP.GaussianSourceInitializer

-- @@ L2339-2339 verbatim
open GapCVP.GaussianAdaptivePhysicalReducedConsistencyCatalogueTM

-- @@ L2340-2340 verbatim
open GapCVP.GaussianReducedConsistencyTM


-- @@ L2342-2347 verbatim
/-- Form the reduced-consistency query from a variable-arity source matrix. -/
def gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    List Bool → List Bool :=
  gaussianPhysicalReducedConsistencyQueryOutput ∘
    gaussianPaperVariableAritySourceReducedStateOutput matrix


-- @@ L2349-2358 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    gaussianPaperVariableAritySourceReducedConsistencyQueryComputable
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer) :
    BitTM
      (gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
        matrix) :=
  GapCVP.TMComposition.computableInPolyTime
    (gaussianPaperVariableAritySourceReducedStateComputable matrix)
    gaussianPhysicalReducedConsistencyQueryComputable


-- @@ L2360-2376 verbatim
private theorem gaussianPaperVariableAritySourceReducedConsistencyQueryOutput_valid
    (matrix : PaperVariableArityPhysicalPackedMatrixSourceComputer)
    (formula : ThreeCNF) :
    gaussianPaperVariableAritySourceReducedConsistencyQueryOutput matrix
        (encodeThreeCNF formula) =
      effectiveGaussianReducedConsistencyQuery
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula)
        (encodeThreeCNF formula) := by
  unfold gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
  rw [Function.comp_apply,
    gaussianPaperVariableAritySourceReducedStateOutput_effective
      matrix formula]
  exact gaussianPhysicalReducedConsistencyQueryOutput_effective
    (physicalWordBinarySystem
      (encodeThreeCNF formula).length formula)
    (encodeThreeCNF formula)


-- @@ L2378-2378 verbatim
end GaussianSourceReducedConsistency


-- @@ L2380-2380 verbatim
namespace GaussianSourceInitializerInstantiation


-- @@ L2382-2382 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CanonicalMatrixShape

-- @@ L2383-2383 verbatim
open GapCVP.CanonicalSourceCatalogue GapCVP.PhysicalColumnOrder

-- @@ L2384-2384 verbatim
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianReducedConsistencyTM

-- @@ L2385-2385 verbatim
open GapCVP.GaussianSourceInitializer GapCVP.GaussianSourceReducedConsistency


-- @@ L2387-2395 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    PaperVariableArityPhysicalPackedMatrixSourceComputer where
  output := paperCanonicalBinaryMatrixPackedOutput worker
  computer := paperVariableArityCanonicalBinaryMatrixPackedComputable worker
  output_valid := paperVariableArityCanonicalBinaryMatrixPackedOutput_valid worker


-- @@ L2397-2403 verbatim
/-- GapCVP reduction support. -/
def gaussianPaperVariableArityCanonicalSourceReducedStateOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  gaussianPaperVariableAritySourceReducedStateOutput
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)


-- @@ L2405-2413 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityCanonicalSourceReducedStateComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityCanonicalSourceReducedStateOutput worker) :=
  gaussianPaperVariableAritySourceReducedStateComputable
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)


-- @@ L2415-2427 verbatim
theorem gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    gaussianPaperVariableArityCanonicalSourceReducedStateOutput worker
        (encodeThreeCNF formula) =
      effectiveGaussianPackedStateWord
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) :=
  gaussianPaperVariableAritySourceReducedStateOutput_effective
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)
    formula


-- @@ L2429-2435 verbatim
/-- Form the canonical source's reduced-consistency query. -/
def gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryOutput
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)


-- @@ L2437-2446 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
        worker) :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryComputable
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)


-- @@ L2448-2461 verbatim
theorem
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
        worker (encodeThreeCNF formula) =
      effectiveGaussianReducedConsistencyQuery
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula)
        (encodeThreeCNF formula) :=
  gaussianPaperVariableAritySourceReducedConsistencyQueryOutput_valid
    (paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer worker)
    formula


-- @@ L2463-2463 verbatim
end GaussianSourceInitializerInstantiation


-- @@ L2465-2465 verbatim
namespace GaussianOutputSerializerTM


-- @@ L2467-2467 verbatim
open Turing GapCVP.Core GapCVP.Factor400BinaryInstanceBridge GapCVP.BinaryEncoding

-- @@ L2468-2468 verbatim
open GapCVP.SourceMachineCert GapCVP.CLStructuralPrefixWriter

-- @@ L2469-2469 verbatim
open GapCVP.CLStructuralAtomicNaturalWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L2470-2470 verbatim
open GapCVP.BinaryDimensionTM GapCVP.BinaryExplicitAffineRows GapCVP.BinaryStructuralRecordTM

-- @@ L2471-2471 verbatim
open GapCVP.BinaryGaussianStructuralAtomTM GapCVP.BinaryGaussianStructuralRecordIndex

-- @@ L2472-2472 verbatim
open GapCVP.BinaryPhysicalRowBasisDivisionTM GapCVP.GaussianPhysicalWordRankIndexTM

-- @@ L2473-2473 verbatim
open GapCVP.GaussianPackedStateTargetAtomTM GapCVP.GaussianPackedStateBasisAtomTM

-- @@ L2474-2474 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness

-- @@ L2475-2475 verbatim
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape

-- @@ L2476-2476 verbatim
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap

-- @@ L2477-2477 verbatim
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM


-- @@ L2479-2484 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperGaussianSourceDimensionWidth
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    SourceQaryMaskDynamicGridWidth where
  output := shape.columns
  computer := shape.columnsComputable


-- @@ L2486-2497 verbatim
theorem paperVariableArityGaussianSourceDimensionWidth_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) :
    (paperGaussianSourceDimensionWidth shape).output
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension true := by
  change shape.columns (encodeThreeCNF formula) = _
  have actual := shape.columnsCorrect formula
  rw [shape.systemCorrect] at actual
  exact actual


-- @@ L2499-2503 verbatim
/-- GapCVP reduction support. -/
def paperGaussianRankDimensionUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  shape.columns ∘ structuralRankOriginalSource


-- @@ L2505-2510 verbatim
private noncomputable def paperGaussianRankDimensionComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankDimensionUnary shape) :=
  GapCVP.TMComposition.computableInPolyTime
    structuralRankOriginalSourceComputable shape.columnsComputable


-- @@ L2512-2524 verbatim
theorem paperGaussianRankDimensionUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianRankDimensionUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension true := by
  unfold paperGaussianRankDimensionUnary
  rw [Function.comp_apply, structuralRankOriginalSource_query]
  exact paperVariableArityGaussianSourceDimensionWidth_valid shape formula


-- @@ L2526-2531 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperGaussianRankDimensionAtomicOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  structuralAtomicNaturalWord ∘
    paperGaussianRankDimensionUnary shape


-- @@ L2533-2540 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankDimensionAtomicComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankDimensionAtomicOutput shape) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperGaussianRankDimensionComputable shape)
    structuralAtomicNaturalWriterComputable


-- @@ L2542-2546 verbatim
/-- GapCVP reduction support. -/
def paperGaussianRankTargetBound
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (input : List Bool) : List Bool :=
  true :: true :: paperGaussianRankDimensionUnary shape input


-- @@ L2548-2557 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankTargetBoundComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianRankTargetBound shape) := by
  have once := GapCVP.TMComposition.computableInPolyTime
    (paperGaussianRankDimensionComputable shape)
    (prependBitComputable true)
  exact GapCVP.TMComposition.computableInPolyTime
    once (prependBitComputable true)


-- @@ L2559-2576 verbatim
theorem paperVariableArityGaussianRankTargetBound_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianRankTargetBound shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension) true := by
  unfold paperGaussianRankTargetBound
  rw [paperGaussianRankDimensionUnary_query]
  rw [show 2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension =
    Nat.succ (Nat.succ (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension) by omega]
  simp only [paperVariableArityPhysicalFormulaSystem_dimension, Nat.succ_eq_add_one,
      List.replicate_succ]


-- @@ L2578-2582 verbatim
private def paperGaussianBasisFlatUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  unarySubtractionOutput structuralRankUnary
    (paperGaussianRankTargetBound shape)


-- @@ L2584-2589 verbatim
private noncomputable def paperVariableArityGaussianBasisFlatComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisFlatUnary shape) :=
  unarySubtractionComputable structuralRankUnaryComputable
    (paperVariableArityGaussianRankTargetBoundComputable shape)


-- @@ L2591-2613 verbatim
private theorem paperVariableArityGaussianBasisFlatUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisFlatUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        (rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) true := by
  exact unarySubtractionOutput_valid structuralRankUnary
    (paperGaussianRankTargetBound shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    rank
    (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension)
    (structuralRankUnary_query
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (paperVariableArityGaussianRankTargetBound_query
      shape formula rank)


-- @@ L2615-2621 verbatim
/-- GapCVP reduction support. -/
def paperGaussianBasisRowUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryQuotient
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)


-- @@ L2623-2629 verbatim
private noncomputable def paperVariableArityGaussianBasisRowComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisRowUnary shape) :=
  sourcePhysicalComputedUnaryQuotientComputable
    (paperVariableArityGaussianBasisFlatComputable shape)
    (paperGaussianRankDimensionComputable shape)


-- @@ L2631-2637 verbatim
/-- GapCVP reduction support. -/
def paperGaussianBasisColumnUnary
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)


-- @@ L2639-2645 verbatim
private noncomputable def paperVariableArityGaussianBasisColumnComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape) :
    BitTM
      (paperGaussianBasisColumnUnary shape) :=
  sourcePhysicalComputedUnaryRemainderComputable
    (paperVariableArityGaussianBasisFlatComputable shape)
    (paperGaussianRankDimensionComputable shape)


-- @@ L2647-2673 verbatim
theorem paperVariableArityGaussianBasisRowUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisRowUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        ((rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) /
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).dimension) true := by
  exact sourcePhysicalComputedUnaryQuotient_valid
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (rank - (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension))
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityGaussianBasisFlatUnary_query shape formula rank)
    (paperGaussianRankDimensionUnary_query
      shape formula rank)


-- @@ L2675-2701 verbatim
theorem paperVariableArityGaussianBasisColumnUnary_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (formula : ThreeCNF) (rank : ℕ) :
    paperGaussianBasisColumnUnary shape
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      List.replicate
        ((rank - (2 + (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension)) %
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).dimension) true := by
  exact sourcePhysicalComputedUnaryRemainder_valid
    (paperGaussianBasisFlatUnary shape)
    (paperGaussianRankDimensionUnary shape)
    (constructiveStructuralRankQuery
      (paperGaussianSourceDimensionWidth shape)
      (encodeThreeCNF formula) rank)
    (rank - (2 + (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension))
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula).dimension
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityGaussianBasisFlatUnary_query shape formula rank)
    (paperGaussianRankDimensionUnary_query
      shape formula rank)


-- @@ L2703-2712 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperGaussianRankBasisStateQuery
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
      (paperGaussianBasisRowUnary shape input) ++
    (lengthPrefixedWord
      (paperGaussianBasisColumnUnary shape input) ++
      compactPhysicalGaussianRankReducedState reduced input)


-- @@ L2714-2737 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityGaussianRankBasisStateQueryComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperGaussianRankBasisStateQuery shape reduced) := by
  have row := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianBasisRowComputable shape)
    structuralPrefixWriterComputable
  have column := GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianBasisColumnComputable shape)
    structuralPrefixWriterComputable
  have tail := pointwiseAppendComputable column
    (compactPhysicalGaussianRankReducedStateComputable computer)
  have physical := pointwiseAppendComputable row tail
  change BitTM
    (fun input =>
      lengthPrefixedWord
          (paperGaussianBasisRowUnary shape input) ++
        (lengthPrefixedWord
          (paperGaussianBasisColumnUnary shape input) ++
          compactPhysicalGaussianRankReducedState reduced input))
  simpa only [Function.comp_apply] using physical


-- @@ L2739-2743 verbatim
private def paperGaussianRankBasisAtom
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPackedIndexedBasisAtom ∘
    paperGaussianRankBasisStateQuery shape reduced


-- @@ L2745-2754 verbatim
private noncomputable def paperVariableArityGaussianRankBasisAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperGaussianRankBasisAtom shape reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    (paperVariableArityGaussianRankBasisStateQueryComputable
      shape computer)
    gaussianPackedIndexedBasisAtomComputable


-- @@ L2756-2770 verbatim
/-- Compute the structural atom used by the paper's Gaussian reduction. -/
def paperGaussianStructuralAtomOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (radius reduced : List Bool → List Bool) : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    (structuralRankLessBit structuralRankOneBound)
    (paperGaussianRankDimensionAtomicOutput shape)
    (binaryGaussianDynamicBranchOutput
      (structuralRankLessBit structuralRankTwoBound)
      (compactPhysicalGaussianRankRadiusAtom radius)
      (binaryGaussianDynamicBranchOutput
        (structuralRankLessBit
          (paperGaussianRankTargetBound shape))
        (compactPhysicalGaussianRankTargetAtom reduced)
        (paperGaussianRankBasisAtom shape reduced)))


-- @@ L2772-2797 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    BitTM
      (paperGaussianStructuralAtomOutput
        shape radius reduced) := by
  have tail := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      (paperVariableArityGaussianRankTargetBoundComputable shape))
    (compactPhysicalGaussianRankTargetAtomComputable reducedComputer)
    (paperVariableArityGaussianRankBasisAtomComputable
      shape reducedComputer)
  have scalar := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankTwoBoundComputable)
    (compactPhysicalGaussianRankRadiusAtomComputable radiusComputer)
    tail
  exact binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankOneBoundComputable)
    (paperVariableArityGaussianRankDimensionAtomicComputable shape)
    scalar


-- @@ L2799-2811 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralAtomComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    ConstructiveStructuralAtomComputer :=
  compactPhysicalGaussianStructuralAtomComputerPack
    (paperGaussianStructuralAtomOutput
      shape radius reduced)
    (paperVariableArityGaussianStructuralAtomComputable
      shape radiusComputer reducedComputer)


-- @@ L2813-2828 verbatim
@[simp] private theorem paperVariableArityGaussianStructuralAtomComputer_output
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced)
    (input : List Bool) :
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer).output input =
      paperGaussianStructuralAtomOutput
        shape radius reduced input := by
  unfold paperVariableArityGaussianStructuralAtomComputer
  exact compactPhysicalGaussianStructuralAtomComputerPack_output
    (paperGaussianStructuralAtomOutput
      shape radius reduced)
    (paperVariableArityGaussianStructuralAtomComputable
      shape radiusComputer reducedComputer) input


-- @@ L2830-2839 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperGaussianStructuralSourceWord
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) : List Bool → List Bool :=
  constructiveStructuralSourceWord
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)


-- @@ L2841-2854 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityGaussianStructuralSourceWordComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced) :
    BitTM
      (paperGaussianStructuralSourceWord
        shape radiusComputer reducedComputer) :=
  constructiveStructuralSourceWordComputable
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)


-- @@ L2856-2875 verbatim
theorem paperGaussianRankReducedState_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    compactPhysicalGaussianRankReducedState reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      effectiveGaussianPackedStateWord
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveGaussianState
        (encodeThreeCNF formula) := by
  unfold compactPhysicalGaussianRankReducedState
  rw [Function.comp_apply, structuralRankOriginalSource_query, actual]


-- @@ L2877-2908 verbatim
private theorem paperVariableArityGaussianRankTargetAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (index : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (indexCorrect : rank - 2 = index.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    compactPhysicalGaussianRankTargetAtom reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        (((physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveAffineRepresentative
            index : ℤ) : ℚ) := by
  unfold compactPhysicalGaussianRankTargetAtom
  rw [Function.comp_apply]
  unfold compactPhysicalGaussianRankTargetStateQuery
  rw [factor400PhysicalWordGaussianTargetCoordinateUnary_query,
    paperGaussianRankReducedState_query
      shape formula rank actual, indexCorrect]
  exact gaussianPackedIndexedTargetAtom_effective
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula)
    index (encodeThreeCNF formula)


-- @@ L2910-2956 verbatim
private theorem paperVariableArityGaussianRankBasisAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (row column : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (rowCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) /
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = row.val)
    (columnCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) %
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = column.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperGaussianRankBasisAtom shape reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        ((physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveSquareBasisMatrix
          row column) := by
  unfold paperGaussianRankBasisAtom
  rw [Function.comp_apply]
  unfold paperGaussianRankBasisStateQuery
  rw [paperVariableArityGaussianBasisRowUnary_query
        shape formula rank,
      paperVariableArityGaussianBasisColumnUnary_query
        shape formula rank,
      paperGaussianRankReducedState_query
        shape formula rank actual,
      rowCorrect, columnCorrect]
  simpa only [gaussianPackedIndexedBasisStateWord,
    affineCellQuery, List.append_assoc] using
    gaussianPackedIndexedBasisAtom_effective
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula)
      row column (encodeThreeCNF formula)


-- @@ L2958-3142 verbatim
private theorem paperVariableArityGaussianStructuralAtomOutput_correct
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (formula : ThreeCNF)
    (radiusValue : ℚ)
    (radiusPositive : 0 < radiusValue)
    (actualRadius :
      radius (encodeThreeCNF formula) = encodeAtomic radiusValue)
    (actualReduced :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula))
    (rank : ℕ)
    (recordBound :
      rank <
        (sourceLatticeStructuralRecords
          (effectiveGapCVPInstance
            (physicalFormulaSystem
              (encodeThreeCNF formula).length formula)
            (physicalFormulaSystem_dimension_pos
              (encodeThreeCNF formula).length formula)
            radiusValue radiusPositive)).length) :
    paperGaussianStructuralAtomOutput
        shape radius reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      (sourceLatticeStructuralRecords
        (effectiveGapCVPInstance
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula)
          (physicalFormulaSystem_dimension_pos
            (encodeThreeCNF formula).length formula)
          radiusValue radiusPositive)).getD rank [] := by
  let source := encodeThreeCNF formula
  let system := physicalFormulaSystem
    source.length formula
  let positiveDimension :=
    physicalFormulaSystem_dimension_pos
      source.length formula
  let lattice := effectiveGapCVPInstance
    system positiveDimension radiusValue radiusPositive
  let width := paperGaussianSourceDimensionWidth shape
  let query := constructiveStructuralRankQuery width source rank
  have one :
      structuralRankLessBit structuralRankOneBound query =
        decide (rank < 1) :=
    structuralRankOneDecision_query width source rank
  have two :
      structuralRankLessBit structuralRankTwoBound query =
        decide (rank < 2) :=
    structuralRankTwoDecision_query width source rank
  have boundary :
      paperGaussianRankTargetBound shape query =
        List.replicate (2 + lattice.dimension) true := by
    have dimension : lattice.dimension = system.dimension := rfl
    rw [dimension]
    simpa only [query, source, width, system] using
      paperVariableArityGaussianRankTargetBound_query
        shape formula rank
  have target :
      structuralRankLessBit
        (paperGaussianRankTargetBound shape) query =
          decide (rank < 2 + lattice.dimension) :=
    structuralRankLessBit_valid
      (paperGaussianRankTargetBound shape)
      query rank (2 + lattice.dimension)
      (structuralRankUnary_query width source rank) boundary
  change paperGaussianStructuralAtomOutput
    shape radius reduced query =
    (sourceLatticeStructuralRecords lattice).getD rank []
  unfold paperGaussianStructuralAtomOutput
    binaryGaussianDynamicBranchOutput
  rw [one]
  by_cases zeroRank : rank < 1
  · rw [decide_eq_true zeroRank, ite_eq_left (by decide)]
    have exactRank : rank = 0 := by omega
    subst rank
    change
      paperGaussianRankDimensionAtomicOutput shape
          (constructiveStructuralRankQuery width source 0) =
        (sourceLatticeStructuralRecords lattice).getD 0 []
    unfold paperGaussianRankDimensionAtomicOutput
    rw [Function.comp_apply]
    change
      structuralAtomicNaturalWord
          (paperGaussianRankDimensionUnary shape
            (constructiveStructuralRankQuery
              (paperGaussianSourceDimensionWidth shape)
              (encodeThreeCNF formula) 0)) =
        (sourceLatticeStructuralRecords lattice).getD 0 []
    rw [paperGaussianRankDimensionUnary_query
      shape formula 0,
      sourceLatticeStructuralRecords_getD_dimension lattice]
    simp only [structuralAtomicNaturalWord, List.length_replicate]
    rfl
  · rw [decide_eq_false zeroRank, ite_eq_right (by decide), two]
    by_cases radiusRank : rank < 2
    · rw [decide_eq_true radiusRank, ite_eq_left (by decide)]
      have exactRank : rank = 1 := by omega
      subst rank
      change
        compactPhysicalGaussianRankRadiusAtom radius
            (constructiveStructuralRankQuery width source 1) =
          (sourceLatticeStructuralRecords lattice).getD 1 []
      unfold compactPhysicalGaussianRankRadiusAtom
      rw [Function.comp_apply, structuralRankOriginalSource_query]
      change radius (encodeThreeCNF formula) =
        (sourceLatticeStructuralRecords lattice).getD 1 []
      rw [actualRadius,
        sourceLatticeStructuralRecords_getD_radius lattice]
      rfl
    · rw [decide_eq_false radiusRank, ite_eq_right (by decide), target]
      by_cases targetRank : rank < 2 + lattice.dimension
      · rw [decide_eq_true targetRank, ite_eq_left (by decide)]
        have dimension : lattice.dimension = system.dimension := rfl
        have indexBound : rank - 2 < system.dimension := by omega
        let index : Fin system.dimension := ⟨rank - 2, indexBound⟩
        have exactRank : rank = 2 + index.val := by
          dsimp [index]
          omega
        have atom := paperVariableArityGaussianRankTargetAtom_query
          shape formula rank index rfl actualReduced
        have exactRecord :
            (sourceLatticeStructuralRecords lattice).getD rank [] =
              encodeAtomic
                ((system.effectiveAffineRepresentative index : ℤ) : ℚ) := by
          rw [exactRank,
            sourceLatticeStructuralRecords_getD_target lattice index]
          rfl
        rw [exactRecord]
        exact atom
      · rw [decide_eq_false targetRank, ite_eq_right (by decide)]
        have positive : 0 < system.dimension := positiveDimension
        have dimension : lattice.dimension = system.dimension := rfl
        have latticeRecords :
            rank < 2 + lattice.dimension +
              lattice.dimension * lattice.dimension := by
          simpa only [sourceLatticeStructuralRecords_length]
            using recordBound
        rw [dimension] at latticeRecords
        have records :
            rank < 2 + system.dimension +
              system.dimension * system.dimension := latticeRecords
        have start : 2 + system.dimension ≤ rank := by omega
        have offset :
            rank - (2 + system.dimension) <
              system.dimension * system.dimension := by omega
        have rowBound :
            (rank - (2 + system.dimension)) / system.dimension <
              system.dimension :=
          (Nat.div_lt_iff_lt_mul positive).2 offset
        let row : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) / system.dimension,
            rowBound⟩
        let column : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) % system.dimension,
            Nat.mod_lt _ positive⟩
        have decompose :
            row.val * system.dimension + column.val =
              rank - (2 + system.dimension) := by
          dsimp [row, column]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod _ _
        have exactRank :
            rank = 2 + system.dimension +
              row.val * system.dimension + column.val := by omega
        have atom := paperVariableArityGaussianRankBasisAtom_query
          shape formula rank row column rfl rfl actualReduced
        have exactRecord :
            (sourceLatticeStructuralRecords lattice).getD rank [] =
              encodeAtomic
                (system.effectiveSquareBasisMatrix row column) := by
          rw [exactRank]
          change
            (sourceLatticeStructuralRecords lattice).getD
                (2 + lattice.dimension +
                  row.val * lattice.dimension + column.val) [] =
              encodeAtomic (lattice.basis row column)
          exact sourceLatticeStructuralRecords_getD_basis
            lattice row column
        rw [exactRecord]
        exact atom


-- @@ L3144-3188 verbatim
theorem paperVariableArityGaussianStructuralSourceWord_eq_encodeGapCVPInstance
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {radius reduced : List Bool → List Bool}
    (radiusComputer : BitTM radius)
    (reducedComputer : BitTM reduced)
    (formula : ThreeCNF)
    (radiusValue : ℚ)
    (radiusPositive : 0 < radiusValue)
    (actualRadius :
      radius (encodeThreeCNF formula) = encodeAtomic radiusValue)
    (actualReduced :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperGaussianStructuralSourceWord
        shape radiusComputer reducedComputer
        (encodeThreeCNF formula) =
      encodeGapCVPInstance
        (effectiveGapCVPInstance
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula)
          (physicalFormulaSystem_dimension_pos
            (encodeThreeCNF formula).length formula)
          radiusValue radiusPositive) := by
  let lattice := effectiveGapCVPInstance
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula)
    (physicalFormulaSystem_dimension_pos
      (encodeThreeCNF formula).length formula)
    radiusValue radiusPositive
  unfold paperGaussianStructuralSourceWord
  apply constructiveStructuralSourceWord_eq_encodeGapCVPInstance
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityGaussianStructuralAtomComputer
      shape radiusComputer reducedComputer)
    (encodeThreeCNF formula) lattice
  · exact paperVariableArityGaussianSourceDimensionWidth_valid
      shape formula
  · intro rank bound
    rw [paperVariableArityGaussianStructuralAtomComputer_output]
    exact paperVariableArityGaussianStructuralAtomOutput_correct
      shape formula radiusValue radiusPositive
      actualRadius actualReduced rank bound


-- @@ L3190-3190 verbatim
end GaussianOutputSerializerTM


-- @@ L3192-3192 verbatim
namespace PhysicalFamilyRowTM


-- @@ L3194-3194 verbatim
open scoped BigOperators


-- @@ L3196-3196 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L3197-3197 verbatim
open GapCVP.SourceMachineCert GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L3198-3198 verbatim
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L3199-3199 verbatim
open GapCVP.CLStructuralNaturalBinaryWriter GapCVP.CLVerifier GapCVP.BinaryDimensionTM

-- @@ L3200-3200 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinarySourceVariableCompaction

-- @@ L3201-3201 verbatim
open GapCVP.BinaryCompactSourceFirstOccurrenceTM GapCVP.SourcePreprocessingSemantics

-- @@ L3202-3202 verbatim
open GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge GapCVP.ClauseOffsetTM


-- @@ L3204-3207 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaSize (formula : ThreeCNF) : ℕ :=
  sourceSizeParameter (encodeThreeCNF formula).length
    (srcFormula formula)


-- @@ L3209-3211 verbatim
/-- GapCVP reduction support. -/
abbrev physDegree (formula : ThreeCNF) : ℕ :=
  sourceFieldExponent (physicalFormulaSize formula)


-- @@ L3213-3216 verbatim
/-- GapCVP reduction support. -/
abbrev physFieldCard
    (formula : ThreeCNF) : ℕ :=
  2 ^ physDegree formula


-- @@ L3218-3221 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaVariableCount
    (formula : ThreeCNF) : ℕ :=
  paperVariableArityVariableCount formula


-- @@ L3223-3227 verbatim
/-- GapCVP reduction support. -/
abbrev physGridCard
    (formula : ThreeCNF) : ℕ :=
  physFieldCard formula -
    physicalFormulaVariableCount formula


-- @@ L3229-3232 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaMomentCount
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaSize formula ^ 30 + 1


-- @@ L3234-3238 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaTupleCount
    (formula : ThreeCNF) : ℕ :=
  sourceClauseWeightSum
    (noTautClauses formula)


-- @@ L3240-3244 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaGlobalBoundary
    (formula : ThreeCNF) : ℕ :=
  physGridCard formula *
    physDegree formula


-- @@ L3246-3253 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaRefinementBoundary
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaGlobalBoundary formula +
    (noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula *
      physDegree formula


-- @@ L3255-3262 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaOrdinaryBoundary
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaRefinementBoundary formula +
    (1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula *
      physDegree formula


-- @@ L3264-3266 verbatim
private def physicalFamilyRetainedSource :
    List Bool → List Bool :=
  firstFieldContents ∘ paperSourcePreprocessingOutput


-- @@ L3268-3272 verbatim
private noncomputable def paperVariableArityPhysicalFamilyRetainedSourceComputable :
    BitTM
      physicalFamilyRetainedSource :=
  GapCVP.TMComposition.computableInPolyTime
    paperSourcePreprocessingComputable firstFieldContentsComputable


-- @@ L3274-3284 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilyRetainedSource_valid
    (formula : ThreeCNF) :
    physicalFamilyRetainedSource
        (encodeThreeCNF formula) =
      encodeThreeCNF (noTautClauses formula) := by
  unfold physicalFamilyRetainedSource
  rw [Function.comp_apply, paperSourcePreprocessingOutput_valid]
  exact firstFieldContents_valid
    (encodeThreeCNF (noTautClauses formula))
    (lengthPrefixedWord (paperSourceNormalizedClauseStream formula) ++
      encodeThreeCNF formula)


-- @@ L3286-3288 verbatim
private def physicalFamilyClauseCountUnary :
    List Bool → List Bool :=
  sourceClauseCountUnary ∘ physicalFamilyRetainedSource


-- @@ L3290-3295 verbatim
private noncomputable def physicalFamilyClauseCountUnaryComputable :
    BitTM
      physicalFamilyClauseCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyRetainedSourceComputable
    sourceClauseCountUnaryComputable


-- @@ L3297-3303 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilyClauseCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyClauseCountUnary
        (encodeThreeCNF formula) =
      List.replicate (noTautClauses formula).length true := by
  simp only [physicalFamilyClauseCountUnary, Function.comp_apply,
      paperVariableArityPhysicalFamilyRetainedSource_valid, sourceClauseCountUnary_valid]


-- @@ L3305-3333 verbatim
private theorem paperVariableArityPhysicalFamilyRetainedVariableCount_eq
    (formula : ThreeCNF) :
    occurringVariableCount
        (noTautClauses formula) =
      paperVariableArityVariableCount formula := by
  classical
  let retained := noTautClauses formula
  have sameVariables :
      (occurringVariables retained).toFinset =
        (paperNormalizedOccurringVariables formula).toFinset := by
    ext name
    simp only [List.mem_toFinset]
    exact (mem_occurringVariables_iff retained name).trans
      ((mem_formulaVariables_iff_exists_literal retained name).trans
        (mem_paperSourceNormalizedOccurringVariables_iff
          formula name).symm)
  unfold occurringVariableCount paperVariableArityVariableCount
  change (occurringVariables retained).length =
    (paperNormalizedOccurringVariables formula).length
  calc
    (occurringVariables retained).length =
        (occurringVariables retained).toFinset.card :=
      (List.toFinset_card_of_nodup
        (occurringVariables_nodup retained)).symm
    _ = (paperNormalizedOccurringVariables formula).toFinset.card :=
      congrArg Finset.card sameVariables
    _ = (paperNormalizedOccurringVariables formula).length :=
      List.toFinset_card_of_nodup
        (paperSourceNormalizedOccurringVariables_nodup formula)


-- @@ L3335-3339 verbatim
/-- GapCVP reduction support. -/
def physicalFamilyVariableCountUnary :
    List Bool → List Bool :=
  compactSourceOccurringVariableCountUnary ∘
    physicalFamilyRetainedSource


-- @@ L3341-3348 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable :
    BitTM
      physicalFamilyVariableCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyRetainedSourceComputable
    compactSourceOccurringVariableCountUnaryComputable


-- @@ L3350-3360 verbatim
@[simp] theorem paperVariableArityPhysicalFamilyVariableCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyVariableCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaVariableCount formula) true := by
  unfold physicalFamilyVariableCountUnary
  rw [Function.comp_apply,
    paperVariableArityPhysicalFamilyRetainedSource_valid,
    compactSourceOccurringVariableCountUnary_valid,
    paperVariableArityPhysicalFamilyRetainedVariableCount_eq]


-- @@ L3362-3367 verbatim
private def physicalFamilySizeUnary
    (input : List Bool) : List Bool :=
  List.replicate 100 true ++
    (sourceInputLengthUnary input ++
    (physicalFamilyVariableCountUnary input ++
      physicalFamilyClauseCountUnary input))


-- @@ L3369-3377 verbatim
private noncomputable def paperVariableArityPhysicalFamilySizeUnaryComputable :
    BitTM
      physicalFamilySizeUnary :=
  pointwiseAppendComputable
    (sourceFixedWordComputable (List.replicate 100 true))
    (pointwiseAppendComputable sourceInputLengthUnaryComputable
      (pointwiseAppendComputable
        paperVariableArityPhysicalFamilyVariableCountUnaryComputable
        physicalFamilyClauseCountUnaryComputable))


-- @@ L3379-3394 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilySizeUnary_valid
    (formula : ThreeCNF) :
    physicalFamilySizeUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSize formula) true := by
  simp only [physicalFamilySizeUnary,
    sourceInputLengthUnary,
    paperVariableArityPhysicalFamilyVariableCountUnary_valid,
    paperVariableArityPhysicalFamilyClauseCountUnary_valid,
    ← List.replicate_add,
    GapCVP.Core.sourceSizeParameter,
    physicalFormulaVariableCount, srcFormula,
    paperSourceNormalizedClauses, List.length_map,
    List.length_attach]
  simp only [Nat.add_assoc]


-- @@ L3396-3401 verbatim
/-- Encode the physical family size raised to the 200th power in unary form. -/
def physicalFamilyPowerTwoHundredUnary :
    List Bool → List Bool :=
  (fun input : List Bool =>
    List.replicate ((Polynomial.X ^ 200).eval input.length) true) ∘
      physicalFamilySizeUnary


-- @@ L3403-3410 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyPowerTwoHundredUnaryComputable :
    BitTM
      physicalFamilyPowerTwoHundredUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilySizeUnaryComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 200))


-- @@ L3412-3420 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilyPowerTwoHundredUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyPowerTwoHundredUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaSize formula ^ 200) true := by
  unfold physicalFamilyPowerTwoHundredUnary
  rw [Function.comp_apply, paperVariableArityPhysicalFamilySizeUnary_valid,
    List.length_replicate, Polynomial.eval_pow, Polynomial.eval_X]


-- @@ L3422-3425 verbatim
/-- GapCVP reduction support. -/
def physicalFamilyFieldCardinalityUnary :
    List Bool → List Bool :=
  nextPowerUnaryOutput physicalFamilyPowerTwoHundredUnary


-- @@ L3427-3433 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable :
    BitTM
      physicalFamilyFieldCardinalityUnary :=
  nextPowerUnaryComputable
    paperVariableArityPhysicalFamilyPowerTwoHundredUnaryComputable


-- @@ L3435-3453 verbatim
@[simp] theorem paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyFieldCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physFieldCard formula) true := by
  unfold physicalFamilyFieldCardinalityUnary
  rw [show physFieldCard formula =
      2 ^ Nat.clog 2 (physicalFormulaSize formula ^ 200) by
    simp only [physFieldCard, physDegree, sourceFieldExponent_eq]]
  apply nextPowerUnaryOutput_valid
    physicalFamilyPowerTwoHundredUnary
    (encodeThreeCNF formula)
    (physicalFormulaSize formula ^ 200)
  · exact paperVariableArityPhysicalFamilyPowerTwoHundredUnary_valid formula
  · have size := GapCVP.Core.sourceSizeParameter_ge_one_hundred
      (encodeThreeCNF formula).length
      (srcFormula formula)
    positivity


-- @@ L3455-3459 verbatim
/-- Encode the physical family field cardinality in binary form. -/
def paperVariableArityPhysicalFamilyFieldCardinalityBinary :
    List Bool → List Bool :=
  (fun input : List Bool => Computability.encodeNat input.length) ∘
    physicalFamilyFieldCardinalityUnary


-- @@ L3461-3468 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldCardinalityBinaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyFieldCardinalityBinary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable
    structuralNaturalBinaryWriterComputable


-- @@ L3470-3474 verbatim
/-- Encode the field bit length of a physical family in unary form. -/
def paperVariableArityPhysicalFamilyFieldBitLengthUnary :
    List Bool → List Bool :=
  sourceInputLengthUnary ∘
    paperVariableArityPhysicalFamilyFieldCardinalityBinary


-- @@ L3476-3483 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldBitLengthUnaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyFieldBitLengthUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldCardinalityBinaryComputable
    sourceInputLengthUnaryComputable


-- @@ L3485-3488 verbatim
/-- GapCVP reduction support. -/
def physicalFamilyFieldDegreeUnary :
    List Bool → List Bool :=
  List.tail ∘ paperVariableArityPhysicalFamilyFieldBitLengthUnary


-- @@ L3490-3497 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable :
    BitTM
      physicalFamilyFieldDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyFieldBitLengthUnaryComputable
    dropHeadComputable


-- @@ L3499-3512 verbatim
@[simp] theorem paperVariableArityPhysicalFamilyFieldDegreeUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyFieldDegreeUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalFamilyFieldDegreeUnary
    paperVariableArityPhysicalFamilyFieldBitLengthUnary
    paperVariableArityPhysicalFamilyFieldCardinalityBinary
    sourceInputLengthUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid]
  simp only [List.length_replicate, encodeNat_length_eq_size, Nat.size_pow, List.replicate_succ,
      List.tail_cons]


-- @@ L3514-3519 verbatim
/-- GapCVP reduction support. -/
def physicalFamilyGridCardinalityUnary :
    List Bool → List Bool :=
  unarySubtractionOutput
    physicalFamilyFieldCardinalityUnary
    physicalFamilyVariableCountUnary


-- @@ L3521-3528 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable :
    BitTM
      physicalFamilyGridCardinalityUnary :=
  unarySubtractionComputable
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable
    paperVariableArityPhysicalFamilyVariableCountUnaryComputable


-- @@ L3530-3544 verbatim
@[simp] theorem paperVariableArityPhysicalFamilyGridCardinalityUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyGridCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physGridCard formula) true := by
  unfold physicalFamilyGridCardinalityUnary
  exact unarySubtractionOutput_valid
    physicalFamilyFieldCardinalityUnary
    physicalFamilyVariableCountUnary
    (encodeThreeCNF formula)
    (physFieldCard formula)
    (physicalFormulaVariableCount formula)
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)
    (paperVariableArityPhysicalFamilyVariableCountUnary_valid formula)


-- @@ L3546-3551 verbatim
/-- Encode the physical family's moment budget in unary form. -/
def paperVariableArityPhysicalFamilyMomentBudgetUnary :
    List Bool → List Bool :=
  (fun input : List Bool =>
    List.replicate ((Polynomial.X ^ 30).eval input.length) true) ∘
      physicalFamilySizeUnary


-- @@ L3553-3560 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyMomentBudgetUnaryComputable :
    BitTM
      paperVariableArityPhysicalFamilyMomentBudgetUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilySizeUnaryComputable
    (polynomialValueUnaryComputable (Polynomial.X ^ 30))


-- @@ L3562-3565 verbatim
/-- GapCVP reduction support. -/
def physicalFamilyMomentCountUnary
    (input : List Bool) : List Bool :=
  true :: paperVariableArityPhysicalFamilyMomentBudgetUnary input


-- @@ L3567-3574 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyMomentCountUnaryComputable :
    BitTM
      physicalFamilyMomentCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyMomentBudgetUnaryComputable
    (prependBitComputable true)


-- @@ L3576-3585 verbatim
@[simp] theorem paperVariableArityPhysicalFamilyMomentCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyMomentCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaMomentCount formula) true := by
  unfold physicalFamilyMomentCountUnary
    paperVariableArityPhysicalFamilyMomentBudgetUnary
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Function.comp_apply,
      paperVariableArityPhysicalFamilySizeUnary_valid, List.length_replicate, List.replicate_succ]


-- @@ L3587-3591 verbatim
/-- Encode the number of physical family tuples in unary form. -/
def physicalFamilyTupleCountUnary :
    List Bool → List Bool :=
  paperSourcePreprocessingField 1 ∘
    paperClauseOffsetOutput


-- @@ L3593-3600 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyTupleCountUnaryComputable :
    BitTM
      physicalFamilyTupleCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityClauseOffsetOutputComputable
    (paperPreprocessingFieldComputable 1)


-- @@ L3602-3611 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilyTupleCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyTupleCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaTupleCount formula) true := by
  unfold physicalFamilyTupleCountUnary
  rw [Function.comp_apply, paperVariableArityClauseOffsetOutput_valid]
  simp only [paperSourcePreprocessingField, paperSourcePreprocessingSuffixAt, Function.iterate_one,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L3613-3616 verbatim
/-- Encode the number of physical family types in unary form. -/
def physicalFamilyTypeCountUnary
    (input : List Bool) : List Bool :=
  true :: physicalFamilyTupleCountUnary input


-- @@ L3618-3625 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalFamilyTypeCountUnaryComputable :
    BitTM
      physicalFamilyTypeCountUnary :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalFamilyTupleCountUnaryComputable
    (prependBitComputable true)


-- @@ L3627-3636 verbatim
@[simp] private theorem paperVariableArityPhysicalFamilyTypeCountUnary_valid
    (formula : ThreeCNF) :
    physicalFamilyTypeCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (1 + physicalFormulaTupleCount formula) true := by
  unfold physicalFamilyTypeCountUnary
  rw [paperVariableArityPhysicalFamilyTupleCountUnary_valid]
  rw [Nat.add_comm]
  rfl


-- @@ L3638-3638 verbatim
end PhysicalFamilyRowTM


-- @@ L3640-3640 verbatim
namespace Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine


-- @@ L3642-3642 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceMachineCert

-- @@ L3643-3643 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L3644-3644 verbatim
open GapCVP.Factor400BinaryConstructiveSourcePlaces

-- @@ L3645-3645 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.FormulaBridge

-- @@ L3646-3646 verbatim
open GapCVP.PhysicalFamilyRowTM

-- @@ L3647-3647 verbatim
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap GapCVP.BinaryRadiusTM


-- @@ L3649-3652 verbatim
/-- Encode the number of one-hot clauses in unary form. -/
def physicalOneHotClauseCountUnary
    (input : List Bool) : List Bool :=
  true :: physicalFamilyClauseCountUnary input


-- @@ L3654-3664 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalOneHotClauseCountUnaryComputable :
    BitTM
      physicalOneHotClauseCountUnary := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    physicalFamilyClauseCountUnaryComputable
    (prependBitComputable true)
  change BitTM
    (fun input => true :: physicalFamilyClauseCountUnary input)
  simpa only [Function.comp_def] using physical


-- @@ L3666-3674 verbatim
@[simp] private theorem paperVariableArityPhysicalOneHotClauseCountUnary_valid
    (formula : ThreeCNF) :
    physicalOneHotClauseCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((noTautClauses formula).length + 1) true := by
  simp only [physicalOneHotClauseCountUnary,
      paperVariableArityPhysicalFamilyClauseCountUnary_valid,
      List.replicate_succ]


-- @@ L3676-3689 verbatim
private theorem paperVariableArityPhysicalFamilyGridCardinalityUnary_eq_actualGrid
    (formula : ThreeCNF) :
    physicalFamilyGridCardinalityUnary
        (encodeThreeCNF formula) =
      List.replicate
        (sourceFormulaGrid (encodeThreeCNF formula).length
          (srcFormula formula)).card true := by
  rw [paperVariableArityPhysicalFamilyGridCardinalityUnary_valid]
  congr 1
  simpa only [physGridCard, physFieldCard, physDegree, physicalFormulaSize,
      physicalFormulaVariableCount,
      paperVariableAritySourceFormula_variableCount] using
      (sourceFormulaGrid_card_eq_fieldWordCount (encodeThreeCNF formula).length (srcFormula
          formula)).symm


-- @@ L3691-3695 verbatim
/-- GapCVP reduction support. -/
def physicalOneHotWeightUnary : List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    physicalOneHotClauseCountUnary
    physicalFamilyGridCardinalityUnary


-- @@ L3697-3704 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalOneHotWeightUnaryComputable :
    BitTM
      physicalOneHotWeightUnary :=
  fourFamilyComputedUnaryProductComputable
    paperVariableArityPhysicalOneHotClauseCountUnaryComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable


-- @@ L3706-3724 verbatim
@[simp] theorem paperVariableArityPhysicalOneHotWeightUnary_valid
    (formula : ThreeCNF) :
    physicalOneHotWeightUnary
        (encodeThreeCNF formula) =
      List.replicate
        (((noTautClauses formula).length + 1) *
          (sourceFormulaGrid (encodeThreeCNF formula).length
            (srcFormula formula)).card)
        true := by
  exact fourFamilyComputedUnaryProductOutput_valid
    physicalOneHotClauseCountUnary
    physicalFamilyGridCardinalityUnary
    (encodeThreeCNF formula)
    ((noTautClauses formula).length + 1)
    (sourceFormulaGrid (encodeThreeCNF formula).length
      (srcFormula formula)).card
    (paperVariableArityPhysicalOneHotClauseCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_eq_actualGrid
      formula)


-- @@ L3726-3729 verbatim
/-- Compute the atomic physical radius output of the variable-arity source. -/
def paperVariableArityPhysicalRadiusAtomicOutput : List Bool → List Bool :=
  ceilSquareRootAtomicRationalOutput
    physicalOneHotWeightUnary


-- @@ L3731-3737 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalRadiusAtomicComputable :
    BitTM
      paperVariableArityPhysicalRadiusAtomicOutput :=
  ceilSquareRootAtomicRationalComputable
    paperVariableArityPhysicalOneHotWeightUnaryComputable


-- @@ L3739-3756 verbatim
@[simp] private theorem paperVariableArityPhysicalRadiusAtomicOutput_valid
    (formula : ThreeCNF) :
    paperVariableArityPhysicalRadiusAtomicOutput
        (encodeThreeCNF formula) =
      encodeAtomic
        (physicalFormulaRadius
          (encodeThreeCNF formula).length formula) := by
  unfold paperVariableArityPhysicalRadiusAtomicOutput
  rw [ceilSquareRootAtomicRationalOutput_valid
    physicalOneHotWeightUnary
    (encodeThreeCNF formula)
    (((noTautClauses formula).length + 1) *
      (sourceFormulaGrid (encodeThreeCNF formula).length
        (srcFormula formula)).card)
    (paperVariableArityPhysicalOneHotWeightUnary_valid formula)]
  unfold physicalFormulaRadius
    GapCVP.Core.sourceOneHotCompletenessRadius
  rw [paperVariableAritySourceFormula_clauses_length]


-- @@ L3758-3758 verbatim
end Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine


-- @@ L3760-3760 verbatim
namespace PhysicalNormalizedBranchTM


-- @@ L3762-3762 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure

-- @@ L3763-3763 verbatim
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM

-- @@ L3764-3764 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.BinarySourceTautologyNormalizationExact

-- @@ L3765-3765 verbatim
open GapCVP.SourcePreprocessingSemantics GapCVP.PhysicalFamilyRowTM GapCVP.GaussianRowWorker

-- @@ L3766-3766 verbatim
open GapCVP.Factor400BinaryPhysicalWorkers


-- @@ L3768-3771 verbatim
/-- GapCVP reduction support. -/
def physicalNormalizedNonemptyMarker
    (input : List Bool) : Bool :=
  (physicalFamilyClauseCountUnary input).headD false


-- @@ L3773-3777 verbatim
/-- Encode the normalized nonempty-case decision bit. -/
def physicalNormalizedNonemptyDecisionWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    physicalFamilyClauseCountUnary


-- @@ L3779-3786 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable :
    BitTM
      physicalNormalizedNonemptyDecisionWord :=
  GapCVP.TMComposition.computableInPolyTime
    physicalFamilyClauseCountUnaryComputable
    binaryGaussianFirstCellComputable


-- @@ L3788-3801 verbatim
private theorem paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq
    (input : List Bool) :
    physicalNormalizedNonemptyDecisionWord input =
      [physicalNormalizedNonemptyMarker input] := by
  unfold physicalNormalizedNonemptyDecisionWord
    physicalNormalizedNonemptyMarker
  cases hcount : physicalFamilyClauseCountUnary input with
  | nil =>
      simp only [binaryGaussianFirstCellWord, Function.comp_apply, markerConditionalOutput, hcount,
          List.headD_eq_head?_getD, List.head?_nil, Option.getD_none]
  | cons bit remaining =>
      simp only [Function.comp_apply, hcount, binaryGaussianFirstCellWord_valid,
          List.headD_eq_head?_getD,
          List.head?_cons, Option.getD_some]


-- @@ L3803-3820 verbatim
@[simp] theorem paperVariableArityPhysicalNormalizedNonemptyMarker_valid
    (formula : ThreeCNF) :
    physicalNormalizedNonemptyMarker
        (encodeThreeCNF formula) =
      decide (paperSourceNormalizedClauses formula ≠ []) := by
  unfold physicalNormalizedNonemptyMarker
  rw [paperVariableArityPhysicalFamilyClauseCountUnary_valid]
  cases hretained : noTautClauses formula with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.headD_eq_head?_getD, List.head?_nil,
          Option.getD_none,
          paperSourceNormalizedClauses, hretained, List.map_nil, ne_eq, not_true_eq_false,
              decide_false]
  | cons clause remaining =>
      simp only [List.length_cons, List.replicate_succ, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some,
          paperSourceNormalizedClauses, hretained, List.map_cons, ne_eq, reduceCtorEq,
              not_false_eq_true, decide_true]


-- @@ L3822-3826 verbatim
/-- Encode the normalized empty-case decision bit. -/
def physicalNormalizedEmptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    physicalNormalizedNonemptyDecisionWord


-- @@ L3828-3834 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalNormalizedEmptyDecisionComputable :
    BitTM
      physicalNormalizedEmptyDecisionWord :=
  fourFamilyBooleanNotOutputComputable
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable


-- @@ L3836-3840 verbatim
/-- Encode the canonical physical decision bit. -/
def physicalCanonicalDecisionWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    (fun input => constructiveCanonicalSourceMarker input :: input)


-- @@ L3842-3849 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalDecisionComputable :
    BitTM
      physicalCanonicalDecisionWord :=
  GapCVP.TMComposition.computableInPolyTime
    constructiveCanonicalSourceMarkerComputable
    binaryGaussianFirstCellComputable


-- @@ L3851-3855 verbatim
@[simp] private theorem paperVariableArityPhysicalCanonicalDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalDecisionWord input =
      [constructiveCanonicalSourceMarker input] := by
  simp only [physicalCanonicalDecisionWord, Function.comp_apply, binaryGaussianFirstCellWord_valid]


-- @@ L3857-3861 verbatim
/-- GapCVP reduction support. -/
def physicalCanonicalNormalizedNonemptyGuard
    (input : List Bool) : Bool :=
  constructiveCanonicalSourceMarker input &&
    physicalNormalizedNonemptyMarker input


-- @@ L3863-3868 verbatim
/-- Encode the canonical normalized nonempty-case decision bit. -/
def physicalCanonicalNormalizedNonemptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalCanonicalDecisionWord
    physicalNormalizedNonemptyDecisionWord


-- @@ L3870-3877 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionComputable :
    BitTM
      physicalCanonicalNormalizedNonemptyDecisionWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalCanonicalDecisionComputable
    paperVariableArityPhysicalNormalizedNonemptyDecisionComputable


-- @@ L3879-3891 verbatim
private theorem paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalNormalizedNonemptyDecisionWord input =
      [physicalCanonicalNormalizedNonemptyGuard input] := by
  unfold physicalCanonicalNormalizedNonemptyDecisionWord
    physicalCanonicalNormalizedNonemptyGuard
  exact fourFamilyBooleanAndOutput_bits
    physicalCanonicalDecisionWord
    physicalNormalizedNonemptyDecisionWord
    input (constructiveCanonicalSourceMarker input)
    (physicalNormalizedNonemptyMarker input)
    (paperVariableArityPhysicalCanonicalDecisionWord_eq input)
    (paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq input)


-- @@ L3893-3898 verbatim
/-- Select the canonical normalized nonempty-case output. -/
def physicalCanonicalNormalizedNonemptySelectionOutput :
    List Bool → List Bool :=
  factor400KeepFirstDropSecondWord ∘
    originalSourcePreservingOutput
      physicalCanonicalNormalizedNonemptyDecisionWord


-- @@ L3900-3907 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyPreservedComputable :
    BitTM
      (originalSourcePreservingOutput
        physicalCanonicalNormalizedNonemptyDecisionWord) :=
  originalSourcePreservingComputable
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionComputable


-- @@ L3909-3916 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionComputable :
    BitTM
      physicalCanonicalNormalizedNonemptySelectionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalCanonicalNormalizedNonemptyPreservedComputable
    factor400KeepFirstDropSecondComputable


-- @@ L3918-3929 verbatim
private theorem paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionOutput_eq
    (input : List Bool) :
    physicalCanonicalNormalizedNonemptySelectionOutput
        input =
      physicalCanonicalNormalizedNonemptyGuard input ::
        input := by
  unfold physicalCanonicalNormalizedNonemptySelectionOutput
    originalSourcePreservingOutput
  rw [Function.comp_apply,
    paperVariableArityPhysicalCanonicalNormalizedNonemptyDecisionWord_eq
      input]
  simp only [factor400KeepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons]


-- @@ L3931-3931 verbatim
end PhysicalNormalizedBranchTM


-- @@ L3933-3933 verbatim
namespace PhysicalNormalizedCanonicalGuardTM


-- @@ L3935-3935 verbatim
open Turing GapCVP.SourceOriginalSourcePreservingTM GapCVP.SourceWholeOutputAssemblyTM

-- @@ L3936-3936 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM GapCVP.PhysicalNormalizedBranchTM

-- @@ L3937-3937 verbatim
open GapCVP.Factor400BinaryPhysicalWorkers


-- @@ L3939-3942 verbatim
/-- GapCVP reduction support. -/
def physicalNormalizedEmptyMarker
    (input : List Bool) : Bool :=
  !physicalNormalizedNonemptyMarker input


-- @@ L3944-3953 verbatim
private theorem paperVariableArityPhysicalNormalizedEmptyDecisionWord_eq
    (input : List Bool) :
    physicalNormalizedEmptyDecisionWord input =
      [physicalNormalizedEmptyMarker input] := by
  unfold physicalNormalizedEmptyDecisionWord
    physicalNormalizedEmptyMarker
  exact fourFamilyBooleanNotOutput_bit
    physicalNormalizedNonemptyDecisionWord input
    (physicalNormalizedNonemptyMarker input)
    (paperVariableArityPhysicalNormalizedNonemptyDecisionWord_eq input)


-- @@ L3955-3959 verbatim
/-- GapCVP reduction support. -/
def physicalCanonicalNormalizedEmptyGuard
    (input : List Bool) : Bool :=
  constructiveCanonicalSourceMarker input &&
    physicalNormalizedEmptyMarker input


-- @@ L3961-3966 verbatim
/-- Encode the canonical normalized empty-case decision bit. -/
def physicalCanonicalNormalizedEmptyDecisionWord :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalCanonicalDecisionWord
    physicalNormalizedEmptyDecisionWord


-- @@ L3968-3975 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionComputable :
    BitTM
      physicalCanonicalNormalizedEmptyDecisionWord :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalCanonicalDecisionComputable
    paperVariableArityPhysicalNormalizedEmptyDecisionComputable


-- @@ L3977-3989 verbatim
private theorem paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionWord_eq
    (input : List Bool) :
    physicalCanonicalNormalizedEmptyDecisionWord input =
      [physicalCanonicalNormalizedEmptyGuard input] := by
  unfold physicalCanonicalNormalizedEmptyDecisionWord
    physicalCanonicalNormalizedEmptyGuard
  exact fourFamilyBooleanAndOutput_bits
    physicalCanonicalDecisionWord
    physicalNormalizedEmptyDecisionWord input
    (constructiveCanonicalSourceMarker input)
    (physicalNormalizedEmptyMarker input)
    (paperVariableArityPhysicalCanonicalDecisionWord_eq input)
    (paperVariableArityPhysicalNormalizedEmptyDecisionWord_eq input)


-- @@ L3991-3996 verbatim
/-- Select the canonical normalized empty-case output. -/
def physicalCanonicalNormalizedEmptySelectionOutput :
    List Bool → List Bool :=
  factor400KeepFirstDropSecondWord ∘
    originalSourcePreservingOutput
      physicalCanonicalNormalizedEmptyDecisionWord


-- @@ L3998-4005 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyPreservedComputable :
    BitTM
      (originalSourcePreservingOutput
        physicalCanonicalNormalizedEmptyDecisionWord) :=
  originalSourcePreservingComputable
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionComputable


-- @@ L4007-4014 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptySelectionComputable :
    BitTM
      physicalCanonicalNormalizedEmptySelectionOutput :=
  GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalCanonicalNormalizedEmptyPreservedComputable
    factor400KeepFirstDropSecondComputable


-- @@ L4016-4025 verbatim
private theorem paperVariableArityPhysicalCanonicalNormalizedEmptySelectionOutput_eq
    (input : List Bool) :
    physicalCanonicalNormalizedEmptySelectionOutput input =
      physicalCanonicalNormalizedEmptyGuard input ::
        input := by
  unfold physicalCanonicalNormalizedEmptySelectionOutput
    originalSourcePreservingOutput
  rw [Function.comp_apply,
    paperVariableArityPhysicalCanonicalNormalizedEmptyDecisionWord_eq input]
  simp only [factor400KeepFirstDropSecondWord, List.cons_append, List.nil_append, List.tail_cons]


-- @@ L4027-4041 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedEmptyGuardComputable :
    BitTM
      (fun input =>
        physicalCanonicalNormalizedEmptyGuard input ::
          input) := by
  have equality :
      physicalCanonicalNormalizedEmptySelectionOutput =
        (fun input =>
          physicalCanonicalNormalizedEmptyGuard input ::
            input) :=
    funext paperVariableArityPhysicalCanonicalNormalizedEmptySelectionOutput_eq
  rw [← equality]
  exact paperVariableArityPhysicalCanonicalNormalizedEmptySelectionComputable


-- @@ L4043-4057 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalCanonicalNormalizedNonemptyGuardComputable :
    BitTM
      (fun input =>
        physicalCanonicalNormalizedNonemptyGuard input ::
          input) := by
  have equality :
      physicalCanonicalNormalizedNonemptySelectionOutput =
        (fun input =>
          physicalCanonicalNormalizedNonemptyGuard input ::
            input) :=
    funext paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionOutput_eq
  rw [← equality]
  exact paperVariableArityPhysicalCanonicalNormalizedNonemptySelectionComputable


-- @@ L4059-4059 verbatim
end PhysicalNormalizedCanonicalGuardTM


-- @@ L4061-4061 verbatim
namespace GaussianExactSourceInitializer


-- @@ L4063-4063 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure

-- @@ L4064-4064 verbatim
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder

-- @@ L4065-4065 verbatim
open GapCVP.GaussianSourceConsistencyBridge GapCVP.GaussianSourceInitializerInstantiation


-- @@ L4067-4076 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperCanonicalSourceBinarySystem
    (input : List Bool) : Option BinaryAffineSystem :=
  match decodeThreeCNF input with
  | none => none
  | some formula =>
      if encodeThreeCNF formula = input then
        some (physicalWordBinarySystem input.length formula)
      else
        none


-- @@ L4078-4084 verbatim
@[simp] private theorem paperVariableArityCanonicalSourceBinarySystem_encode
    (formula : ThreeCNF) :
    paperCanonicalSourceBinarySystem
        (encodeThreeCNF formula) =
      some (physicalWordBinarySystem
        (encodeThreeCNF formula).length formula) := by
  simp only [paperCanonicalSourceBinarySystem, decodeThreeCNF_encode, ↓reduceIte]


-- @@ L4086-4095 verbatim
/-- Compute the exact reduced state of a variable-arity source. -/
def gaussianPaperVariableArityExactSourceReducedStateOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  if constructiveCanonicalSourceMarker input then
    gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
      worker input
  else
    binaryGaussianMalformedReducedState


-- @@ L4097-4115 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityExactSourceReducedStateComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (gaussianPaperVariableArityExactSourceReducedStateOutput worker) := by
  change BitTM
    (fun input =>
      if constructiveCanonicalSourceMarker input then
        gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput
          worker input
      else
        binaryGaussianMalformedReducedState)
  exact sourcePreservingConditionalComputable
    constructiveCanonicalSourceMarkerComputable
    (gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryComputable
      worker)
    binaryGaussianMalformedReducedState


-- @@ L4117-4144 verbatim
private theorem gaussianPaperVariableArityExactSourceReducedStateOutput_eq
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    gaussianPaperVariableArityExactSourceReducedStateOutput worker input =
      binaryGaussianExpectedReducedSourceState
        paperCanonicalSourceBinarySystem input := by
  cases hdecode : decodeThreeCNF input with
  | none =>
      simp only [gaussianPaperVariableArityExactSourceReducedStateOutput,
          constructiveCanonicalSourceMarker,
          hdecode, Bool.false_eq_true, ↓reduceIte, binaryGaussianExpectedReducedSourceState,
              paperCanonicalSourceBinarySystem]
  | some formula =>
      by_cases hcanonical : encodeThreeCNF formula = input
      · subst input
        simpa only [gaussianPaperVariableArityExactSourceReducedStateOutput,
            constructiveCanonicalSourceMarker,
            decodeThreeCNF_encode, decide_true, ↓reduceIte,
                binaryGaussianExpectedReducedSourceState,
            paperCanonicalSourceBinarySystem] using
            gaussianPaperVariableArityCanonicalSourceReducedConsistencyQueryOutput_valid worker
                formula
      · simp only [gaussianPaperVariableArityExactSourceReducedStateOutput,
          constructiveCanonicalSourceMarker,
            hdecode, hcanonical, decide_false, Bool.false_eq_true, ↓reduceIte,
                binaryGaussianExpectedReducedSourceState,
            paperCanonicalSourceBinarySystem]


-- @@ L4146-4153 verbatim
@[irreducible] private noncomputable def gaussianPaperVariableArityExactSourceInitializer
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BinaryGaussianExactSourceInitializer
      paperCanonicalSourceBinarySystem where
  output := gaussianPaperVariableArityExactSourceReducedStateOutput worker
  computer := gaussianPaperVariableArityExactSourceReducedStateComputable worker
  output_eq := gaussianPaperVariableArityExactSourceReducedStateOutput_eq worker


-- @@ L4155-4159 verbatim
/-- Compute exact Gaussian consistency on every source input. -/
@[expose] def gaussianPaperVariableArityAllInputExactConsistencyOutput
    (input : List Bool) : List Bool :=
  binaryGaussianSourceConsistencyGuard
      paperCanonicalSourceBinarySystem input :: input


-- @@ L4161-4169 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    gaussianPaperVariableArityAllInputExactConsistencyComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (worker : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      gaussianPaperVariableArityAllInputExactConsistencyOutput :=
  binaryGaussianExactSourceConsistencyComputable
    (gaussianPaperVariableArityExactSourceInitializer worker)


-- @@ L4171-4171 verbatim
end GaussianExactSourceInitializer


-- @@ L4173-4173 verbatim
namespace ExactPhysicalSourceTM


-- @@ L4175-4175 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L4176-4176 verbatim
open GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceWholeOutputAssemblyTM

-- @@ L4177-4177 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge

-- @@ L4178-4178 verbatim
open GapCVP.SourcePreprocessingSemantics GapCVP.CanonicalMatrixShape

-- @@ L4179-4179 verbatim
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap

-- @@ L4180-4180 verbatim
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM

-- @@ L4181-4181 verbatim
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine

-- @@ L4182-4182 verbatim
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation

-- @@ L4183-4183 verbatim
open GapCVP.GaussianOutputSerializerTM


-- @@ L4185-4192 verbatim
/-- Compute the exact physical structural output. -/
noncomputable def paperExactPhysicalStructuralOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  paperGaussianStructuralSourceWord shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)


-- @@ L4194-4203 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityExactPhysicalStructuralOutputComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperExactPhysicalStructuralOutput cell) :=
  paperVariableArityGaussianStructuralSourceWordComputable shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)


-- @@ L4205-4226 verbatim
private theorem paperVariableArityExactPhysicalStructuralOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperExactPhysicalStructuralOutput cell
        (encodeThreeCNF formula) =
      encodeGapCVPInstance
        (physicalFormulaInstance
          (encodeThreeCNF formula).length formula) := by
  unfold paperExactPhysicalStructuralOutput
  exact paperVariableArityGaussianStructuralSourceWord_eq_encodeGapCVPInstance
    shape
    paperVariableArityPhysicalRadiusAtomicComputable
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)
    formula
    (physicalFormulaRadius
      (encodeThreeCNF formula).length formula)
    (physicalFormulaRadius_pos
      (encodeThreeCNF formula).length formula)
    (paperVariableArityPhysicalRadiusAtomicOutput_valid formula)
    (gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
      cell formula)


-- @@ L4228-4242 verbatim
/-- Route the exact physical output through its selected branch. -/
def paperExactPhysicalRoutedOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  if physicalCanonicalNormalizedEmptyGuard input then
    SourceMachineRouting.canonicalYesWord
  else if physicalCanonicalNormalizedNonemptyGuard input then
    if binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem input then
      paperExactPhysicalStructuralOutput cell input
    else
      Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  else
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord


-- @@ L4244-4262 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityExactPhysicalRoutedOutputComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperExactPhysicalRoutedOutput cell) := by
  have consistency := sourcePreservingConditionalComputable
    (gaussianPaperVariableArityAllInputExactConsistencyComputable cell)
    (paperVariableArityExactPhysicalStructuralOutputComputable cell)
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  have nonempty := sourcePreservingConditionalComputable
    paperVariableArityPhysicalCanonicalNormalizedNonemptyGuardComputable
    consistency Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  have routed := binaryGaussianDynamicBranchComputable
    paperVariableArityPhysicalCanonicalNormalizedEmptyGuardComputable
    (sourceFixedWordComputable SourceMachineRouting.canonicalYesWord)
    nonempty
  exact routed


-- @@ L4264-4273 verbatim
@[simp] theorem paperVariableArityExactPhysicalConsistencyGuard_encode
    (formula : ThreeCNF) :
    binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem
        (encodeThreeCNF formula) =
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).effectiveReducedConsistent := by
  unfold binaryGaussianSourceConsistencyGuard
  rw [paperVariableArityCanonicalSourceBinarySystem_encode]
  rfl


-- @@ L4275-4349 verbatim
/-- Identifies the shared physical routing tree from its five semantic branches. -/
theorem physicalRoutedOutput_eq_sourceMap
    (structuralOutput sourceMap : List Bool → List Bool) (noWord : List Bool)
    (decodeNone : ∀ input, decodeThreeCNF input = none → noWord = sourceMap input)
    (noncanonical : ∀ input formula, decodeThreeCNF input = some formula →
      encodeThreeCNF formula ≠ input → noWord = sourceMap input)
    (normalizedEmpty : ∀ formula, paperSourceNormalizedClauses formula = [] →
      SourceMachineRouting.canonicalYesWord = sourceMap (encodeThreeCNF formula))
    (inconsistent : ∀ formula, paperSourceNormalizedClauses formula ≠ [] →
      (physicalFormulaSystem (encodeThreeCNF formula).length
        formula).effectiveReducedConsistent = false →
      noWord = sourceMap (encodeThreeCNF formula))
    (consistent : ∀ formula, paperSourceNormalizedClauses formula ≠ [] →
      (physicalFormulaSystem (encodeThreeCNF formula).length
        formula).effectiveReducedConsistent = true →
      structuralOutput (encodeThreeCNF formula) = sourceMap (encodeThreeCNF formula))
    (input : List Bool) :
    (if physicalCanonicalNormalizedEmptyGuard input then
      SourceMachineRouting.canonicalYesWord
    else if physicalCanonicalNormalizedNonemptyGuard input then
      if binaryGaussianSourceConsistencyGuard paperCanonicalSourceBinarySystem input then
        structuralOutput input
      else noWord
    else noWord) = sourceMap input := by
  cases decoded : decodeThreeCNF input with
  | none =>
      have canonical : constructiveCanonicalSourceMarker input = false := by
        simp only [constructiveCanonicalSourceMarker, decoded]
      have empty : physicalCanonicalNormalizedEmptyGuard input = false := by
        simp only [physicalCanonicalNormalizedEmptyGuard, canonical, Bool.false_and]
      have nonempty : physicalCanonicalNormalizedNonemptyGuard input = false := by
        simp only [physicalCanonicalNormalizedNonemptyGuard, canonical, Bool.false_and]
      simpa only [empty, Bool.false_eq_true, ↓reduceIte, nonempty] using
        decodeNone input decoded
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · subst input
        by_cases empty : paperSourceNormalizedClauses formula = []
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true, physicalNormalizedEmptyMarker,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, empty, ne_eq,
              not_true_eq_false, decide_false, Bool.not_false, Bool.and_self]
          simpa only [emptyGuard, ↓reduceIte] using normalizedEmpty formula empty
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard (encodeThreeCNF formula) = false := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true, physicalNormalizedEmptyMarker,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq, empty,
              not_false_eq_true, Bool.not_true, Bool.and_false]
          have nonemptyGuard :
              physicalCanonicalNormalizedNonemptyGuard (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedNonemptyGuard, constructiveCanonicalSourceMarker,
              decodeThreeCNF_encode, decide_true,
              paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq, empty,
              not_false_eq_true, Bool.and_self]
          cases consistency : (physicalFormulaSystem
              (encodeThreeCNF formula).length formula).effectiveReducedConsistent with
          | false =>
              simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode, consistency] using
                inconsistent formula empty consistency
          | true =>
              simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode, consistency] using
                consistent formula empty consistency
      · have sourceGuard : constructiveCanonicalSourceMarker input = false := by
          simp only [constructiveCanonicalSourceMarker, decoded, canonical, decide_false]
        have emptyGuard : physicalCanonicalNormalizedEmptyGuard input = false := by
          simp only [physicalCanonicalNormalizedEmptyGuard, sourceGuard, Bool.false_and]
        have nonemptyGuard : physicalCanonicalNormalizedNonemptyGuard input = false := by
          simp only [physicalCanonicalNormalizedNonemptyGuard, sourceGuard, Bool.false_and]
        simpa only [emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard] using
          noncanonical input formula decoded canonical


-- @@ L4351-4387 verbatim
private theorem paperVariableArityExactPhysicalRoutedOutput_eq_sourceMap
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    paperExactPhysicalRoutedOutput cell input =
      paperVariableArityPhysicalSourceMap input := by
  unfold paperExactPhysicalRoutedOutput
  apply physicalRoutedOutput_eq_sourceMap
    (paperExactPhysicalStructuralOutput cell)
    paperVariableArityPhysicalSourceMap
    Factor400BinaryCanonicalNo.adaptedCanonicalNoWord
  · intro source decode
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_decode_none source decode]
    rfl
  · intro source formula decode noncanonical
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_noncanonical
      source formula decode noncanonical]
    rfl
  · intro formula empty
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_normalized_empty
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode]) rfl empty]
    rfl
  · intro formula nonempty inconsistent
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_inconsistent
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode])
      rfl nonempty inconsistent]
    rfl
  · intro formula nonempty consistent
    unfold paperVariableArityPhysicalSourceMap
    rw [paperVariableArityPhysicalSourceInstance_of_consistent
      (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode])
      rfl nonempty consistent]
    exact paperVariableArityExactPhysicalStructuralOutput_valid cell formula


-- @@ L4389-4401 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityPhysicalSourceMapMachineOfCell
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      paperVariableArityPhysicalSourceMap := by
  have machine := paperVariableArityExactPhysicalRoutedOutputComputable cell
  have equality :
      paperExactPhysicalRoutedOutput cell =
        paperVariableArityPhysicalSourceMap :=
    funext (paperVariableArityExactPhysicalRoutedOutput_eq_sourceMap cell)
  rwa [equality] at machine


-- @@ L4403-4403 verbatim
end ExactPhysicalSourceTM


-- @@ L4405-4405 verbatim
namespace PhysicalFamilyMarkerTM


-- @@ L4407-4407 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L4408-4408 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM GapCVP.BinaryExplicitAffineRows

-- @@ L4409-4409 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.PhysicalFamilyRowTM


-- @@ L4411-4415 verbatim
private def physicalGlobalBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    physicalFamilyGridCardinalityUnary
    physicalFamilyFieldDegreeUnary


-- @@ L4417-4422 verbatim
private noncomputable def paperVariableArityPhysicalGlobalBoundaryUnaryComputable :
    BitTM
      physicalGlobalBoundaryUnary :=
  fourFamilyComputedUnaryProductComputable
    paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable


-- @@ L4424-4438 verbatim
@[simp] private theorem paperVariableArityPhysicalGlobalBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalGlobalBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaGlobalBoundary formula) true := by
  unfold physicalGlobalBoundaryUnary
  exact fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyGridCardinalityUnary
    physicalFamilyFieldDegreeUnary
    (encodeThreeCNF formula)
    (physGridCard formula)
    (physDegree formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)


-- @@ L4440-4448 verbatim
private def physicalRefinementWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyClauseCountUnary
        physicalFamilyGridCardinalityUnary)
      physicalFamilyFieldCardinalityUnary)
    physicalFamilyFieldDegreeUnary


-- @@ L4450-4459 verbatim
private noncomputable def paperVariableArityPhysicalRefinementWidthUnaryComputable :
    BitTM
      physicalRefinementWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        physicalFamilyClauseCountUnaryComputable
        paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
      paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable


-- @@ L4461-4500 verbatim
@[simp] private theorem paperVariableArityPhysicalRefinementWidthUnary_valid
    (formula : ThreeCNF) :
    physicalRefinementWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((noTautClauses formula).length *
          physGridCard formula *
          physFieldCard formula *
          physDegree formula) true := by
  let input := encodeThreeCNF formula
  have clauseGrid := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyClauseCountUnary
    physicalFamilyGridCardinalityUnary input
    (noTautClauses formula).length
    (physGridCard formula)
    (paperVariableArityPhysicalFamilyClauseCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  have field := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyClauseCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary input
    ((noTautClauses formula).length *
      physGridCard formula)
    (physFieldCard formula)
    clauseGrid
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyClauseCountUnary
        physicalFamilyGridCardinalityUnary)
      physicalFamilyFieldCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    ((noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula)
    (physDegree formula)
    field
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)


-- @@ L4502-4507 verbatim
/-- Encode the physical refinement boundary in unary form. -/
def physicalRefinementBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalGlobalBoundaryUnary
    physicalRefinementWidthUnary


-- @@ L4509-4516 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable :
    BitTM
      physicalRefinementBoundaryUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalGlobalBoundaryUnaryComputable
    paperVariableArityPhysicalRefinementWidthUnaryComputable


-- @@ L4518-4536 verbatim
@[simp] private theorem paperVariableArityPhysicalRefinementBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalRefinementBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaRefinementBoundary formula)
        true := by
  unfold physicalRefinementBoundaryUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalGlobalBoundaryUnary
    physicalRefinementWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaGlobalBoundary formula)
    ((noTautClauses formula).length *
      physGridCard formula *
      physFieldCard formula *
      physDegree formula)
    (paperVariableArityPhysicalGlobalBoundaryUnary_valid formula)
    (paperVariableArityPhysicalRefinementWidthUnary_valid formula)


-- @@ L4538-4546 verbatim
private def physicalOrdinaryWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyTypeCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary


-- @@ L4548-4557 verbatim
private noncomputable def paperVariableArityPhysicalOrdinaryWidthUnaryComputable :
    BitTM
      physicalOrdinaryWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        paperVariableArityPhysicalFamilyTypeCountUnaryComputable
        paperVariableArityPhysicalFamilyMomentCountUnaryComputable)
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable


-- @@ L4559-4598 verbatim
@[simp] private theorem paperVariableArityPhysicalOrdinaryWidthUnary_valid
    (formula : ThreeCNF) :
    physicalOrdinaryWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        ((1 + physicalFormulaTupleCount formula) *
          physicalFormulaMomentCount formula *
          physGridCard formula *
          physDegree formula) true := by
  let input := encodeThreeCNF formula
  have tagMoment := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyTypeCountUnary
    physicalFamilyMomentCountUnary input
    (1 + physicalFormulaTupleCount formula)
    (physicalFormulaMomentCount formula)
    (paperVariableArityPhysicalFamilyTypeCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyMomentCountUnary_valid formula)
  have grid := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyMomentCountUnary)
    physicalFamilyGridCardinalityUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula)
    (physGridCard formula)
    tagMoment
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalFamilyTypeCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula)
    (physDegree formula)
    grid
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)


-- @@ L4600-4604 verbatim
private def physicalOrdinaryBoundaryUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalRefinementBoundaryUnary
    physicalOrdinaryWidthUnary


-- @@ L4606-4611 verbatim
private noncomputable def paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable :
    BitTM
      physicalOrdinaryBoundaryUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable
    paperVariableArityPhysicalOrdinaryWidthUnaryComputable


-- @@ L4613-4631 verbatim
@[simp] private theorem paperVariableArityPhysicalOrdinaryBoundaryUnary_valid
    (formula : ThreeCNF) :
    physicalOrdinaryBoundaryUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaOrdinaryBoundary formula)
        true := by
  unfold physicalOrdinaryBoundaryUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalRefinementBoundaryUnary
    physicalOrdinaryWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaRefinementBoundary formula)
    ((1 + physicalFormulaTupleCount formula) *
      physicalFormulaMomentCount formula *
      physGridCard formula *
      physDegree formula)
    (paperVariableArityPhysicalRefinementBoundaryUnary_valid formula)
    (paperVariableArityPhysicalOrdinaryWidthUnary_valid formula)


-- @@ L4633-4636 verbatim
/-- GapCVP reduction support. -/
def physicalCellSourceLift
    (worker : List Bool → List Bool) : List Bool → List Bool :=
  worker ∘ sourceExplicitAffineCellOriginalSource


-- @@ L4638-4645 verbatim
/-- GapCVP reduction support. -/
noncomputable def physicalCellSourceLiftComputable
    {worker : List Bool → List Bool}
    (computer : BitTM worker) :
    BitTM
      (physicalCellSourceLift worker) :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable computer


-- @@ L4647-4655 verbatim
@[simp] theorem paperVariableArityPhysicalCellSourceLift_query
    (worker : List Bool → List Bool)
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellSourceLift worker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      worker (encodeThreeCNF formula) := by
  simp only [physicalCellSourceLift, Function.comp_apply,
      sourceExplicitAffineCellOriginalSource_query]


-- @@ L4657-4661 verbatim
/-- GapCVP reduction support. -/
def physicalCellGlobalBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalGlobalBoundaryUnary


-- @@ L4663-4669 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable :
    BitTM
      physicalCellGlobalBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalGlobalBoundaryUnaryComputable


-- @@ L4671-4680 verbatim
@[simp] theorem paperVariableArityPhysicalCellGlobalBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellGlobalBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaGlobalBoundary formula) true := by
  unfold physicalCellGlobalBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalGlobalBoundaryUnary_valid]


-- @@ L4682-4686 verbatim
/-- GapCVP reduction support. -/
def physicalCellRefinementBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalRefinementBoundaryUnary


-- @@ L4688-4694 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellRefinementBoundaryUnaryComputable :
    BitTM
      physicalCellRefinementBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalRefinementBoundaryUnaryComputable


-- @@ L4696-4706 verbatim
@[simp] theorem paperVariableArityPhysicalCellRefinementBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellRefinementBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaRefinementBoundary formula)
        true := by
  unfold physicalCellRefinementBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalRefinementBoundaryUnary_valid]


-- @@ L4708-4712 verbatim
/-- GapCVP reduction support. -/
def physicalCellOrdinaryBoundaryUnary :
    List Bool → List Bool :=
  physicalCellSourceLift
    physicalOrdinaryBoundaryUnary


-- @@ L4714-4720 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalCellOrdinaryBoundaryUnaryComputable :
    BitTM
      physicalCellOrdinaryBoundaryUnary :=
  physicalCellSourceLiftComputable
    paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable


-- @@ L4722-4732 verbatim
@[simp] theorem paperVariableArityPhysicalCellOrdinaryBoundaryUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalCellOrdinaryBoundaryUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physicalFormulaOrdinaryBoundary formula)
        true := by
  unfold physicalCellOrdinaryBoundaryUnary
  rw [paperVariableArityPhysicalCellSourceLift_query,
    paperVariableArityPhysicalOrdinaryBoundaryUnary_valid]


-- @@ L4734-4738 verbatim
/-- Tests whether a physical row precedes the global-family boundary. -/
def physicalRowBeforeGlobal : List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary


-- @@ L4740-4745 verbatim
private noncomputable def paperVariableArityPhysicalRowBeforeGlobalComputable :
    BitTM
      physicalRowBeforeGlobal :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellGlobalBoundaryUnaryComputable


-- @@ L4747-4764 verbatim
@[simp] private theorem paperVariableArityPhysicalRowBeforeGlobal_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeGlobal
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula)] := by
  unfold physicalRowBeforeGlobal
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellGlobalBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaGlobalBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellGlobalBoundaryUnary_query
      row column formula)


-- @@ L4766-4770 verbatim
private def physicalRowBeforeRefinement :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellRefinementBoundaryUnary


-- @@ L4772-4777 verbatim
private noncomputable def paperVariableArityPhysicalRowBeforeRefinementComputable :
    BitTM
      physicalRowBeforeRefinement :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellRefinementBoundaryUnaryComputable


-- @@ L4779-4796 verbatim
@[simp] private theorem paperVariableArityPhysicalRowBeforeRefinement_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeRefinement
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaRefinementBoundary formula)] := by
  unfold physicalRowBeforeRefinement
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellRefinementBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaRefinementBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellRefinementBoundaryUnary_query
      row column formula)


-- @@ L4798-4802 verbatim
private def physicalRowBeforeOrdinary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    sourceExplicitAffineCellRow
    physicalCellOrdinaryBoundaryUnary


-- @@ L4804-4809 verbatim
private noncomputable def paperVariableArityPhysicalRowBeforeOrdinaryComputable :
    BitTM
      physicalRowBeforeOrdinary :=
  fourFamilyComputedUnaryLessBitComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalCellOrdinaryBoundaryUnaryComputable


-- @@ L4811-4828 verbatim
@[simp] private theorem paperVariableArityPhysicalRowBeforeOrdinary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRowBeforeOrdinary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaOrdinaryBoundary formula)] := by
  unfold physicalRowBeforeOrdinary
  exact fourFamilyComputedUnaryLessBitOutput_valid
    sourceExplicitAffineCellRow
    physicalCellOrdinaryBoundaryUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physicalFormulaOrdinaryBoundary formula)
    (sourceExplicitAffineCellRow_query row column
      (encodeThreeCNF formula))
    (paperVariableArityPhysicalCellOrdinaryBoundaryUnary_query
      row column formula)


-- @@ L4830-4832 verbatim
/-- GapCVP reduction support. -/
abbrev physicalGlobalRowMarker : List Bool → List Bool :=
  physicalRowBeforeGlobal


-- @@ L4834-4838 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalGlobalRowMarkerComputable :
    BitTM
      physicalGlobalRowMarker :=
  paperVariableArityPhysicalRowBeforeGlobalComputable


-- @@ L4840-4847 verbatim
theorem paperVariableArityPhysicalGlobalRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalGlobalRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula)] :=
  paperVariableArityPhysicalRowBeforeGlobal_query row column formula


-- @@ L4849-4854 verbatim
/-- GapCVP reduction support. -/
def physicalRefinementRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement


-- @@ L4856-4863 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRefinementRowMarkerComputable :
    BitTM
      physicalRefinementRowMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      paperVariableArityPhysicalRowBeforeGlobalComputable)
    paperVariableArityPhysicalRowBeforeRefinementComputable


-- @@ L4865-4894 verbatim
@[simp] theorem paperVariableArityPhysicalRefinementRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRefinementRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaGlobalBoundary formula ≤ row ∧
          row < physicalFormulaRefinementBoundary formula)] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have notGlobal := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeGlobal query
    (decide (row < physicalFormulaGlobalBoundary formula))
    (paperVariableArityPhysicalRowBeforeGlobal_query row column formula)
  have both := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement query
    (!(decide
      (row < physicalFormulaGlobalBoundary formula)))
    (decide
      (row < physicalFormulaRefinementBoundary formula))
    notGlobal
    (paperVariableArityPhysicalRowBeforeRefinement_query
      row column formula)
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeGlobal)
    physicalRowBeforeRefinement query = _
  simpa only [← decide_not, Nat.not_lt, ← Bool.decide_and] using both


-- @@ L4896-4901 verbatim
/-- GapCVP reduction support. -/
def physicalOrdinaryRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary


-- @@ L4903-4910 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalOrdinaryRowMarkerComputable :
    BitTM
      physicalOrdinaryRowMarker :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      paperVariableArityPhysicalRowBeforeRefinementComputable)
    paperVariableArityPhysicalRowBeforeOrdinaryComputable


-- @@ L4912-4943 verbatim
@[simp] theorem paperVariableArityPhysicalOrdinaryRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalOrdinaryRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaRefinementBoundary formula ≤ row ∧
          row < physicalFormulaOrdinaryBoundary formula)] := by
  let query := affineCellQuery row column
    (encodeThreeCNF formula)
  have notRefinement := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeRefinement query
    (decide
      (row < physicalFormulaRefinementBoundary formula))
    (paperVariableArityPhysicalRowBeforeRefinement_query
      row column formula)
  have both := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary query
    (!(decide
      (row < physicalFormulaRefinementBoundary formula)))
    (decide
      (row < physicalFormulaOrdinaryBoundary formula))
    notRefinement
    (paperVariableArityPhysicalRowBeforeOrdinary_query
      row column formula)
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      physicalRowBeforeRefinement)
    physicalRowBeforeOrdinary query = _
  simpa only [← decide_not, Nat.not_lt, ← Bool.decide_and] using both


-- @@ L4945-4948 verbatim
/-- GapCVP reduction support. -/
def physicalShiftedRowMarker : List Bool → List Bool :=
  sourceFourFamilyBooleanNotOutput
    physicalRowBeforeOrdinary


-- @@ L4950-4955 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalShiftedRowMarkerComputable :
    BitTM
      physicalShiftedRowMarker :=
  fourFamilyBooleanNotOutputComputable
    paperVariableArityPhysicalRowBeforeOrdinaryComputable


-- @@ L4957-4973 verbatim
@[simp] theorem paperVariableArityPhysicalShiftedRowMarker_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalShiftedRowMarker
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (physicalFormulaOrdinaryBoundary formula ≤ row)] := by
  unfold physicalShiftedRowMarker
  have negation := fourFamilyBooleanNotOutput_bit
    physicalRowBeforeOrdinary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (row < physicalFormulaOrdinaryBoundary formula))
    (paperVariableArityPhysicalRowBeforeOrdinary_query
      row column formula)
  simpa only [← decide_not, Nat.not_lt] using negation


-- @@ L4975-4975 verbatim
end PhysicalFamilyMarkerTM


-- @@ L4977-4977 verbatim
namespace ShiftedTupleTM


-- @@ L4979-4979 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert

-- @@ L4980-4980 verbatim
open GapCVP.SourceIndexedClauseLookupTM

-- @@ L4981-4981 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L4982-4982 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L4983-4983 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics

-- @@ L4984-4984 verbatim
open GapCVP.SourcePreprocessingTM GapCVP.ClauseOffsetTM


-- @@ L4986-4989 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperShiftedSourceClauseWeight (clause : ThreeClause) : ℕ :=
  (paperSourceNormalizedClause clause).length *
    (2 ^ (paperSourceNormalizedClause clause).length - 1)


-- @@ L4991-4994 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperShiftedSourceClauseWeightSum
    (clauses : List ThreeClause) : ℕ :=
  (clauses.map paperShiftedSourceClauseWeight).sum


-- @@ L4996-5000 verbatim
/-- GapCVP reduction support. -/
def paperShiftedClauseWeightUnary : List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    paperVariableArityClauseArityUnary
    paperVariableArityClauseWeightUnary


-- @@ L5002-5008 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedClauseWeightUnaryComputable :
    BitTM
      paperShiftedClauseWeightUnary :=
  fourFamilyComputedUnaryProductComputable
    paperClauseArityUnaryComputable
    paperClauseWeightUnaryComputable


-- @@ L5010-5025 verbatim
@[simp] theorem paperVariableArityShiftedClauseWeightUnary_valid
    (clause : ThreeClause) (suffix : List Bool) :
    paperShiftedClauseWeightUnary
        (encodeThreeClause clause ++ suffix) =
      List.replicate
        (paperShiftedSourceClauseWeight clause) true := by
  unfold paperShiftedClauseWeightUnary
    paperShiftedSourceClauseWeight
  exact fourFamilyComputedUnaryProductOutput_valid
    paperVariableArityClauseArityUnary
    paperVariableArityClauseWeightUnary
    (encodeThreeClause clause ++ suffix)
    (paperSourceNormalizedClause clause).length
    (2 ^ (paperSourceNormalizedClause clause).length - 1)
    (paperVariableArityClauseArityUnary_valid clause suffix)
    (paperVariableArityClauseWeightUnary_valid clause suffix)


-- @@ L5027-5030 verbatim
/-- GapCVP reduction support. -/
abbrev paperVariableArityShiftedRetainedSourceWord :
    List Bool → List Bool :=
  paperPreprocessingFilteredFormulaWord


-- @@ L5032-5036 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedRetainedSourceWordComputable :
    BitTM
      paperVariableArityShiftedRetainedSourceWord :=
  paperSourcePreprocessingFilteredFormulaWordComputable


-- @@ L5038-5042 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperShiftedRetainedClauseWidth :
    SourceQaryMaskDynamicGridWidth where
  output := paperRetainedClauseCountUnary
  computer := paperVariableArityRetainedClauseCountUnaryComputable


-- @@ L5044-5048 verbatim
@[simp] theorem paperVariableArityShiftedRetainedClauseWidth_output
    (input : List Bool) :
    paperShiftedRetainedClauseWidth.output input =
      paperRetainedClauseCountUnary input := by
  rfl


-- @@ L5050-5055 verbatim
/-- GapCVP reduction support. -/
def paperShiftedIndexedClauseQuery
    (input : List Bool) : List Bool :=
  firstFieldContents input ++
    false :: paperVariableArityShiftedRetainedSourceWord
      (firstFieldSuffix (firstFieldSuffix input))


-- @@ L5057-5068 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityShiftedIndexedClauseQueryComputable :
    BitTM
      paperShiftedIndexedClauseQuery := by
  have original := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  have retained := GapCVP.TMComposition.computableInPolyTime
    original paperVariableArityShiftedRetainedSourceWordComputable
  have delimited := GapCVP.TMComposition.computableInPolyTime
    retained (prependBitComputable false)
  exact pointwiseAppendComputable
    firstFieldContentsComputable delimited


-- @@ L5070-5083 verbatim
@[simp] theorem paperVariableArityShiftedIndexedClauseQuery_valid
    (formula : ThreeCNF) (rank : ℕ) :
    paperShiftedIndexedClauseQuery
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          paperShiftedRetainedClauseWidth
          (encodeThreeCNF formula)) =
      sourceOriginalIndexedClauseQuery rank
        (noTautClauses formula) := by
  simp only [paperShiftedIndexedClauseQuery, sourceQaryMaskDynamicGridBaseSource,
      paperShiftedRetainedClauseWidth, paperVariableArityRetainedClauseCountUnary_valid,
          firstFieldContents_valid,
      firstFieldSuffix_valid, paperSourcePreprocessingFilteredFormulaWord_valid,
          sourceOriginalIndexedClauseQuery]


-- @@ L5085-5090 verbatim
/-- Encode a shifted indexed clause weight in unary form. -/
def paperVariableArityShiftedIndexedClauseWeightUnary :
    List Bool → List Bool :=
  paperShiftedClauseWeightUnary ∘
    sourceOriginalIndexedClauseOutput ∘
    paperShiftedIndexedClauseQuery


-- @@ L5092-5101 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable :
    BitTM
      paperVariableArityShiftedIndexedClauseWeightUnary := by
  have indexed := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityShiftedIndexedClauseQueryComputable
    sourceOriginalIndexedClauseComputable
  exact GapCVP.TMComposition.computableInPolyTime
    indexed paperVariableArityShiftedClauseWeightUnaryComputable


-- @@ L5103-5122 verbatim
private theorem paperVariableArityShiftedIndexedClauseWeightUnary_valid
    (formula : ThreeCNF) (rank : ℕ)
    (hbound : rank < (noTautClauses formula).length) :
    paperVariableArityShiftedIndexedClauseWeightUnary
      (lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          paperShiftedRetainedClauseWidth
          (encodeThreeCNF formula)) =
      List.replicate
        (paperShiftedSourceClauseWeight
          ((noTautClauses formula).get
            ⟨rank, hbound⟩)) true := by
  unfold paperVariableArityShiftedIndexedClauseWeightUnary
  simp only [Function.comp_apply]
  rw [paperVariableArityShiftedIndexedClauseQuery_valid,
    sourceOriginalIndexedClauseOutput_valid rank
      (noTautClauses formula) hbound]
  simpa only [List.get_eq_getElem, List.append_nil] using
      paperVariableArityShiftedClauseWeightUnary_valid ((noTautClauses formula).get ⟨rank, hbound⟩)
          []


-- @@ L5124-5129 verbatim
/-- GapCVP reduction support. -/
@[expose] def paperShiftedIndexedSourceClauseWeight
    (clauses : List ThreeClause) (rank : ℕ) : ℕ :=
  match clauses[rank]? with
  | some clause => paperShiftedSourceClauseWeight clause
  | none => 0


-- @@ L5131-5162 verbatim
theorem paperVariableArityShiftedSourceClauseWeight_flatMap
    (clauses : List ThreeClause) :
    (List.range clauses.length).flatMap
      (fun rank => List.replicate
        (paperShiftedIndexedSourceClauseWeight
          clauses rank) true) =
      List.replicate
        (paperShiftedSourceClauseWeightSum clauses) true := by
  induction clauses with
  | nil =>
      simp only [List.length_nil, List.range_zero, List.flatMap_nil,
          paperShiftedSourceClauseWeightSum,
          List.map_nil, List.sum_nil, List.replicate_zero]
  | cons clause remaining ih =>
      simp only [paperShiftedIndexedSourceClauseWeight, List.length_cons, List.range_succ_eq_map,
          List.flatMap_cons,
          lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos, List.getElem_cons_zero,
              List.flatMap_map,
          Nat.succ_eq_add_one, List.getElem?_cons_succ, paperShiftedSourceClauseWeightSum,
              List.map_cons, List.sum_cons]
      change
        List.replicate
            (paperShiftedSourceClauseWeight clause) true ++
          (List.range remaining.length).flatMap
            (fun rank => List.replicate
              (paperShiftedIndexedSourceClauseWeight
                remaining rank) true) =
          List.replicate
            (paperShiftedSourceClauseWeight clause +
              paperShiftedSourceClauseWeightSum remaining)
            true
      rw [ih, List.replicate_append_replicate]


-- @@ L5164-5167 verbatim
private def paperVariableArityShiftedTagCountUnary : List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable


-- @@ L5169-5174 verbatim
private noncomputable def paperVariableArityShiftedTagCountUnaryComputable :
    BitTM
      paperVariableArityShiftedTagCountUnary :=
  maskDynamicGridRecordCatalogueComputable
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable


-- @@ L5176-5209 verbatim
private theorem paperVariableArityShiftedTagCountUnary_valid
    (formula : ThreeCNF) :
    paperVariableArityShiftedTagCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperShiftedSourceClauseWeightSum
          (noTautClauses formula)) true := by
  have hwidth :
      paperShiftedRetainedClauseWidth.output
          (encodeThreeCNF formula) =
        List.replicate
          (noTautClauses formula).length true := by
    rw [paperVariableArityShiftedRetainedClauseWidth_output]
    exact paperVariableArityRetainedClauseCountUnary_valid formula
  have catalogue := maskDynamicGridRecordCatalogueOutput_valid
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable
    (encodeThreeCNF formula)
    (noTautClauses formula).length hwidth
  change maskDynamicGridRecordCatalogueOutput
    paperShiftedRetainedClauseWidth
    paperVariableArityShiftedIndexedClauseWeightUnaryComputable
    (encodeThreeCNF formula) = _
  rw [catalogue]
  rw [← paperVariableArityShiftedSourceClauseWeight_flatMap
    (noTautClauses formula)]
  apply List.flatMap_congr
  intro rank hrank
  have hbound : rank < (noTautClauses formula).length :=
    List.mem_range.mp hrank
  rw [paperVariableArityShiftedIndexedClauseWeightUnary_valid
    formula rank hbound]
  simp only [paperShiftedIndexedSourceClauseWeight,
    List.getElem?_eq_getElem hbound, List.get_eq_getElem]


-- @@ L5211-5211 verbatim
end ShiftedTupleTM


-- @@ L5213-5213 verbatim
namespace CanonicalOffsetIdentity


-- @@ L5215-5215 verbatim
open scoped BigOperators


-- @@ L5217-5217 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.SourcePreprocessingSemantics

-- @@ L5218-5218 verbatim
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.ShiftedTupleTM GapCVP.SourceOrder


-- @@ L5220-5234 verbatim
theorem sourceListWeightSum
    {α : Type*} (clauses : List α) (weight : α → ℕ) :
    (clauses.map weight).sum =
      ∑ index : Fin clauses.length, weight (clauses.get index) := by
  calc
    (clauses.map weight).sum =
        (List.map weight (List.ofFn clauses.get)).sum := by
      rw [List.ofFn_get]
    _ = (List.ofFn
        (fun index : Fin clauses.length =>
          weight (clauses.get index))).sum := by
      rw [List.map_ofFn]
      rfl
    _ = ∑ index : Fin clauses.length, weight (clauses.get index) :=
      List.sum_ofFn


-- @@ L5236-5242 verbatim
/-- GapCVP reduction support. -/
abbrev paperRetainedOriginalClauseIndexOrder
    (formula : ThreeCNF) :
    Fin (noTautClauses formula).length ≃
      Fin (srcFormula formula).clauses.length := by
  apply finCongr
  simp only [srcFormula, paperSourceNormalizedClauses, List.length_map, List.length_attach]


-- @@ L5244-5257 verbatim
theorem paperFormulaClauseWidth_retainedOriginal
    (formula : ThreeCNF)
    (index : Fin (noTautClauses formula).length) :
    paperFormulaClauseWidth formula
        (paperRetainedOriginalClauseIndexOrder
          formula index) =
      (paperSourceNormalizedClause
        ((noTautClauses formula).get index)).length := by
  simp only [paperFormulaClauseWidth, paperSourceNormalizedClauses, paperFormulaRetainedClause,
      Fin.cast,
      srcFormula, paperRetainedOriginalClauseIndexOrder, finCongr, List.get_eq_getElem,
          List.getElem_attach,
      List.getElem_map]
  congr 3


-- @@ L5259-5289 verbatim
theorem sourceClauseWeightSum_eq_localTagCount
    (formula : ThreeCNF) :
    sourceClauseWeightSum
        (noTautClauses formula) =
      paperVariableArityLocalTagCount formula := by
  let retained := noTautClauses formula
  let indexOrder :=
    paperRetainedOriginalClauseIndexOrder formula
  unfold sourceClauseWeightSum
    paperVariableArityLocalTagCount
  calc
    (retained.map sourceClauseWeight).sum =
        ∑ index : Fin retained.length,
          sourceClauseWeight
            (retained.get index) :=
      sourceListWeightSum
        retained sourceClauseWeight
    _ = ∑ index : Fin retained.length,
          (2 ^ paperFormulaClauseWidth
            formula (indexOrder index) - 1) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [sourceClauseWeight, List.get_eq_getElem]
      rw [paperFormulaClauseWidth_retainedOriginal]
      rfl
    _ = ∑ index : Fin
          (srcFormula formula).clauses.length,
          (2 ^ paperFormulaClauseWidth formula index - 1) :=
      indexOrder.sum_comp
        (fun index =>
          2 ^ paperFormulaClauseWidth formula index - 1)


-- @@ L5291-5329 verbatim
private theorem paperVariableArityShiftedSourceClauseWeightSum_eq_localWeights
    (formula : ThreeCNF) :
    paperShiftedSourceClauseWeightSum
        (noTautClauses formula) =
      ∑ index : Fin
        (srcFormula formula).clauses.length,
        paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth formula index - 1) := by
  let retained := noTautClauses formula
  let indexOrder :=
    paperRetainedOriginalClauseIndexOrder formula
  unfold paperShiftedSourceClauseWeightSum
  calc
    (retained.map paperShiftedSourceClauseWeight).sum =
        ∑ index : Fin retained.length,
          paperShiftedSourceClauseWeight
            (retained.get index) :=
      sourceListWeightSum
        retained paperShiftedSourceClauseWeight
    _ = ∑ index : Fin retained.length,
          paperFormulaClauseWidth
            formula (indexOrder index) *
            (2 ^ paperFormulaClauseWidth
              formula (indexOrder index) - 1) := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [paperShiftedSourceClauseWeight, List.get_eq_getElem]
      rw [paperFormulaClauseWidth_retainedOriginal]
      rfl
    _ = ∑ index : Fin
          (srcFormula formula).clauses.length,
          paperFormulaClauseWidth formula index *
            (2 ^ paperFormulaClauseWidth
              formula index - 1) :=
      indexOrder.sum_comp
        (fun index =>
          paperFormulaClauseWidth formula index *
            (2 ^ paperFormulaClauseWidth
              formula index - 1))


-- @@ L5331-5363 verbatim
theorem paperVariableArityShiftedFamilyTagCount_eq_sourceWeight
    (formula : ThreeCNF) (momentBudget : ℕ) :
    paperShiftedFamilyTagCount formula momentBudget =
      paperShiftedSourceClauseWeightSum
        (noTautClauses formula) *
          (momentBudget + 1) := by
  unfold paperShiftedFamilyTagCount
    paperShiftedClauseTagCount
  calc
    (∑ index : Fin
      (srcFormula formula).clauses.length,
      (2 ^ paperFormulaClauseWidth formula index - 1) *
        (paperFormulaClauseWidth formula index *
          (momentBudget + 1))) =
      ∑ index : Fin
        (srcFormula formula).clauses.length,
        (paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth
            formula index - 1)) * (momentBudget + 1) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
    _ =
      (∑ index : Fin
        (srcFormula formula).clauses.length,
        paperFormulaClauseWidth formula index *
          (2 ^ paperFormulaClauseWidth
            formula index - 1)) * (momentBudget + 1) := by
        rw [Finset.sum_mul]
    _ = paperShiftedSourceClauseWeightSum
        (noTautClauses formula) *
          (momentBudget + 1) := by
        rw [paperVariableArityShiftedSourceClauseWeightSum_eq_localWeights]


-- @@ L5365-5365 verbatim
end CanonicalOffsetIdentity


-- @@ L5367-5367 verbatim
namespace Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine


-- @@ L5369-5369 verbatim
open scoped BigOperators


-- @@ L5371-5371 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding

-- @@ L5372-5372 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L5373-5373 verbatim
open GapCVP.Factor400BinaryConstructiveSourcePlaces

-- @@ L5374-5374 verbatim
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.BinaryExplicitAffineSystem

-- @@ L5375-5375 verbatim
open GapCVP.FormulaBridge GapCVP.ClauseOffsetTM GapCVP.SourceOrder GapCVP.ShiftedTupleTM

-- @@ L5376-5376 verbatim
open GapCVP.CanonicalOffsetIdentity GapCVP.PhysicalColumnOrder GapCVP.PhysicalFamilyRowTM

-- @@ L5377-5377 verbatim
open GapCVP.PhysicalFamilyMarkerTM


-- @@ L5379-5383 verbatim
/-- GapCVP reduction support. -/
abbrev physicalFormulaShiftedTupleCount
    (formula : ThreeCNF) : ℕ :=
  paperShiftedSourceClauseWeightSum
    (noTautClauses formula)


-- @@ L5385-5391 verbatim
/-- Number of shifted-family rows in the physical formula system. -/
abbrev paperVariableArityPhysicalFormulaShiftedWidth
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaShiftedTupleCount formula *
    physicalFormulaMomentCount formula *
    physGridCard formula *
    physDegree formula


-- @@ L5393-5397 verbatim
/-- GapCVP reduction support. -/
abbrev paperVariableArityPhysicalFormulaRowCount
    (formula : ThreeCNF) : ℕ :=
  physicalFormulaOrdinaryBoundary formula +
    paperVariableArityPhysicalFormulaShiftedWidth formula


-- @@ L5399-5403 verbatim
private abbrev physicalFormulaColumnCount
    (formula : ThreeCNF) : ℕ :=
  (1 + physicalFormulaTupleCount formula) *
    physGridCard formula *
    physFieldCard formula


-- @@ L5405-5408 verbatim
/-- Encode the shifted physical tuple count in unary form. -/
def physicalShiftedTupleCountUnary :
    List Bool → List Bool :=
  paperVariableArityShiftedTagCountUnary


-- @@ L5410-5415 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalShiftedTupleCountUnaryComputable :
    BitTM
      physicalShiftedTupleCountUnary :=
  paperVariableArityShiftedTagCountUnaryComputable


-- @@ L5417-5423 verbatim
@[simp] private theorem paperVariableArityPhysicalShiftedTupleCountUnary_valid
    (formula : ThreeCNF) :
    physicalShiftedTupleCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaShiftedTupleCount formula) true := by
  exact paperVariableArityShiftedTagCountUnary_valid formula


-- @@ L5425-5433 verbatim
private def physicalShiftedWidthUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalShiftedTupleCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary


-- @@ L5435-5444 verbatim
private noncomputable def paperVariableArityPhysicalShiftedWidthUnaryComputable :
    BitTM
      physicalShiftedWidthUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      (fourFamilyComputedUnaryProductComputable
        paperVariableArityPhysicalShiftedTupleCountUnaryComputable
        paperVariableArityPhysicalFamilyMomentCountUnaryComputable)
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable


-- @@ L5446-5482 verbatim
@[simp] private theorem paperVariableArityPhysicalShiftedWidthUnary_valid
    (formula : ThreeCNF) :
    physicalShiftedWidthUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperVariableArityPhysicalFormulaShiftedWidth formula) true := by
  let input := encodeThreeCNF formula
  have tagMoment := fourFamilyComputedUnaryProductOutput_valid
    physicalShiftedTupleCountUnary
    physicalFamilyMomentCountUnary input
    (physicalFormulaShiftedTupleCount formula)
    (physicalFormulaMomentCount formula)
    (paperVariableArityPhysicalShiftedTupleCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyMomentCountUnary_valid formula)
  have grid := fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalShiftedTupleCountUnary
      physicalFamilyMomentCountUnary)
    physicalFamilyGridCardinalityUnary input
    (physicalFormulaShiftedTupleCount formula *
      physicalFormulaMomentCount formula)
    (physGridCard formula)
    tagMoment
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      (fourFamilyComputedUnaryProductOutput
        physicalShiftedTupleCountUnary
        physicalFamilyMomentCountUnary)
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldDegreeUnary input
    (physicalFormulaShiftedTupleCount formula *
      physicalFormulaMomentCount formula *
      physGridCard formula)
    (physDegree formula)
    grid
    (paperVariableArityPhysicalFamilyFieldDegreeUnary_valid formula)


-- @@ L5484-5489 verbatim
/-- GapCVP reduction support. -/
def physicalRowCountUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    physicalOrdinaryBoundaryUnary
    physicalShiftedWidthUnary


-- @@ L5491-5497 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRowCountUnaryComputable :
    BitTM
      physicalRowCountUnary :=
  fourFamilyComputedUnarySumComputable
    paperVariableArityPhysicalOrdinaryBoundaryUnaryComputable
    paperVariableArityPhysicalShiftedWidthUnaryComputable


-- @@ L5499-5513 verbatim
@[simp] private theorem paperVariableArityPhysicalRowCountUnary_formula_valid
    (formula : ThreeCNF) :
    physicalRowCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperVariableArityPhysicalFormulaRowCount formula) true := by
  unfold physicalRowCountUnary
  exact fourFamilyComputedUnarySumOutput_valid
    physicalOrdinaryBoundaryUnary
    physicalShiftedWidthUnary
    (encodeThreeCNF formula)
    (physicalFormulaOrdinaryBoundary formula)
    (paperVariableArityPhysicalFormulaShiftedWidth formula)
    (paperVariableArityPhysicalOrdinaryBoundaryUnary_valid formula)
    (paperVariableArityPhysicalShiftedWidthUnary_valid formula)


-- @@ L5515-5522 verbatim
/-- GapCVP reduction support. -/
def physicalColumnCountUnary :
    List Bool → List Bool :=
  fourFamilyComputedUnaryProductOutput
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary


-- @@ L5524-5532 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalColumnCountUnaryComputable :
    BitTM
      physicalColumnCountUnary :=
  fourFamilyComputedUnaryProductComputable
    (fourFamilyComputedUnaryProductComputable
      paperVariableArityPhysicalFamilyTypeCountUnaryComputable
      paperVariableArityPhysicalFamilyGridCardinalityUnaryComputable)
    paperVariableArityPhysicalFamilyFieldCardinalityUnaryComputable


-- @@ L5534-5557 verbatim
@[simp] private theorem paperVariableArityPhysicalColumnCountUnary_formula_valid
    (formula : ThreeCNF) :
    physicalColumnCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalFormulaColumnCount formula) true := by
  let input := encodeThreeCNF formula
  have typeGrid := fourFamilyComputedUnaryProductOutput_valid
    physicalFamilyTypeCountUnary
    physicalFamilyGridCardinalityUnary input
    (1 + physicalFormulaTupleCount formula)
    (physGridCard formula)
    (paperVariableArityPhysicalFamilyTypeCountUnary_valid formula)
    (paperVariableArityPhysicalFamilyGridCardinalityUnary_valid formula)
  exact fourFamilyComputedUnaryProductOutput_valid
    (fourFamilyComputedUnaryProductOutput
      physicalFamilyTypeCountUnary
      physicalFamilyGridCardinalityUnary)
    physicalFamilyFieldCardinalityUnary input
    ((1 + physicalFormulaTupleCount formula) *
      physGridCard formula)
    (physFieldCard formula)
    typeGrid
    (paperVariableArityPhysicalFamilyFieldCardinalityUnary_valid formula)


-- @@ L5559-5575 verbatim
private theorem paperVariableArityPhysicalFormulaColumnCount_eq_sourceDimension
    (formula : ThreeCNF) :
    physicalFormulaColumnCount formula =
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        (encodeThreeCNF formula).length
        (srcFormula formula) := by
  symm
  unfold GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
  rw [GapCVP.Core.sourceSATTableDimension_eq,
    sourceTableType_card,
    sourceFormulaGrid_card_eq_fieldWordCount,
    GapCVP.Core.sourceFiniteField_card
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula)),
    paperVariableAritySourceFormula_variableCount,
    ← sourceClauseWeightSum_eq_localTagCount formula]


-- @@ L5577-5585 verbatim
theorem paperVariableArityPhysicalColumnCountUnary_valid
    (formula : ThreeCNF) :
    physicalColumnCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).dimension true := by
  rw [paperVariableArityPhysicalColumnCountUnary_formula_valid,
    paperVariableArityPhysicalFormulaColumnCount_eq_sourceDimension]


-- @@ L5587-5683 verbatim
theorem paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily
    (formula : ThreeCNF) :
    paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula =
      paperVariableArityPhysicalFormulaRowCount formula := by
  classical
  let length := (encodeThreeCNF formula).length
  let source := srcFormula formula
  let gridCount := Fintype.card
    (ExplicitGridPoint length source)
  let fieldCount := Fintype.card
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      length source)
  let degree := physDegree formula
  let momentCount := physicalFormulaMomentCount formula
  have grid_valid :
      gridCount = physGridCard formula := by
    change Fintype.card
      (ExplicitGridPoint length source) = _
    simpa [length, source,
      paperVariableAritySourceFormula_variableCount] using
      sourceFormulaGrid_card_eq_fieldWordCount length source
  have field_valid :
      fieldCount =
        physFieldCard formula := by
    change Fintype.card
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        length source) = _
    simpa [length, source] using
      GapCVP.Core.sourceFiniteField_card
        (GapCVP.Core.sourceSizeParameter_ge_one_hundred length source)
  have shifted_valid :
      Fintype.card
        (Σ clause : Fin source.clauses.length,
          Σ _tuple :
            (source.clauses.get clause).SatisfyingLocalTuple,
          (source.clauses.get clause).LocalVariable ×
            Fin (explicitMomentBudget length source + 1)) =
        physicalFormulaShiftedTupleCount formula *
          momentCount := by
    calc
      Fintype.card
          (Σ clause : Fin source.clauses.length,
            Σ _tuple :
              (source.clauses.get clause).SatisfyingLocalTuple,
            (source.clauses.get clause).LocalVariable ×
              Fin (explicitMomentBudget length source + 1)) =
          paperShiftedFamilyTagCount
            formula (explicitMomentBudget length source) := by
            simpa [source] using
              (Fintype.card_congr
                (paperShiftedFamilyWordOrder formula
                  (explicitMomentBudget length source))).symm
      _ = physicalFormulaShiftedTupleCount formula *
          (explicitMomentBudget length source + 1) :=
        paperVariableArityShiftedFamilyTagCount_eq_sourceWeight
          formula (explicitMomentBudget length source)
      _ = physicalFormulaShiftedTupleCount formula *
          momentCount := by
        rfl
  have table_valid :
      Fintype.card (sourceSATTableType source) =
        1 + physicalFormulaTupleCount formula := by
    change Fintype.card
      (sourceSATTableType (srcFormula formula)) = _
    rw [sourceTableType_card,
      ← sourceClauseWeightSum_eq_localTagCount formula]
  calc
    paperExplicitBinaryRowWordCount
        length formula =
      ∑ family : ExplicitConstraintFamily length source,
        explicitFamilyRowCount length source family * degree := by
          unfold paperExplicitBinaryRowWordCount
            paperExplicitBinaryFamilyBlockCount
          exact (paperExplicitFamilyWordOrder
            length formula).sum_comp
            (fun family => explicitFamilyRowCount
              length (srcFormula formula)
              family * degree)
    _ = gridCount * degree +
      (noTautClauses formula).length *
        gridCount * fieldCount * degree +
      (1 + physicalFormulaTupleCount formula) *
        momentCount * gridCount * degree +
      physicalFormulaShiftedTupleCount formula *
        momentCount * gridCount * degree := by
          simp only [Fintype.sum_sum_type,
            explicitFamilyRowCount, Fintype.card_prod,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Fintype.card_fin]
          rw [shifted_valid, table_valid]
          simp [source,
            gridCount, fieldCount, degree, momentCount,
            explicitMomentBudget]
          ring
    _ = paperVariableArityPhysicalFormulaRowCount formula := by
      rw [grid_valid, field_valid]


-- @@ L5685-5694 verbatim
theorem paperVariableArityPhysicalRowCountUnary_valid
    (formula : ThreeCNF) :
    physicalRowCountUnary
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rowCount true := by
  rw [paperVariableArityPhysicalRowCountUnary_formula_valid]
  rw [paperVariableArityPhysicalWordBinarySystem_rowCount]
  rw [paperVariableArityExplicitBinaryRowWordCount_eq_fourFamily]


-- @@ L5696-5696 verbatim
end Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine


-- @@ L5698-5698 verbatim
namespace CanonicalPhysicalMatrixShape


-- @@ L5700-5700 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.Factor400BinaryConstructiveSourcePlaces

-- @@ L5701-5701 verbatim
open GapCVP.FormulaBridge GapCVP.CanonicalMatrixShape GapCVP.PhysicalColumnOrder

-- @@ L5702-5702 verbatim
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRowCountMachine


-- @@ L5704-5720 verbatim
/-- GapCVP reduction support. -/
@[expose] noncomputable def paperCanonicalPhysicalMatrixShape :
    PaperVariableArityCanonicalBinaryMatrixShape where
  system := physicalWordBinarySystem
  systemCorrect _ _ := rfl
  rows := physicalRowCountUnary
  columns := physicalColumnCountUnary
  rowsComputable := paperVariableArityPhysicalRowCountUnaryComputable
  columnsComputable := paperVariableArityPhysicalColumnCountUnaryComputable
  rowsCorrect formula :=
    paperVariableArityPhysicalRowCountUnary_valid formula
  columnsCorrect formula :=
    paperVariableArityPhysicalColumnCountUnary_valid formula
  columnsPositive formula :=
    sourceFormulaDimension_pos
      (encodeThreeCNF formula).length
      (srcFormula formula)


-- @@ L5722-5727 verbatim
@[simp] private theorem paperVariableArityCanonicalPhysicalMatrixShape_system
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.system
        encodingLength formula =
      physicalWordBinarySystem encodingLength formula := by
  rfl


-- @@ L5729-5737 verbatim
@[simp] theorem paperVariableArityCanonicalPhysicalMatrixShape_rows_valid
    (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.rows
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rowCount true := by
  simpa only [paperVariableArityCanonicalPhysicalMatrixShape_system] using
    paperCanonicalPhysicalMatrixShape.rowsCorrect formula


-- @@ L5739-5747 verbatim
@[simp] theorem paperVariableArityCanonicalPhysicalMatrixShape_columns_valid
    (formula : ThreeCNF) :
    paperCanonicalPhysicalMatrixShape.columns
        (encodeThreeCNF formula) =
      List.replicate
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).dimension true := by
  simpa only [paperVariableArityCanonicalPhysicalMatrixShape_system] using
    paperCanonicalPhysicalMatrixShape.columnsCorrect formula


-- @@ L5749-5752 verbatim
/-- GapCVP reduction support. -/
abbrev PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer :=
  PaperVariableArityCanonicalBinaryMatrixCellComputer
    paperCanonicalPhysicalMatrixShape


-- @@ L5754-5754 verbatim
end CanonicalPhysicalMatrixShape


-- @@ L5756-5756 verbatim
namespace BinaryCompactPhysicalFieldCoefficientBitTM


-- @@ L5758-5758 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L5759-5759 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM GapCVP.BinaryExplicitAffineRows

-- @@ L5760-5760 verbatim
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalCellGridWordTM

-- @@ L5761-5761 verbatim
open GapCVP.BinaryPhysicalLagrangeCoefficientTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM


-- @@ L5763-5766 verbatim
private def compactPhysicalFieldCoefficientBitQuery
    (basisRank : ℕ) (coefficient source : List Bool) : List Bool :=
  lengthPrefixedWord (List.replicate basisRank true) ++
    (lengthPrefixedWord coefficient ++ source)


-- @@ L5768-5770 verbatim
/-- Read the coefficient bit index from a compact physical field query. -/
def compactPhysicalFieldCoefficientBitIndex : List Bool → List Bool :=
  firstFieldContents


-- @@ L5772-5777 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitIndexComputable :
    BitTM
      compactPhysicalFieldCoefficientBitIndex :=
  firstFieldContentsComputable


-- @@ L5779-5781 verbatim
/-- Read the source word from a compact coefficient bit query. -/
def compactPhysicalFieldCoefficientBitSource : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix


-- @@ L5783-5789 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitSourceComputable :
    BitTM
      compactPhysicalFieldCoefficientBitSource :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    firstFieldSuffixComputable firstFieldContentsComputable


-- @@ L5791-5798 verbatim
@[simp] private theorem compactPhysicalFieldCoefficientBitIndex_query
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitIndex
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) =
      List.replicate basisRank true := by
  simp only [compactPhysicalFieldCoefficientBitIndex, compactPhysicalFieldCoefficientBitQuery,
      firstFieldContents_valid]


-- @@ L5800-5806 verbatim
@[simp] private theorem compactPhysicalFieldCoefficientBitSource_query
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitSource
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) = coefficient := by
  simp only [compactPhysicalFieldCoefficientBitSource, compactPhysicalFieldCoefficientBitQuery,
      Function.comp_apply, firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L5808-5812 verbatim
/-- Compute the selected bit of a compact physical field coefficient. -/
def compactPhysicalFieldCoefficientBitWord : List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    compactPhysicalFieldCoefficientBitIndex
    compactPhysicalFieldCoefficientBitSource


-- @@ L5814-5821 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitComputable :
    BitTM
      compactPhysicalFieldCoefficientBitWord :=
  fiveOriginalDynamicBitComputable
    compactPhysicalFieldCoefficientBitIndexComputable
    compactPhysicalFieldCoefficientBitSourceComputable


-- @@ L5823-5838 verbatim
@[simp] private theorem compactPhysicalFieldCoefficientBitWord_valid
    (basisRank : ℕ) (coefficient source : List Bool) :
    compactPhysicalFieldCoefficientBitWord
      (compactPhysicalFieldCoefficientBitQuery
        basisRank coefficient source) =
      [(coefficient.drop basisRank).headD false] := by
  unfold compactPhysicalFieldCoefficientBitWord
  rw [fiveOriginalDynamicBitWord_valid
    compactPhysicalFieldCoefficientBitIndex
    compactPhysicalFieldCoefficientBitSource
    (compactPhysicalFieldCoefficientBitQuery
      basisRank coefficient source)
    basisRank
    (compactPhysicalFieldCoefficientBitIndex_query
      basisRank coefficient source),
    compactPhysicalFieldCoefficientBitSource_query]


-- @@ L5840-5847 verbatim
private theorem compactPhysicalFieldCoefficientFiniteWord_drop_head
    {degree : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (basisRank : ℕ) (hrank : basisRank < degree) :
    ((finiteWordBits word).drop basisRank).headD false =
      word ⟨basisRank, hrank⟩ := by
  exact GapCVP.BinarySourceConvolutionCorrectness.factor400BinaryFiniteWordBits_drop_head
    word basisRank hrank


-- @@ L5849-5855 verbatim
/-- Prepare the query for a compact coefficient bit computation. -/
def compactPhysicalFieldCoefficientBitPreparedQuery
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (basisRank.output input) ++
    (lengthPrefixedWord (coefficient.output input) ++
      source.output input)


-- @@ L5857-5870 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientBitPreparedQueryComputable
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientBitPreparedQuery
        basisRank coefficient source) :=
  physicalCellGridAppendComputer
    (factor400BinaryPhysicalWordRuntimeCompositionComputer
      basisRank.computer physicalCellGridPrefixComputer)
    (physicalCellGridAppendComputer
      (factor400BinaryPhysicalWordRuntimeCompositionComputer
        coefficient.computer physicalCellGridPrefixComputer)
      source.computer)


-- @@ L5872-5886 verbatim
private theorem compactPhysicalFieldCoefficientBitPreparedQuery_valid
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (position : ℕ)
    (coefficientWord originalSource : List Bool)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = coefficientWord)
    (hsource : source.output input = originalSource) :
    compactPhysicalFieldCoefficientBitPreparedQuery
        basisRank coefficient source input =
      compactPhysicalFieldCoefficientBitQuery
        position coefficientWord originalSource := by
  simp only [compactPhysicalFieldCoefficientBitPreparedQuery,
    compactPhysicalFieldCoefficientBitQuery,
    hrank, hcoefficient, hsource]


-- @@ L5888-5894 verbatim
/-- GapCVP reduction support. -/
def compactPhysicalFieldCoefficientPreparedBit
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientBitWord ∘
    compactPhysicalFieldCoefficientBitPreparedQuery
      basisRank coefficient source


-- @@ L5896-5906 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientPreparedBitComputable
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source) :=
  factor400BinaryPhysicalWordRuntimeCompositionComputer
    (compactPhysicalFieldCoefficientBitPreparedQueryComputable
      basisRank coefficient source)
    compactPhysicalFieldCoefficientBitComputable


-- @@ L5908-5924 verbatim
private theorem compactPhysicalFieldCoefficientPreparedBit_valid
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (position : ℕ)
    (coefficientWord originalSource : List Bool)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = coefficientWord)
    (hsource : source.output input = originalSource) :
    compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source input =
      [(coefficientWord.drop position).headD false] := by
  unfold compactPhysicalFieldCoefficientPreparedBit
  rw [Function.comp_apply,
    compactPhysicalFieldCoefficientBitPreparedQuery_valid
      basisRank coefficient source input position
      coefficientWord originalSource hrank hcoefficient hsource,
    compactPhysicalFieldCoefficientBitWord_valid]


-- @@ L5926-5944 verbatim
theorem compactPhysicalFieldCoefficientPreparedBit_bounded_valid
    {degree : ℕ}
    (basisRank coefficient source : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (hposition : position < degree)
    (hrank : basisRank.output input =
      List.replicate position true)
    (hcoefficient : coefficient.output input = finiteWordBits word)
    (hsource : source.output input = encodeThreeCNF formula) :
    compactPhysicalFieldCoefficientPreparedBit
        basisRank coefficient source input =
      [word ⟨position, hposition⟩] := by
  rw [compactPhysicalFieldCoefficientPreparedBit_valid
    basisRank coefficient source input position
    (finiteWordBits word) (encodeThreeCNF formula)
    hrank hcoefficient hsource,
    compactPhysicalFieldCoefficientFiniteWord_drop_head
      word position hposition]


-- @@ L5946-5949 verbatim
private noncomputable def compactPhysicalFieldCoefficientCellSourceComputer :
    SourcePhysicalLagrangeWordComputer where
  output := sourceExplicitAffineCellOriginalSource
  computer := factor400BinaryPhysicalWordCellOriginalSourceComputer


-- @@ L5951-5961 verbatim
@[simp] private theorem compactPhysicalFieldCoefficientCellSourceComputer_query
    (row column : ℕ) (formula : ThreeCNF) :
    compactPhysicalFieldCoefficientCellSourceComputer.output
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      encodeThreeCNF formula := by
  change sourceExplicitAffineCellOriginalSource
    (affineCellQuery row column
      (encodeThreeCNF formula)) = encodeThreeCNF formula
  exact sourceExplicitAffineCellOriginalSource_query
    row column (encodeThreeCNF formula)


-- @@ L5963-5968 verbatim
/-- GapCVP reduction support. -/
def compactPhysicalFieldCoefficientCellBit
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    List Bool → List Bool :=
  compactPhysicalFieldCoefficientPreparedBit
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer


-- @@ L5970-5977 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    compactPhysicalFieldCoefficientCellBitComputable
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (compactPhysicalFieldCoefficientCellBit basisRank coefficient) :=
  compactPhysicalFieldCoefficientPreparedBitComputable
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer


-- @@ L5979-6003 verbatim
theorem compactPhysicalFieldCoefficientCellBit_valid
    {degree : ℕ}
    (basisRank coefficient : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (formula : ThreeCNF)
    (word : GapCVP.Core.EffectiveBinaryField.Word degree)
    (position : ℕ) (hposition : position < degree)
    (hrank : basisRank.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) =
        List.replicate position true)
    (hcoefficient : coefficient.output
      (affineCellQuery row column
        (encodeThreeCNF formula)) = finiteWordBits word) :
    compactPhysicalFieldCoefficientCellBit basisRank coefficient
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [word ⟨position, hposition⟩] := by
  unfold compactPhysicalFieldCoefficientCellBit
  exact compactPhysicalFieldCoefficientPreparedBit_bounded_valid
    basisRank coefficient compactPhysicalFieldCoefficientCellSourceComputer
    (affineCellQuery row column
      (encodeThreeCNF formula))
    formula word position hposition hrank hcoefficient
    (compactPhysicalFieldCoefficientCellSourceComputer_query
      row column formula)


-- @@ L6005-6005 verbatim
end BinaryCompactPhysicalFieldCoefficientBitTM


-- @@ L6007-6007 verbatim
namespace BinaryCompactPhysicalFieldBasisCoordinates


-- @@ L6009-6009 verbatim
open Polynomial GapCVP.Core GapCVP.Core.EffectiveBinaryField GapCVP.BinaryFieldBasis

-- @@ L6010-6010 verbatim
open GapCVP.BinaryFieldInverseAlgebra


-- @@ L6012-6035 verbatim
private theorem effectiveExtensionBasis_wordElement_coordinate
    (degree : ℕ) (word : Word degree) (index : Fin degree) :
    (effectiveExtensionBasis degree).equivFun
      (wordElement word) index = bitValue (word index) := by
  change
    ((AdjoinRoot.powerBasisAux'
      (selectedPolynomial_monic degree)).reindex
        (finCongr (selectedPolynomial_natDegree degree))).equivFun
      (AdjoinRoot.mk (selectedPolynomial degree)
        (wordPolynomial word)) index = _
  rw [Module.Basis.equivFun_apply,
    Module.Basis.repr_reindex_apply,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
    AdjoinRoot.modByMonicHom_mk]
  have hdegree :
      (wordPolynomial word).degree <
        (selectedPolynomial degree).degree := by
    rw [Polynomial.degree_eq_natDegree
      (selectedPolynomial_monic degree).ne_zero,
      selectedPolynomial_natDegree]
    exact wordPolynomial_degree_lt word
  rw [(Polynomial.modByMonic_eq_self_iff
    (selectedPolynomial_monic degree)).mpr hdegree]
  exact wordPolynomial_coeff_fin word index


-- @@ L6037-6064 verbatim
theorem sourceFormulaFieldBasis_sourceWordValue_coordinate
    (encodingLength : ℕ) (formula : Formula)
    (word : Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))
    (index : Fin
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula))) :
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
      encodingLength formula).equivFun
      (sourceWordValue encodingLength formula word) index =
        bitValue (word index) := by
  change
    (effectiveFieldBasis
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula))
      (sourceFieldExponent_pos
        (sourceSizeParameter_ge_one_hundred encodingLength formula))).equivFun
      (extensionAlgEquivGaloisField
        (sourceFieldExponent
          (sourceSizeParameter encodingLength formula))
        (sourceFieldExponent_pos
          (sourceSizeParameter_ge_one_hundred encodingLength formula))
        (wordElement word)) index = _
  rw [effectiveFieldBasis_coordinates_transport]
  exact effectiveExtensionBasis_wordElement_coordinate
    (sourceFieldExponent
      (sourceSizeParameter encodingLength formula)) word index


-- @@ L6066-6066 verbatim
end BinaryCompactPhysicalFieldBasisCoordinates


-- @@ L6068-6068 verbatim
namespace MatrixEntrySemantics


-- @@ L6070-6070 verbatim
open scoped BigOperators


-- @@ L6072-6072 verbatim
open GapCVP.Core GapCVP.Core.EffectiveBinaryField

-- @@ L6073-6073 verbatim
open GapCVP.BinaryCompactPhysicalFieldBasisCoordinates GapCVP.BinaryExplicitAffineSystem

-- @@ L6074-6074 verbatim
open GapCVP.BinaryFieldInverseAlgebra GapCVP.BinaryOrderedRefinement GapCVP.FormulaBridge

-- @@ L6075-6075 verbatim
open GapCVP.PhysicalColumnOrder GapCVP.SourceOrder GapCVP.BinaryPhysicalWordEntries

-- @@ L6076-6076 verbatim
open GapCVP.BinaryReedSolomonParity GapCVP.BinarySourceRowOrder


-- @@ L6078-6078 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L6080-6084 verbatim
/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordField
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
    encodingLength (srcFormula formula)


-- @@ L6086-6090 verbatim
/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordDimension
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
    encodingLength (srcFormula formula)


-- @@ L6092-6096 verbatim
/-- GapCVP reduction support. -/
abbrev PaperVariableArityPhysicalWordGrid
    (encodingLength : ℕ) (formula : ThreeCNF) :=
  GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
    encodingLength (srcFormula formula)


-- @@ L6098-6107 verbatim
private def physicalWordBasisVector
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    Fin (PaperVariableArityPhysicalWordDimension
      encodingLength formula) →
        PaperVariableArityPhysicalWordField encodingLength formula :=
  Pi.single
    (physicalColumnPermutation
      encodingLength formula column) 1


-- @@ L6109-6123 verbatim
/-- GapCVP reduction support. -/
@[expose] def physicalWordCoordinateDelta
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (value : PaperVariableArityPhysicalWordField
      encodingLength formula) :
    PaperVariableArityPhysicalWordField encodingLength formula :=
  if physicalCoordinateIndex
      encodingLength formula tableType point value = column
    then 1 else 0


-- @@ L6125-6184 verbatim
@[simp] private theorem paperVariableArityPhysicalWordBasisVector_apply_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula))
    (tableType : sourceSATTableType
      (srcFormula formula))
    (point : sourceSATGridPoint
      (PaperVariableArityPhysicalWordGrid encodingLength formula))
    (value : PaperVariableArityPhysicalWordField
      encodingLength formula) :
    physicalWordBasisVector
      encodingLength formula column
        (sourceSATColumnIndex
          (srcFormula formula)
          (PaperVariableArityPhysicalWordGrid encodingLength formula)
          tableType point value) =
      physicalWordCoordinateDelta
        encodingLength formula column tableType point value := by
  let permutation :=
    physicalColumnPermutation
      encodingLength formula
  let semantic := sourceSATColumnIndex
    (srcFormula formula)
    (PaperVariableArityPhysicalWordGrid encodingLength formula)
    tableType point value
  have index :
      permutation.symm semantic =
        physicalCoordinateIndex
          encodingLength formula tableType point value :=
    paperVariableArityPhysicalColumnPermutation_symm_sourceSATColumnIndex
      encodingLength formula tableType point value
  have equivalent :
      permutation column = semantic ↔
        physicalCoordinateIndex
          encodingLength formula tableType point value = column := by
    constructor
    · intro equality
      have inverse := congrArg permutation.symm equality
      simpa only [index, Equiv.symm_apply_apply] using inverse.symm
    · intro equality
      apply permutation.symm.injective
      simpa only [Equiv.symm_apply_apply, index] using equality.symm
  simp only [physicalWordBasisVector,
    physicalWordCoordinateDelta]
  change Pi.single (permutation column) 1 semantic =
    if physicalCoordinateIndex
        encodingLength formula tableType point value = column
      then 1 else 0
  by_cases physical :
      physicalCoordinateIndex
        encodingLength formula tableType point value = column
  · have semanticEquality : semantic = permutation column :=
      (equivalent.mpr physical).symm
    rw [semanticEquality, Pi.single_eq_same]
    simp only [physical, ↓reduceIte]
  · have semanticInequality : semantic ≠ permutation column := by
      intro equality
      exact physical (equivalent.mp equality.symm)
    rw [Pi.single_eq_of_ne semanticInequality]
    simp only [physical, ↓reduceIte]


-- @@ L6186-6200 verbatim
/-- GapCVP reduction support. -/
def physicalWordFamilyFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (family : ExplicitConstraintFamily
      encodingLength (srcFormula formula))
    (row : Fin
      (explicitFamilyRowCount
        encodingLength (srcFormula formula) family))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    PaperVariableArityPhysicalWordField encodingLength formula :=
  sourceFormulaPhysicalFamilyLinearMap
    encodingLength (srcFormula formula) family
      (physicalWordBasisVector
        encodingLength formula column) row


-- @@ L6202-6219 verbatim
@[simp] private theorem paperVariableArityPhysicalWordFamilyFieldCoefficient_eq_matrix
    (encodingLength : ℕ) (formula : ThreeCNF)
    (family : ExplicitConstraintFamily
      encodingLength (srcFormula formula))
    (row : Fin
      (explicitFamilyRowCount
        encodingLength (srcFormula formula) family))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
        encodingLength formula family row column =
      sourceFormulaPhysicalFamilyFieldMatrix
        encodingLength (srcFormula formula) family row
          (physicalColumnPermutation
            encodingLength formula column) := by
  rw [sourceFormulaPhysicalFamilyFieldMatrix,
    LinearMap.toMatrix'_apply]
  rfl


-- @@ L6221-6256 verbatim
theorem paperVariableArityPhysicalWordGlobalFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula (.inl ()) row column =
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        physicalWordCoordinateDelta
          encodingLength formula column (.inl ())
          (sourceFormulaExplicitGridOrder
            encodingLength (srcFormula formula)
            row) value := by
  unfold physicalWordFamilyFieldCoefficient sourceFormulaPhysicalFamilyLinearMap
    explicitFamilyLinearMap
  change
    (∑ value : PaperVariableArityPhysicalWordField
      encodingLength formula,
      physicalWordBasisVector
        encodingLength formula column
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula) (.inl ())
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) row)
            value)) = _
  apply Finset.sum_congr rfl
  intro value _
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column (.inl ())
    (sourceFormulaExplicitGridOrder
      encodingLength (srcFormula formula) row) value


-- @@ L6258-6320 verbatim
theorem paperVariableArityPhysicalWordRefinementFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula) ×
        PaperVariableArityPhysicalWordField
          encodingLength formula)))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula (.inr (.inl clause)) row column =
      let position := sourceFormulaExplicitRefinementOrder
        encodingLength (srcFormula formula) row
      physicalWordCoordinateDelta
          encodingLength formula column
          (.inl ()) position.1 position.2 -
        ∑ tuple :
          ((srcFormula
            formula).clauses.get clause).SatisfyingLocalTuple,
          physicalWordCoordinateDelta
            encodingLength formula column
              (.inr ⟨clause, tuple⟩) position.1 position.2 := by
  dsimp only
  unfold physicalWordFamilyFieldCoefficient sourceFormulaPhysicalFamilyLinearMap
    explicitFamilyLinearMap
  change
    physicalWordBasisVector
      encodingLength formula column
        (sourceSATColumnIndex
          (srcFormula formula)
          (PaperVariableArityPhysicalWordGrid
            encodingLength formula) (.inl ())
          (sourceFormulaExplicitRefinementOrder
            encodingLength (srcFormula formula) row).1
          (sourceFormulaExplicitRefinementOrder
            encodingLength (srcFormula formula) row).2) -
      ∑ tuple :
        ((srcFormula
          formula).clauses.get clause).SatisfyingLocalTuple,
        physicalWordBasisVector
          encodingLength formula column
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              (.inr ⟨clause, tuple⟩)
              (sourceFormulaExplicitRefinementOrder
                encodingLength
                (srcFormula formula) row).1
              (sourceFormulaExplicitRefinementOrder
                encodingLength
                (srcFormula formula) row).2) = _
  rw [paperVariableArityPhysicalWordBasisVector_apply_coordinate]
  refine congrArg (HSub.hSub _) ?_
  apply Finset.sum_congr rfl
  intro tuple _
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column (.inr ⟨clause, tuple⟩)
    (sourceFormulaExplicitRefinementOrder
      encodingLength (srcFormula formula) row).1
    (sourceFormulaExplicitRefinementOrder
      encodingLength (srcFormula formula) row).2


-- @@ L6322-6402 verbatim
theorem paperVariableArityPhysicalWordOrdinaryFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (tableType : sourceSATTableType
      (srcFormula formula))
    (moment : Fin
      (explicitMomentBudget
        encodingLength (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inl (tableType, moment)))) row column =
      ∑ position : Fin (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula))),
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitOrdinaryDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row position *
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          physicalWordCoordinateDelta
            encodingLength formula column tableType
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) position) value *
              value ^ moment.val := by
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength (srcFormula formula)
  let fieldVector := physicalWordBasisVector
    encodingLength formula column
  unfold physicalWordFamilyFieldCoefficient sourceFormulaPhysicalFamilyLinearMap
    explicitFamilyLinearMap
  change
    constructiveParityLinearMap
      (fun index => (gridOrder index).val)
      (explicitOrdinaryDegree_lt_grid encodingLength
        (srcFormula formula) moment)
      (fun position =>
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          fieldVector
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              tableType (gridOrder position) value) *
                value ^ moment.val) row = _
  rw [← LinearMap.toMatrix'_mulVec]
  change
    (∑ position : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))),
      constructiveParityMatrix
        (fun index => (gridOrder index).val)
        (explicitOrdinaryDegree_lt_grid encodingLength
          (srcFormula formula) moment)
        row position *
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        fieldVector
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula)
            tableType (gridOrder position) value) *
              value ^ moment.val) = _
  apply Finset.sum_congr rfl
  intro position _
  refine congrArg (HMul.hMul _) ?_
  apply Finset.sum_congr rfl
  intro value _
  refine congrArg (· * _) ?_
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column tableType
      (gridOrder position) value


-- @@ L6404-6516 verbatim
theorem paperVariableArityPhysicalWordShiftedFieldCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin (srcFormula formula).clauses.length)
    (tuple :
      ((srcFormula
        formula).clauses.get clause).SatisfyingLocalTuple)
    (localVariable :
      ((srcFormula
        formula).clauses.get clause).LocalVariable)
    (moment : Fin
      (explicitMomentBudget
        encodingLength (srcFormula formula) + 1))
    (row : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    physicalWordFamilyFieldCoefficient
      encodingLength formula
        (.inr (.inr (.inr
          ⟨clause, tuple, localVariable, moment⟩))) row column =
      ∑ position : Fin (Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula))),
        constructiveParityMatrix
          (fun index =>
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) index).val)
          (explicitShiftedDegree_lt_grid encodingLength
            (srcFormula formula) moment)
          row position *
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          physicalWordCoordinateDelta
            encodingLength formula column
            (.inr ⟨clause, tuple⟩)
            (sourceFormulaExplicitGridOrder encodingLength
              (srcFormula formula) position) value *
            ((value -
                sourceSATFieldBit
                  (K := PaperVariableArityPhysicalWordField
                    encodingLength formula)
                  (tuple.val localVariable)) /
              ((sourceFormulaExplicitGridOrder encodingLength
                (srcFormula formula) position).val -
                GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                    encodingLength (srcFormula formula)
                    localVariable.val)) ^ moment.val := by
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength (srcFormula formula)
  let fieldVector := physicalWordBasisVector
    encodingLength formula column
  unfold physicalWordFamilyFieldCoefficient sourceFormulaPhysicalFamilyLinearMap
    explicitFamilyLinearMap
  change
    constructiveParityLinearMap
      (fun index => (gridOrder index).val)
      (explicitShiftedDegree_lt_grid encodingLength
        (srcFormula formula) moment)
      (fun position =>
        ∑ value : PaperVariableArityPhysicalWordField
          encodingLength formula,
          fieldVector
            (sourceSATColumnIndex
              (srcFormula formula)
              (PaperVariableArityPhysicalWordGrid
                encodingLength formula)
              (.inr ⟨clause, tuple⟩) (gridOrder position) value) *
            ((value -
                sourceSATFieldBit
                  (K := PaperVariableArityPhysicalWordField
                    encodingLength formula)
                  (tuple.val localVariable)) /
              ((gridOrder position).val -
                GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                    encodingLength (srcFormula formula)
                    localVariable.val)) ^ moment.val) row = _
  rw [← LinearMap.toMatrix'_mulVec]
  change
    (∑ position : Fin (Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula))),
      constructiveParityMatrix
        (fun index => (gridOrder index).val)
        (explicitShiftedDegree_lt_grid encodingLength
          (srcFormula formula) moment)
        row position *
      ∑ value : PaperVariableArityPhysicalWordField
        encodingLength formula,
        fieldVector
          (sourceSATColumnIndex
            (srcFormula formula)
            (PaperVariableArityPhysicalWordGrid
              encodingLength formula)
            (.inr ⟨clause, tuple⟩) (gridOrder position) value) *
          ((value -
              sourceSATFieldBit
                (K := PaperVariableArityPhysicalWordField
                  encodingLength formula)
                (tuple.val localVariable)) /
            ((gridOrder position).val -
              GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                  encodingLength (srcFormula formula)
                  localVariable.val)) ^ moment.val) = _
  apply Finset.sum_congr rfl
  intro position _
  refine congrArg (HMul.hMul _) ?_
  apply Finset.sum_congr rfl
  intro value _
  refine congrArg (· * _) ?_
  exact paperVariableArityPhysicalWordBasisVector_apply_coordinate
    encodingLength formula column
      (.inr ⟨clause, tuple⟩) (gridOrder position) value


-- @@ L6518-6524 verbatim
/-- GapCVP reduction support. -/
abbrev physicalWordDecodedRow
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :=
  paperVariableArityExplicitBinaryRowWordOrder
    encodingLength formula row


-- @@ L6526-6560 verbatim
theorem physicalWordBinaryCheckCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).check row column =
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula)).equivFun
        (physicalWordFamilyFieldCoefficient
          encodingLength formula
          (physicalWordDecodedRow
            encodingLength formula row).1
          (physicalWordDecodedRow
            encodingLength formula row).2.1 column)
        (physicalWordDecodedRow
          encodingLength formula row).2.2 := by
  rw [paperVariableArityPhysicalWordBinarySystem_check_apply]
  change
    binaryFieldParityMatrix
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula))
      (sourceFormulaPhysicalFamilyFieldMatrix
        encodingLength (srcFormula formula)
        (physicalWordDecodedRow
          encodingLength formula row).1)
      ((physicalWordDecodedRow
        encodingLength formula row).2.1,
       (physicalWordDecodedRow
        encodingLength formula row).2.2)
      (physicalColumnPermutation
        encodingLength formula column) = _
  rw [binaryFieldParityMatrix_apply_basisCoordinate]
  rw [← paperVariableArityPhysicalWordFamilyFieldCoefficient_eq_matrix]


-- @@ L6562-6578 verbatim
private theorem paperVariableArityPhysicalWordBinaryRightHandSideCoefficient
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row =
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
          encodingLength (srcFormula formula)).equivFun
        (explicitFamilyTarget
          encodingLength (srcFormula formula)
          (physicalWordDecodedRow
            encodingLength formula row).1
          (physicalWordDecodedRow
            encodingLength formula row).2.1)
        (physicalWordDecodedRow
          encodingLength formula row).2.2 := by
  rfl


-- @@ L6580-6595 verbatim
@[simp] theorem paperVariableArityPhysicalFieldBasis_one_coordinate
    (encodingLength : ℕ) (formula : ThreeCNF)
    (coordinate : Fin
      (sourceFieldExponent
        (sourceSizeParameter encodingLength
          (srcFormula formula)))) :
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaFieldBasis
        encodingLength (srcFormula formula)).equivFun
      1 coordinate = bitValue (decide (coordinate.val = 0)) := by
  have word := sourceFormulaFieldBasis_sourceWordValue_coordinate
    encodingLength (srcFormula formula)
    (oneWord (sourceFieldExponent
      (sourceSizeParameter encodingLength
        (srcFormula formula)))) coordinate
  rw [sourceWordValue_oneWord] at word
  simpa only [Module.Basis.equivFun_apply, oneWord] using word


-- @@ L6597-6609 verbatim
private theorem paperVariableArityExplicitFamilyTarget_eq
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (family : ExplicitConstraintFamily encodingLength formula)
    (row : Fin (explicitFamilyRowCount
      encodingLength formula family)) :
    explicitFamilyTarget encodingLength formula family row =
      if family = .inl () then 1 else 0 := by
  cases family with
  | inl value =>
    cases value
    simp only [explicitFamilyTarget, List.get_eq_getElem, ↓reduceIte]
  | inr value =>
    simp only [explicitFamilyTarget, List.get_eq_getElem, reduceCtorEq, ↓reduceIte]


-- @@ L6611-6629 verbatim
private theorem paperVariableArityPhysicalWordBinaryRightHandSide_global
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (global :
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl ()) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row =
      bitValue (decide
        ((physicalWordDecodedRow
          encodingLength formula row).2.2.val = 0)) := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSideCoefficient]
  rw [paperVariableArityExplicitFamilyTarget_eq,
    ite_eq_left global]
  exact paperVariableArityPhysicalFieldBasis_one_coordinate
    encodingLength formula
      (physicalWordDecodedRow
        encodingLength formula row).2.2


-- @@ L6631-6643 verbatim
private theorem paperVariableArityPhysicalWordBinaryRightHandSide_nonGlobal
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula))
    (nonGlobal :
      (physicalWordDecodedRow
        encodingLength formula row).1 ≠ .inl ()) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 0 := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSideCoefficient]
  rw [paperVariableArityExplicitFamilyTarget_eq,
    ite_eq_right nonGlobal]
  simp only [map_zero, Pi.zero_apply]


-- @@ L6645-6665 verbatim
private theorem paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin (paperExplicitBinaryRowWordCount
      encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 1 ↔
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl () ∧
      (physicalWordDecodedRow
        encodingLength formula row).2.2.val = 0 := by
  by_cases global :
      (physicalWordDecodedRow
        encodingLength formula row).1 = .inl ()
  · rw [paperVariableArityPhysicalWordBinaryRightHandSide_global
      encodingLength formula row global]
    simp only [bitValue, decide_eq_true_eq, ite_eq_left_iff, zero_ne_one, imp_false,
        Decidable.not_not, global,
        List.get_eq_getElem, true_and]
  · rw [paperVariableArityPhysicalWordBinaryRightHandSide_nonGlobal
      encodingLength formula row global]
    simp only [zero_ne_one, List.get_eq_getElem, global, false_and]


-- @@ L6667-6667 verbatim
end MatrixEntrySemantics


-- @@ L6669-6669 verbatim
namespace PhysicalRowOrderProjection


-- @@ L6671-6671 verbatim
open scoped BigOperators


-- @@ L6673-6673 verbatim
open GapCVP.Core GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineSystem GapCVP.FormulaBridge

-- @@ L6674-6674 verbatim
open GapCVP.SourceOrder GapCVP.PhysicalColumnOrder GapCVP.MatrixEntrySemantics


-- @@ L6676-6686 verbatim
/-- GapCVP reduction support. -/
@[expose] def physicalRowDependentFamilyIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    Fin (paperExplicitFamilyTagCount
      encodingLength formula) :=
  ((finSigmaFinEquiv
    (n := paperExplicitBinaryFamilyBlockCount
      encodingLength formula)).symm row).1


-- @@ L6688-6700 verbatim
/-- GapCVP reduction support. -/
@[expose] def physicalRowDependentBlockRank
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    Fin (paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      (physicalRowDependentFamilyIndex
        encodingLength formula row)) :=
  ((finSigmaFinEquiv
    (n := paperExplicitBinaryFamilyBlockCount
      encodingLength formula)).symm row).2


-- @@ L6702-6734 verbatim
theorem physicalRowDependentRank_eq_prefix
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    row.val =
      (∑ index : Fin
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val,
        paperExplicitBinaryFamilyBlockCount
          encodingLength formula
          (Fin.castLE
            (physicalRowDependentFamilyIndex
              encodingLength formula row).isLt.le index)) +
        (physicalRowDependentBlockRank
          encodingLength formula row).val := by
  let decomposition :=
    (finSigmaFinEquiv
      (n := paperExplicitBinaryFamilyBlockCount
        encodingLength formula)).symm row
  change row.val =
    (∑ index : Fin decomposition.1.val,
      paperExplicitBinaryFamilyBlockCount
        encodingLength formula
        (Fin.castLE decomposition.1.isLt.le index)) +
      decomposition.2.val
  calc
    row.val = (finSigmaFinEquiv decomposition).val := by
      exact congrArg Fin.val
        ((finSigmaFinEquiv
          (n := paperExplicitBinaryFamilyBlockCount
            encodingLength formula)).apply_symm_apply row).symm
    _ = _ := finSigmaFinEquiv_apply decomposition


-- @@ L6736-6747 verbatim
theorem physicalRowOrder_family
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).1 =
      paperExplicitFamilyWordOrder
        encodingLength formula
        (physicalRowDependentFamilyIndex
          encodingLength formula row) := by
  rfl


-- @@ L6749-6760 verbatim
theorem physicalRowOrder_fieldRow
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.1.val =
      (physicalRowDependentBlockRank
        encodingLength formula row).val /
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  rfl


-- @@ L6762-6773 verbatim
private theorem paperVariableArityPhysicalRowOrder_basis
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.2.val =
      (physicalRowDependentBlockRank
        encodingLength formula row).val %
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  rfl


-- @@ L6775-6816 verbatim
theorem physicalRowOrder_basis_val
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).2.2.val =
      row.val % paperExplicitBinaryRowDegree
        encodingLength formula := by
  rw [paperVariableArityPhysicalRowOrder_basis]
  have rank := physicalRowDependentRank_eq_prefix
    encodingLength formula row
  have prefixSum :
      (∑ index : Fin
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val,
        paperExplicitBinaryFamilyBlockCount
          encodingLength formula
          (Fin.castLE
            (physicalRowDependentFamilyIndex
              encodingLength formula row).isLt.le index)) =
        (∑ index : Fin
          (physicalRowDependentFamilyIndex
            encodingLength formula row).val,
          explicitFamilyRowCount encodingLength
            (srcFormula formula)
            (paperExplicitFamilyWordOrder
              encodingLength formula
              (Fin.castLE
                (physicalRowDependentFamilyIndex
                  encodingLength formula row).isLt.le index))) *
            paperExplicitBinaryRowDegree
              encodingLength formula := by
    simp only [paperExplicitBinaryFamilyBlockCount]
    rw [Finset.sum_mul]
  rw [prefixSum] at rank
  have residue := congrArg
    (fun value : ℕ =>
      value % paperExplicitBinaryRowDegree
        encodingLength formula) rank
  simpa only [Nat.add_mod, Nat.mul_mod_left, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
      using residue.symm


-- @@ L6818-6866 verbatim
private theorem paperVariableArityPhysicalSigmaFamilyIndex_zero_iff
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (positive : 0 < familyCount)
    (row : Fin (∑ index : Fin familyCount, blockCount index)) :
    ((finSigmaFinEquiv (n := blockCount)).symm row).1.val = 0 ↔
      row.val < blockCount ⟨0, positive⟩ := by
  let decomposition :=
    (finSigmaFinEquiv (n := blockCount)).symm row
  have rank :
      row.val =
        (∑ index : Fin decomposition.1.val,
          blockCount (Fin.castLE decomposition.1.isLt.le index)) +
        decomposition.2.val := by
    simpa only [decomposition, Equiv.apply_symm_apply] using
      finSigmaFinEquiv_apply decomposition
  constructor
  · intro zero
    change decomposition.1.val = 0 at zero
    have first : decomposition.1 = ⟨0, positive⟩ := by
      apply Fin.ext
      exact zero
    have prefixZero :
        (∑ index : Fin decomposition.1.val,
          blockCount (Fin.castLE decomposition.1.isLt.le index)) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Fin.elim0 (Fin.cast zero index)
    have localEquality : row.val = decomposition.2.val := by
      omega
    rw [localEquality]
    simpa [first] using decomposition.2.isLt
  · intro bounded
    by_contra nonzero
    change decomposition.1.val ≠ 0 at nonzero
    have indexPositive : 0 < decomposition.1.val :=
      Nat.pos_of_ne_zero nonzero
    let first : Fin decomposition.1.val := ⟨0, indexPositive⟩
    have prefixLower :
        blockCount ⟨0, positive⟩ ≤
          ∑ index : Fin decomposition.1.val,
            blockCount (Fin.castLE decomposition.1.isLt.le index) := by
      have term := Finset.single_le_sum
        (f := fun index : Fin decomposition.1.val =>
          blockCount (Fin.castLE decomposition.1.isLt.le index))
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ first)
      simpa [first] using term
    omega


-- @@ L6868-6875 verbatim
theorem physicalFamilyTagCount_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < paperExplicitFamilyTagCount
      encodingLength formula := by
  simp only [paperExplicitFamilyTagCount,
      add_pos_iff,
      Order.lt_one_iff, true_or, mul_pos_iff_of_pos_left, Order.lt_add_one_iff, zero_le, or_true,
          or_self]


-- @@ L6877-6883 verbatim
theorem physicalFamilyWordOrder_zero
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperExplicitFamilyWordOrder
      encodingLength formula
      ⟨0, physicalFamilyTagCount_pos
        encodingLength formula⟩ = .inl () := by
  rfl


-- @@ L6885-6898 verbatim
theorem physicalFirstFamilyBlockCount
    (encodingLength : ℕ) (formula : ThreeCNF) :
    paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      ⟨0, physicalFamilyTagCount_pos
        encodingLength formula⟩ =
      Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula)) *
        paperExplicitBinaryRowDegree
          encodingLength formula := by
  simp only [paperExplicitBinaryFamilyBlockCount, explicitFamilyRowCount,
      physicalFamilyWordOrder_zero,
      List.get_eq_getElem, Fintype.card_coe]


-- @@ L6900-6907 verbatim
/-- GapCVP reduction support. -/
abbrev physicalSourceGlobalBoundary
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  Fintype.card
    (ExplicitGridPoint encodingLength
      (srcFormula formula)) *
    paperExplicitBinaryRowDegree
      encodingLength formula


-- @@ L6909-6970 verbatim
theorem paperVariableArityPhysicalRowOrder_global_iff
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordDecodedRow
      encodingLength formula row).1 = .inl () ↔
      row.val < physicalSourceGlobalBoundary
        encodingLength formula := by
  let positive := physicalFamilyTagCount_pos
    encodingLength formula
  have first := paperVariableArityPhysicalSigmaFamilyIndex_zero_iff
    (paperExplicitBinaryFamilyBlockCount
      encodingLength formula) positive row
  constructor
  · intro global
    have selected :
        paperExplicitFamilyWordOrder
          encodingLength formula
          (physicalRowDependentFamilyIndex
            encodingLength formula row) = .inl () := by
      exact (physicalRowOrder_family
        encodingLength formula row).symm.trans global
    have zero :
        physicalRowDependentFamilyIndex
          encodingLength formula row = ⟨0, positive⟩ := by
      apply
        (paperExplicitFamilyWordOrder
          encodingLength formula).injective
      simpa only [physicalFamilyWordOrder_zero, List.get_eq_getElem] using selected
    have selectedZero :
        ((finSigmaFinEquiv
          (n := paperExplicitBinaryFamilyBlockCount
            encodingLength formula)).symm row).1.val = 0 := by
      change
        (physicalRowDependentFamilyIndex
          encodingLength formula row).val = 0
      exact congrArg Fin.val zero
    have bounded := first.mp selectedZero
    rw [physicalFirstFamilyBlockCount] at bounded
    exact bounded
  · intro bounded
    have inFirst :
        row.val < paperExplicitBinaryFamilyBlockCount
          encodingLength formula ⟨0, positive⟩ := by
      rw [physicalFirstFamilyBlockCount]
      exact bounded
    have zero := first.mpr inFirst
    have selected :
        physicalRowDependentFamilyIndex
          encodingLength formula row = ⟨0, positive⟩ := by
      apply Fin.ext
      exact zero
    rw [physicalRowOrder_family]
    change
      paperExplicitFamilyWordOrder
        encodingLength formula
        (physicalRowDependentFamilyIndex
          encodingLength formula row) = .inl ()
    rw [selected]
    exact physicalFamilyWordOrder_zero
      encodingLength formula


-- @@ L6972-6984 verbatim
theorem physicalSourceGridCardinality_eq
    (encodingLength : ℕ) (formula : ThreeCNF) :
    Fintype.card
      (ExplicitGridPoint encodingLength
        (srcFormula formula)) =
      2 ^ sourceFieldExponent
          (sourceSizeParameter encodingLength
            (srcFormula formula)) -
        paperVariableArityVariableCount formula := by
  simpa only [Fintype.card_coe, paperVariableAritySourceFormula_variableCount] using
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid_card_eq_fieldWordCount
          encodingLength
        (srcFormula formula)


-- @@ L6986-7004 verbatim
private theorem paperVariableArityPhysicalSourceGlobalBoundary_eq
    (formula : ThreeCNF) :
    physicalSourceGlobalBoundary
      (encodeThreeCNF formula).length formula =
      (2 ^ sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) -
        paperVariableArityVariableCount formula) *
      sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) := by
  change
    Fintype.card
      (ExplicitGridPoint (encodeThreeCNF formula).length
        (srcFormula formula)) *
      sourceFieldExponent
        (sourceSizeParameter (encodeThreeCNF formula).length
          (srcFormula formula)) = _
  rw [physicalSourceGridCardinality_eq]


-- @@ L7006-7021 verbatim
private theorem paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff_sourceRanks
    (encodingLength : ℕ) (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        encodingLength formula)) :
    (physicalWordBinarySystem
      encodingLength formula).rightHandSide row = 1 ↔
      row.val < physicalSourceGlobalBoundary
        encodingLength formula ∧
      row.val % paperExplicitBinaryRowDegree
        encodingLength formula = 0 := by
  rw [paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff]
  exact and_congr
    (paperVariableArityPhysicalRowOrder_global_iff
      encodingLength formula row)
    (by rw [physicalRowOrder_basis_val])


-- @@ L7023-7029 verbatim
/-- GapCVP reduction support. -/
@[expose] def physicalSigmaPrefix
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (family : Fin familyCount) : ℕ :=
  ∑ index : Fin family.val,
    blockCount (Fin.castLE family.isLt.le index)


-- @@ L7031-7076 verbatim
theorem paperVariableArityPhysicalSigmaFamilyIndex_eq_iff
    {familyCount : ℕ}
    (blockCount : Fin familyCount → ℕ)
    (row : Fin (∑ index : Fin familyCount, blockCount index))
    (family : Fin familyCount) :
    ((finSigmaFinEquiv (n := blockCount)).symm row).1 = family ↔
      physicalSigmaPrefix
        blockCount family ≤ row.val ∧
        row.val < physicalSigmaPrefix
          blockCount family + blockCount family := by
  let decomposition :=
    (finSigmaFinEquiv (n := blockCount)).symm row
  have rank :
      row.val =
        physicalSigmaPrefix
          blockCount decomposition.1 + decomposition.2.val := by
    simpa only [physicalSigmaPrefix,
      decomposition, Equiv.apply_symm_apply] using
      finSigmaFinEquiv_apply decomposition
  constructor
  · intro selected
    change decomposition.1 = family at selected
    subst family
    have bound := decomposition.2.isLt
    omega
  · rintro ⟨lower, upper⟩
    let localRank : Fin (blockCount family) :=
      ⟨row.val - physicalSigmaPrefix
        blockCount family, by omega⟩
    have forward :
        finSigmaFinEquiv (n := blockCount)
          (⟨family, localRank⟩ : (index : Fin familyCount) ×
            Fin (blockCount index)) = row := by
      apply Fin.ext
      rw [finSigmaFinEquiv_apply]
      change
        physicalSigmaPrefix blockCount family +
          (row.val - physicalSigmaPrefix
            blockCount family) = row.val
      omega
    have decode :
        (finSigmaFinEquiv (n := blockCount)).symm row =
          (⟨family, localRank⟩ : (index : Fin familyCount) ×
            Fin (blockCount index)) := by
      rw [← forward, Equiv.symm_apply_apply]
    exact congrArg Sigma.fst decode


-- @@ L7078-7086 verbatim
/-- GapCVP reduction support. -/
@[expose] def physicalRefinementFamilyIndex
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    Fin (paperExplicitFamilyTagCount
      encodingLength formula) :=
  (paperExplicitFamilyWordOrder
    encodingLength formula).symm (.inr (.inl clause))


-- @@ L7088-7094 verbatim
theorem paperVariableArityPhysicalRefinementFamilyIndex_val
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    (physicalRefinementFamilyIndex
      encodingLength formula clause).val = 1 + clause.val := by
  rfl


-- @@ L7096-7114 verbatim
theorem paperVariableArityPhysicalRefinementFamilyBlockCount
    (encodingLength : ℕ) (formula : ThreeCNF)
    (clause : Fin
      (srcFormula formula).clauses.length) :
    paperExplicitBinaryFamilyBlockCount
      encodingLength formula
      (physicalRefinementFamilyIndex
        encodingLength formula clause) =
      Fintype.card
        (ExplicitGridPoint encodingLength
          (srcFormula formula)) *
      Fintype.card
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength (srcFormula formula)) *
      paperExplicitBinaryRowDegree
        encodingLength formula := by
  simp only [paperExplicitBinaryFamilyBlockCount, explicitFamilyRowCount,
      physicalRefinementFamilyIndex,
      List.get_eq_getElem, Equiv.apply_symm_apply, Fintype.card_prod, Fintype.card_coe]


-- @@ L7116-7116 verbatim
end PhysicalRowOrderProjection


-- @@ L7118-7118 verbatim
namespace PhysicalRightHandSideTM


-- @@ L7120-7120 verbatim
open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L7121-7121 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L7122-7122 verbatim
open GapCVP.SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

-- @@ L7123-7123 verbatim
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryPhysicalRowBasisDivisionTM

-- @@ L7124-7124 verbatim
open GapCVP.FormulaBridge GapCVP.SourceOrder GapCVP.PhysicalColumnOrder

-- @@ L7125-7125 verbatim
open GapCVP.PhysicalFamilyRowTM GapCVP.PhysicalFamilyMarkerTM GapCVP.MatrixEntrySemantics

-- @@ L7126-7126 verbatim
open GapCVP.PhysicalRowOrderProjection


-- @@ L7128-7132 verbatim
/-- GapCVP reduction support. -/
def physicalRightHandSideCellDegreeUnary :
    List Bool → List Bool :=
  physicalFamilyFieldDegreeUnary ∘
    sourceExplicitAffineCellOriginalSource


-- @@ L7134-7141 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable :
    BitTM
      physicalRightHandSideCellDegreeUnary :=
  GapCVP.TMComposition.computableInPolyTime
    sourceExplicitAffineCellOriginalSourceComputable
    paperVariableArityPhysicalFamilyFieldDegreeUnaryComputable


-- @@ L7143-7152 verbatim
@[simp] theorem paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideCellDegreeUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (physDegree formula) true := by
  unfold physicalRightHandSideCellDegreeUnary
  rw [Function.comp_apply, sourceExplicitAffineCellOriginalSource_query,
    paperVariableArityPhysicalFamilyFieldDegreeUnary_valid]


-- @@ L7154-7159 verbatim
/-- Encode the right-hand-side basis rank in unary form. -/
def physicalRightHandSideBasisRankUnary :
    List Bool → List Bool :=
  sourcePhysicalComputedUnaryRemainder
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary


-- @@ L7161-7168 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideBasisRankUnaryComputable :
    BitTM
      physicalRightHandSideBasisRankUnary :=
  sourcePhysicalComputedUnaryRemainderComputable
    sourceExplicitAffineCellRowComputable
    paperVariableArityPhysicalRightHandSideCellDegreeUnaryComputable


-- @@ L7170-7191 verbatim
@[simp] private theorem paperVariableArityPhysicalRightHandSideBasisRankUnary_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBasisRankUnary
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      List.replicate
        (row % physDegree formula) true := by
  unfold physicalRightHandSideBasisRankUnary
  apply sourcePhysicalComputedUnaryRemainder_valid
    sourceExplicitAffineCellRow
    physicalRightHandSideCellDegreeUnary
    (affineCellQuery row column
      (encodeThreeCNF formula))
    row (physDegree formula)
  · exact GapCVP.Core.sourceFieldExponent_pos
      (GapCVP.Core.sourceSizeParameter_ge_one_hundred
        (encodeThreeCNF formula).length
        (srcFormula formula))
  · exact sourceExplicitAffineCellRow_query
      row column (encodeThreeCNF formula)
  · exact paperVariableArityPhysicalRightHandSideCellDegreeUnary_query
      row column formula


-- @@ L7193-7198 verbatim
/-- GapCVP reduction support. -/
def physicalRightHandSideBasisZeroBit :
    List Bool → List Bool :=
  maskComputedWordEquality
    physicalRightHandSideBasisRankUnary
    (fun _ => [])


-- @@ L7200-7207 verbatim
/-- GapCVP reduction support. -/
noncomputable def
    paperVariableArityPhysicalRightHandSideBasisZeroBitComputable :
    BitTM
      physicalRightHandSideBasisZeroBit :=
  maskComputedWordEqualityComputable
    paperVariableArityPhysicalRightHandSideBasisRankUnaryComputable
    (sourceFixedWordComputable [])


-- @@ L7209-7218 verbatim
@[simp] theorem paperVariableArityPhysicalRightHandSideBasisZeroBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBasisZeroBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide (row % physDegree formula = 0)] := by
  unfold physicalRightHandSideBasisZeroBit
  rw [sourceQaryMaskSquareComputedWordEquality_valid,
    paperVariableArityPhysicalRightHandSideBasisRankUnary_query]
  simp only [List.replicate_eq_nil_iff]


-- @@ L7220-7225 verbatim
/-- GapCVP reduction support. -/
def physicalRightHandSideBit :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    physicalGlobalRowMarker
    physicalRightHandSideBasisZeroBit


-- @@ L7227-7233 verbatim
/-- GapCVP reduction support. -/
noncomputable def paperVariableArityPhysicalRightHandSideBitComputable :
    BitTM
      physicalRightHandSideBit :=
  fourFamilyBooleanAndComputable
    paperVariableArityPhysicalGlobalRowMarkerComputable
    paperVariableArityPhysicalRightHandSideBasisZeroBitComputable


-- @@ L7235-7257 verbatim
@[simp] private theorem paperVariableArityPhysicalRightHandSideBit_query
    (row column : ℕ) (formula : ThreeCNF) :
    physicalRightHandSideBit
        (affineCellQuery row column
          (encodeThreeCNF formula)) =
      [decide
        (row < physicalFormulaGlobalBoundary formula) &&
       decide
        (row % physDegree formula = 0)] := by
  unfold physicalRightHandSideBit
  exact fourFamilyBooleanAndOutput_bits
    physicalGlobalRowMarker
    physicalRightHandSideBasisZeroBit
    (affineCellQuery row column
      (encodeThreeCNF formula))
    (decide
      (row < physicalFormulaGlobalBoundary formula))
    (decide
      (row % physDegree formula = 0))
    (paperVariableArityPhysicalGlobalRowMarker_query
      row column formula)
    (paperVariableArityPhysicalRightHandSideBasisZeroBit_query
      row column formula)


-- @@ L7259-7292 verbatim
theorem paperVariableArityPhysicalRightHandSide_valid
    (formula : ThreeCNF)
    (row : Fin
      (paperExplicitBinaryRowWordCount
        (encodeThreeCNF formula).length formula))
    (column : Fin
      (PaperVariableArityPhysicalWordDimension
        (encodeThreeCNF formula).length formula)) :
    physicalRightHandSideBit
        (affineCellQuery row.val column.val
          (encodeThreeCNF formula)) =
      [decide
        ((physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rightHandSide row =
            (1 : ZMod 2))] := by
  have boundary :
      physicalSourceGlobalBoundary
        (encodeThreeCNF formula).length formula =
        physicalFormulaGlobalBoundary formula :=
    paperVariableArityPhysicalSourceGlobalBoundary_eq formula
  have target :
      (row.val < physicalFormulaGlobalBoundary formula ∧
        row.val % physDegree formula = 0) ↔
        (physicalWordBinarySystem
          (encodeThreeCNF formula).length formula).rightHandSide row =
            (1 : ZMod 2) := by
    have ranks := paperVariableArityPhysicalWordBinaryRightHandSide_eq_one_iff_sourceRanks
      (encodeThreeCNF formula).length formula row
    rw [boundary] at ranks
    exact ranks.symm
  rw [paperVariableArityPhysicalRightHandSideBit_query,
    ← Bool.decide_and]
  exact congrArg (fun bit : Bool => [bit])
    (Bool.decide_congr target)


-- @@ L7294-7294 verbatim
end PhysicalRightHandSideTM


-- @@ L7296-7296 verbatim
namespace BinaryAllWordRankOrder


-- @@ L7298-7298 verbatim
open GapCVP.BinaryFieldBasis GapCVP.Core.EffectiveBinaryField


-- @@ L7300-7311 verbatim
private theorem naturalRange_double_flatMap (count : ℕ) :
    List.range (2 * count) =
      (List.range count).flatMap
        (fun rank => [2 * rank, 2 * rank + 1]) := by
  induction count with
  | zero => simp only [mul_zero, List.range_zero, List.flatMap_nil]
  | succ count ih =>
      rw [show 2 * (count + 1) = 2 * count + 2 by omega,
        List.range_add]
      simp only [ih, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
          List.map_cons, add_zero,
          List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]


-- @@ L7313-7314 verbatim
private def naturalRankWord (degree rank : ℕ) : Word degree :=
  fun bit => rank.testBit bit.val


-- @@ L7316-7327 verbatim
private theorem naturalRankWord_even
    (degree rank : ℕ) :
    naturalRankWord (degree + 1) (2 * rank) =
      Fin.cases false (naturalRankWord degree rank) := by
  funext bit
  refine Fin.cases ?_ (fun next => ?_) bit
  · simp only [naturalRankWord, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.testBit_zero,
      Nat.mul_mod_right,
        zero_ne_one, decide_false, Fin.cases_zero]
  · simp only [naturalRankWord, Fin.val_succ, Nat.testBit_succ, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true,
        mul_div_cancel_left₀, Fin.cases_succ]


-- @@ L7329-7344 verbatim
private theorem naturalRankWord_odd
    (degree rank : ℕ) :
    naturalRankWord (degree + 1) (2 * rank + 1) =
      Fin.cases true (naturalRankWord degree rank) := by
  funext bit
  refine Fin.cases ?_ (fun next => ?_) bit
  · simp only [naturalRankWord, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.testBit_zero,
      Nat.mul_add_mod_self_left,
        Nat.mod_succ, decide_true, Fin.cases_zero]
  · change
      (2 * rank + 1).testBit (next.val + 1) =
        rank.testBit next.val
    have hdivision : (2 * rank + 1) / 2 = rank := by
      omega
    rw [show next.val + 1 = Nat.succ next.val by omega,
      Nat.testBit_succ, hdivision]


-- @@ L7346-7383 verbatim
private theorem allWords_eq_naturalRankWords (degree : ℕ) :
    allWords degree =
      (List.range (2 ^ degree)).map
        (naturalRankWord degree) := by
  induction degree with
  | zero =>
      change [(fun bit : Fin 0 => Fin.elim0 bit)] =
        [naturalRankWord 0 0]
      congr 1
      exact Subsingleton.elim _ _
  | succ degree ih =>
      calc
        allWords (degree + 1) =
            ((List.range (2 ^ degree)).map
              (naturalRankWord degree)).flatMap
              (fun tail =>
                [Fin.cases false tail, Fin.cases true tail]) := by
              rw [allWords, ih]
        _ = (List.range (2 ^ degree)).flatMap
              (fun rank =>
                [naturalRankWord (degree + 1) (2 * rank),
                 naturalRankWord (degree + 1) (2 * rank + 1)]) := by
              simp only [List.flatMap_map]
              apply List.flatMap_congr
              intro rank _
              rw [naturalRankWord_even, naturalRankWord_odd]
        _ = ((List.range (2 ^ degree)).flatMap
              (fun rank => [2 * rank, 2 * rank + 1])).map
                (naturalRankWord (degree + 1)) := by
              simp only [List.map_flatMap, List.map_cons, List.map_nil]
        _ = (List.range (2 * 2 ^ degree)).map
              (naturalRankWord (degree + 1)) := by
              rw [naturalRange_double_flatMap]
        _ = (List.range (2 ^ (degree + 1))).map
              (naturalRankWord (degree + 1)) := by
              rw [pow_succ]
              congr 2
              omega


-- @@ L7385-7400 verbatim
theorem allWords_eq_finRange_indexedWord (degree : ℕ) :
    allWords degree =
      (List.finRange (2 ^ degree)).map (indexedWord degree) := by
  calc
    allWords degree =
        (List.range (2 ^ degree)).map
          (naturalRankWord degree) :=
      allWords_eq_naturalRankWords degree
    _ = ((List.finRange (2 ^ degree)).map
          (fun rank => rank.val)).map
            (naturalRankWord degree) := by
          rw [List.map_coe_finRange_eq_range]
    _ = (List.finRange (2 ^ degree)).map
          (indexedWord degree) := by
          rw [List.map_map]
          rfl


-- @@ L7402-7402 verbatim
end BinaryAllWordRankOrder


-- @@ L7404-7404 verbatim
namespace BinarySelectedIrreducibleWordTM


-- @@ L7406-7406 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L7407-7407 verbatim
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.CNFBoundedRecordFoldTM

-- @@ L7408-7408 verbatim
open GapCVP.CNFFiveFamilyOriginalIndexedBitTM

-- @@ L7409-7409 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CLStructuralPrefixWriter

-- @@ L7410-7410 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryFieldBasis

-- @@ L7411-7411 verbatim
open GapCVP.BinaryModularReductionTM GapCVP.BinaryPhysicalWordRuntimeDegreeTM

-- @@ L7412-7412 verbatim
open GapCVP.BinarySourceConvolutionTM


-- @@ L7414-7421 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalCompositionComputer
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    BitTM (g ∘ f) :=
  GapCVP.TMComposition.computableInPolyTime first second


-- @@ L7423-7431 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalAppendComputer
    {first second : List Bool → List Bool}
    (firstComputer : BitTM first)
    (secondComputer : BitTM second) :
    BitTM
      (fun input => first input ++ second input) :=
  pointwiseAppendComputable firstComputer secondComputer


-- @@ L7433-7441 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDynamicCatalogueComputer
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record) :
    BitTM
      (maskDynamicGridRecordCatalogueOutput width computer) :=
  maskDynamicGridRecordCatalogueComputable width computer


-- @@ L7443-7450 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDynamicWidth
    {output : List Bool → List Bool}
    (computer : BitTM output) :
    SourceQaryMaskDynamicGridWidth where
  output := output
  computer := computer


-- @@ L7452-7459 verbatim
@[simp] theorem factor400BinaryIrreduciblePhysicalDynamicWidth_output
    {output : List Bool → List Bool}
    (computer : BitTM output)
    (input : List Bool) :
    (factor400BinaryIrreduciblePhysicalDynamicWidth computer).output input =
      output input := by
  unfold factor400BinaryIrreduciblePhysicalDynamicWidth
  rfl


-- @@ L7461-7466 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFalseComputer :
    BitTM
      (fun _ : List Bool => [false]) :=
  sourceFixedWordComputable [false]


-- @@ L7468-7473 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalTrueComputer :
    BitTM
      (fun _ : List Bool => [true]) :=
  sourceFixedWordComputable [true]


-- @@ L7475-7480 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalNaturalWriterComputer :
    BitTM
      (fun input : List Bool => Computability.encodeNat input.length) :=
  factor400BinaryPhysicalWordNaturalWriterComputer


-- @@ L7482-7486 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalDropHeadComputer :
    BitTM List.tail :=
  factor400BinaryPhysicalWordDropHeadComputer


-- @@ L7488-7493 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFieldContentsComputer :
    BitTM
      firstFieldContents :=
  firstFieldContentsComputable


-- @@ L7495-7500 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer :
    BitTM
      firstFieldSuffix :=
  firstFieldSuffixComputable


-- @@ L7502-7507 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalPrefixWriterComputer :
    BitTM
      lengthPrefixedWord :=
  structuralPrefixWriterComputable


-- @@ L7509-7512 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIrreduciblePhysicalComputedPrefixOutput
    (word : List Bool → List Bool) : List Bool → List Bool :=
  lengthPrefixedWord ∘ word


-- @@ L7514-7523 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalComputedPrefixComputer
    {word : List Bool → List Bool}
    (computer : BitTM word) :
    BitTM
      (binaryIrreduciblePhysicalComputedPrefixOutput word) :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := word) (g := lengthPrefixedWord)
    computer factor400BinaryIrreduciblePhysicalPrefixWriterComputer


-- @@ L7525-7531 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalSquareComputer :
    BitTM
      (fun input : List Bool =>
        List.replicate ((Polynomial.X ^ 2).eval input.length) true) :=
  polynomialValueUnaryComputable (Polynomial.X ^ 2)


-- @@ L7533-7538 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreduciblePhysicalConvolutionComputer :
    BitTM
      binarySourceRawConvolutionWord :=
  factor400BinarySourceRawConvolutionComputable


-- @@ L7540-7543 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinaryIrreducibleRankUnary
    (input : List Bool) : List Bool :=
  firstFieldContents input


-- @@ L7545-7550 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankUnaryComputable :
    BitTM
      factor400BinaryIrreducibleRankUnary :=
  factor400BinaryIrreduciblePhysicalFieldContentsComputer


-- @@ L7552-7555 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIrreducibleRankOriginal :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L7557-7565 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankOriginalComputable :
    BitTM
      binaryIrreducibleRankOriginal :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := firstFieldSuffix) (g := firstFieldSuffix)
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer
    factor400BinaryIrreduciblePhysicalFieldSuffixComputer


-- @@ L7567-7573 verbatim
theorem factor400BinaryIrreducibleRankOriginal_valid
    (rank auxiliary source : List Bool) :
    binaryIrreducibleRankOriginal
      (lengthPrefixedWord rank ++
        lengthPrefixedWord auxiliary ++ source) = source := by
  simp only [binaryIrreducibleRankOriginal, List.append_assoc, Function.comp_apply,
      firstFieldSuffix_valid]


-- @@ L7575-7579 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIrreducibleRankBinary :
    List Bool → List Bool :=
  (fun input : List Bool => Computability.encodeNat input.length) ∘
    factor400BinaryIrreducibleRankUnary


-- @@ L7581-7590 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleRankBinaryComputable :
    BitTM
      binaryIrreducibleRankBinary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := factor400BinaryIrreducibleRankUnary)
    (g := fun input : List Bool => Computability.encodeNat input.length)
    factor400BinaryIrreducibleRankUnaryComputable
    factor400BinaryIrreduciblePhysicalNaturalWriterComputer


-- @@ L7592-7595 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIrreducibleCoefficientOuterSource :
    List Bool → List Bool :=
  binaryIrreducibleRankOriginal


-- @@ L7597-7602 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientOuterSourceComputable :
    BitTM
      binaryIrreducibleCoefficientOuterSource :=
  factor400BinaryIrreducibleRankOriginalComputable


-- @@ L7604-7608 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinaryIrreducibleCoefficientRankBinary :
    List Bool → List Bool :=
  binaryIrreducibleRankBinary ∘
    binaryIrreducibleCoefficientOuterSource


-- @@ L7610-7619 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientRankBinaryComputable :
    BitTM
      factor400BinaryIrreducibleCoefficientRankBinary :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    (f := binaryIrreducibleCoefficientOuterSource)
    (g := binaryIrreducibleRankBinary)
    factor400BinaryIrreducibleCoefficientOuterSourceComputable
    factor400BinaryIrreducibleRankBinaryComputable


-- @@ L7621-7626 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIrreducibleCoefficientBitWord :
    List Bool → List Bool :=
  fiveFamilyOriginalDynamicBitWord
    factor400BinaryIrreducibleRankUnary
    factor400BinaryIrreducibleCoefficientRankBinary


-- @@ L7628-7635 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinaryIrreducibleCoefficientBitComputable :
    BitTM
      binaryIrreducibleCoefficientBitWord :=
  fiveOriginalDynamicBitComputable
    factor400BinaryIrreducibleRankUnaryComputable
    factor400BinaryIrreducibleCoefficientRankBinaryComputable


-- @@ L7637-7651 verbatim
private theorem factor400Irreducible_encodePosNum_eq_bits (value : PosNum) :
    Computability.encodePosNum value = Nat.bits (value : ℕ) := by
  induction value with
  | one => rfl
  | bit0 value ih =>
      change false :: Computability.encodePosNum value =
        Nat.bits ((value : ℕ) + (value : ℕ))
      rw [← two_mul, Nat.bit0_bits]
      · exact congrArg (List.cons false) ih
      · exact Nat.ne_of_gt (PosNum.cast_pos value)
  | bit1 value ih =>
      change true :: Computability.encodePosNum value =
        Nat.bits ((value : ℕ) + (value : ℕ) + 1)
      rw [← two_mul, Nat.bit1_bits]
      exact congrArg (List.cons true) ih


-- @@ L7653-7668 verbatim
private theorem factor400Irreducible_encodeNat_eq_bits (value : ℕ) :
    Computability.encodeNat value = Nat.bits value := by
  change Computability.encodeNum (value : Num) = Nat.bits value
  generalize hnum : (value : Num) = numeral
  have hvalue : (numeral : ℕ) = value := by
    rw [← hnum]
    exact Num.to_of_nat value
  cases numeral with
  | zero =>
      have hz : value = 0 := by simpa only [Num.cast_zero'] using hvalue.symm
      subst value
      rfl
  | pos positive =>
      change Computability.encodePosNum positive = Nat.bits value
      rw [← hvalue]
      exact factor400Irreducible_encodePosNum_eq_bits positive


-- @@ L7670-7676 verbatim
theorem factor400Irreducible_encodeNat_drop_head
    (value index : ℕ) :
    ((Computability.encodeNat value).drop index).headD false =
      value.testBit index := by
  rw [factor400Irreducible_encodeNat_eq_bits,
    Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  simp only [List.headD_eq_head?_getD, List.head?_drop, Bool.default_bool]


-- @@ L7678-7687 verbatim
theorem factor400BinaryIrreducibleFiniteWordBits_indexedWord
    (degree : ℕ) (rank : Fin (2 ^ degree)) :
    finiteWordBits (indexedWord degree rank) =
      (List.range degree).map
        (fun bitRank => rank.val.testBit bitRank) := by
  apply List.ext_getElem
  · simp only [finiteWordBits, List.length_map, List.length_finRange, List.length_range]
  · intro bitRank hleft hright
    simp only [finiteWordBits, List.getElem_map, indexedWord, List.getElem_finRange, Fin.cast_mk,
        List.getElem_range]


-- @@ L7689-7696 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIndexedNoProperFactorsBit
    (degree rank : ℕ) : Bool :=
  if h : rank < 2 ^ degree then
    GapCVP.Core.EffectiveBinaryField.noProperFactors degree
      (indexedWord degree ⟨rank, h⟩)
  else
    false


-- @@ L7698-7701 verbatim
/-- GapCVP reduction support. -/
@[expose] def binarySourceIrreducibleFactorPairCandidateSource :
    List Bool → List Bool :=
  factor400BinarySourceSkipFields 2


-- @@ L7703-7708 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinarySourceIrreducibleFactorPairCandidateSourceComputable :
    BitTM
      binarySourceIrreducibleFactorPairCandidateSource :=
  binarySourceSkipFieldsComputable 2


-- @@ L7710-7714 verbatim
/-- GapCVP reduction support. -/
@[expose] def factor400BinarySourceIrreducibleFactorPairOriginalSource :
    List Bool → List Bool :=
  binaryIrreducibleRankOriginal ∘
    binarySourceIrreducibleFactorPairCandidateSource


-- @@ L7716-7723 verbatim
/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    factor400BinarySourceIrreducibleFactorPairOriginalSourceComputable :
    BitTM
      factor400BinarySourceIrreducibleFactorPairOriginalSource :=
  factor400BinaryIrreduciblePhysicalCompositionComputer
    factor400BinarySourceIrreducibleFactorPairCandidateSourceComputable
    factor400BinaryIrreducibleRankOriginalComputable


-- @@ L7725-7729 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIndexedIrreducibleCandidateMarkers
    (degree : ℕ) : List Bool :=
  (List.range (2 ^ degree)).map
    (binaryIndexedNoProperFactorsBit degree)


-- @@ L7731-7731 verbatim
end BinarySelectedIrreducibleWordTM


-- @@ L7733-7733 verbatim
namespace BinarySelectedIrreducibleFactorCorrectness


-- @@ L7735-7735 verbatim
open Turing GapCVP.BinaryFieldBasis

-- @@ L7736-7736 verbatim
open GapCVP.BinaryAllWordRankOrder GapCVP.Core.EffectiveBinaryField


-- @@ L7738-7753 verbatim
/-- GapCVP reduction support. -/
@[expose] def binaryIndexedProperFactorPairBit
    (degree : ℕ) (lower : Word degree) (rank : ℕ) : Bool :=
  if h : rank < (2 ^ degree) ^ 2 then
    have hq : 0 < 2 ^ degree := by positivity
    let first : Fin (2 ^ degree) :=
      ⟨rank / (2 ^ degree), by
        apply (Nat.div_lt_iff_lt_mul hq).2
        simpa only [pow_two] using h⟩
    let second : Fin (2 ^ degree) :=
      ⟨rank % (2 ^ degree), Nat.mod_lt rank hq⟩
    decide
      (multiplyWords (indexedWord degree first)
        (indexedWord degree second) = monicWord lower)
  else
    false


-- @@ L7755-7761 verbatim
private theorem factor400BinaryIndexedWord_surjective
    (degree : ℕ) (word : Word degree) :
    ∃ rank : Fin (2 ^ degree), indexedWord degree rank = word := by
  have hword := GapCVP.Core.EffectiveBinaryField.mem_allWords word
  rw [allWords_eq_finRange_indexedWord degree] at hword
  obtain ⟨rank, _, hrank⟩ := List.mem_map.mp hword
  exact ⟨rank, hrank⟩


-- @@ L7763-7777 verbatim
private theorem factor400BinaryProperFactorPairRank_lt
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    first.val * 2 ^ degree + second.val < (2 ^ degree) ^ 2 := by
  calc
    first.val * 2 ^ degree + second.val <
        first.val * 2 ^ degree + 2 ^ degree :=
      Nat.add_lt_add_left second.isLt _
    _ = (first.val + 1) * 2 ^ degree := by
      simp only [Nat.add_mul, one_mul]
    _ ≤ (2 ^ degree) * (2 ^ degree) :=
      Nat.mul_le_mul_right (2 ^ degree)
        (Nat.succ_le_of_lt first.isLt)
    _ = (2 ^ degree) ^ 2 := by
      rw [pow_two]


-- @@ L7779-7786 verbatim
private theorem factor400BinaryProperFactorPairRank_div
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    (first.val * 2 ^ degree + second.val) / (2 ^ degree) = first.val := by
  have hq : 0 < 2 ^ degree := by positivity
  rw [Nat.mul_comm first.val (2 ^ degree),
    Nat.mul_add_div hq, Nat.div_eq_of_lt second.isLt]
  simp only [add_zero]


-- @@ L7788-7793 verbatim
private theorem factor400BinaryProperFactorPairRank_mod
    {degree : ℕ}
    (first second : Fin (2 ^ degree)) :
    (first.val * 2 ^ degree + second.val) % (2 ^ degree) = second.val := by
  rw [Nat.mul_add_mod' first.val (2 ^ degree) second.val,
    Nat.mod_eq_of_lt second.isLt]


-- @@ L7795-7808 verbatim
private theorem factor400BinaryIndexedProperFactorPairBit_rank
    {degree : ℕ} (lower : Word degree)
    (first second : Fin (2 ^ degree)) :
    binaryIndexedProperFactorPairBit degree lower
        (first.val * 2 ^ degree + second.val) =
      decide
        (multiplyWords
          (indexedWord degree first)
          (indexedWord degree second) = monicWord lower) := by
  unfold binaryIndexedProperFactorPairBit
  rw [dite_eq_left (factor400BinaryProperFactorPairRank_lt first second)]
  dsimp
  simp only [factor400BinaryProperFactorPairRank_div first second,
    factor400BinaryProperFactorPairRank_mod first second, Fin.eta]


-- @@ L7810-7851 verbatim
theorem factor400BinaryIndexedProperFactorPairMarkers_find_none_iff
    (degree : ℕ) (lower : Word degree) :
    ((List.range ((2 ^ degree) ^ 2)).map
        (binaryIndexedProperFactorPairBit degree lower)).findIdx?
          id = none ↔
      ∀ first second : Word degree,
        multiplyWords first second ≠ monicWord lower := by
  constructor
  · intro hnone first second
    obtain ⟨firstRank, hfirst⟩ :=
      factor400BinaryIndexedWord_surjective degree first
    obtain ⟨secondRank, hsecond⟩ :=
      factor400BinaryIndexedWord_surjective degree second
    let rank := firstRank.val * 2 ^ degree + secondRank.val
    have hbound : rank < (2 ^ degree) ^ 2 :=
      factor400BinaryProperFactorPairRank_lt firstRank secondRank
    have hmember :
        binaryIndexedProperFactorPairBit degree lower rank ∈
          (List.range ((2 ^ degree) ^ 2)).map
            (binaryIndexedProperFactorPairBit degree lower) :=
      List.mem_map.mpr
        ⟨rank, List.mem_range.mpr hbound, rfl⟩
    have hfalse := (List.findIdx?_eq_none_iff.mp hnone)
      (binaryIndexedProperFactorPairBit degree lower rank) hmember
    change
      binaryIndexedProperFactorPairBit degree lower rank = false
        at hfalse
    dsimp [rank] at hfalse
    rw [factor400BinaryIndexedProperFactorPairBit_rank] at hfalse
    rw [hfirst, hsecond] at hfalse
    exact of_decide_eq_false hfalse
  · intro hnone
    apply List.findIdx?_eq_none_iff.mpr
    intro marker hmember
    obtain ⟨rank, hrank, hmarker⟩ := List.mem_map.mp hmember
    subst marker
    have hbound : rank < (2 ^ degree) ^ 2 :=
      List.mem_range.mp hrank
    unfold binaryIndexedProperFactorPairBit
    rw [dite_eq_left hbound]
    dsimp
    exact decide_eq_false (hnone _ _)


-- @@ L7853-7853 verbatim
end BinarySelectedIrreducibleFactorCorrectness



-- @@ L7856-7856 verbatim
end GapCVP


-- @@ L7858-7858 verbatim
end
