/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part10
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.InformationTheory.Hamming


-- @@ L13-13 verbatim
/-! # GapCVP proof, part 11 -/


-- @@ L15-15 verbatim
public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open StateTransition (EvalsToInTime)

-- @@ L20-20 verbatim
open scoped BigOperators


-- @@ L22-22 verbatim
namespace GapCVP


-- @@ L24-24 verbatim
open GapCVP.TraceGolf (oneStep rebound)


-- @@ L26-26 verbatim
namespace BinaryPhysicalLagrangeCoefficientTM


-- @@ L28-28 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.BinaryExplicitAffineRows

-- @@ L29-29 verbatim
open GapCVP.BinarySourceFieldMultiplicationTM GapCVP.BinaryModularReductionTM

-- @@ L30-30 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L32-37 verbatim
/-- GapCVP reduction support. -/
structure SourcePhysicalLagrangeWordComputer where
  /-- GapCVP reduction support. -/
  output : List Bool → List Bool
  /-- GapCVP reduction support. -/
  computer : BitTM output


-- @@ L39-40 verbatim
private abbrev sourcePhysicalLagrangeOriginalSource : List Bool → List Bool :=
  sourceExplicitAffineCellOriginalSource


-- @@ L42-45 verbatim
private noncomputable def sourcePhysicalLagrangeOriginalSourceComputable :
    BitTM
      sourcePhysicalLagrangeOriginalSource :=
  sourceExplicitAffineCellOriginalSourceComputable


-- @@ L47-51 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourcePhysicalLagrangePrefixedOutput
    (worker : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (worker.output input)


-- @@ L53-62 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalLagrangePrefixedComputable
    (worker : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (sourcePhysicalLagrangePrefixedOutput worker) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    worker.computer structuralPrefixWriterComputable
  change BitTM
    (fun input => lengthPrefixedWord (worker.output input))
  simpa only [Function.comp_def] using hphysical


-- @@ L64-69 verbatim
private def sourcePhysicalLagrangeMultiplyQuery
    (lower left right : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  factor400BinarySourceFieldQuery
    (lower.output input) (left.output input) (right.output input)
    (sourcePhysicalLagrangeOriginalSource input)


-- @@ L71-88 verbatim
private noncomputable def sourcePhysicalLagrangeMultiplyQueryComputable
    (lower left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (sourcePhysicalLagrangeMultiplyQuery lower left right) := by
  have hright := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable right)
    sourcePhysicalLagrangeOriginalSourceComputable
  have hmiddle := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable left) hright
  have hcomplete := pointwiseAppendComputable
    (sourcePhysicalLagrangePrefixedComputable lower) hmiddle
  change BitTM
    (fun input => factor400BinarySourceFieldQuery
      (lower.output input) (left.output input) (right.output input)
      (sourcePhysicalLagrangeOriginalSource input))
  simpa only [factor400BinarySourceFieldQuery, List.append_assoc,
      sourcePhysicalLagrangePrefixedOutput] using
      hcomplete


-- @@ L90-95 verbatim
/-- GapCVP reduction support. -/
def sourcePhysicalLagrangeMultiplyWord
    (lower left right : SourcePhysicalLagrangeWordComputer)
    (input : List Bool) : List Bool :=
  binarySourceMultiplyModWord
    (sourcePhysicalLagrangeMultiplyQuery lower left right input)


-- @@ L97-109 verbatim
/-- GapCVP reduction support. -/
noncomputable def sourcePhysicalLagrangeMultiplyComputable
    (multiplyComputer : BitTM binarySourceMultiplyModWord)
    (lower left right : SourcePhysicalLagrangeWordComputer) :
    BitTM
      (sourcePhysicalLagrangeMultiplyWord lower left right) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (sourcePhysicalLagrangeMultiplyQueryComputable lower left right)
    multiplyComputer
  change BitTM
    (fun input => binarySourceMultiplyModWord
      (sourcePhysicalLagrangeMultiplyQuery lower left right input))
  simpa only [Function.comp_def] using hphysical


-- @@ L111-143 verbatim
theorem sourcePhysicalLagrangeMultiplyWord_valid
    {degree : ℕ}
    (lowerWord leftWord rightWord :
      GapCVP.Core.EffectiveBinaryField.Word degree)
    (lower left right : SourcePhysicalLagrangeWordComputer)
    (row column : ℕ) (source : List Bool)
    (hlower : lower.output
      (affineCellQuery row column source) =
        finiteWordBits lowerWord)
    (hleft : left.output
      (affineCellQuery row column source) =
        finiteWordBits leftWord)
    (hright : right.output
      (affineCellQuery row column source) =
        finiteWordBits rightWord) :
    sourcePhysicalLagrangeMultiplyWord lower left right
        (affineCellQuery row column source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyMod
          lowerWord leftWord rightWord) := by
  unfold sourcePhysicalLagrangeMultiplyWord
    sourcePhysicalLagrangeMultiplyQuery
  rw [hlower, hleft, hright]
  change binarySourceMultiplyModWord
    (factor400BinarySourceFieldQuery
      (finiteWordBits lowerWord)
      (finiteWordBits leftWord)
      (finiteWordBits rightWord)
      (sourceExplicitAffineCellOriginalSource
        (affineCellQuery row column source))) = _
  rw [sourceExplicitAffineCellOriginalSource_query]
  exact binarySourceMultiplyModWord_valid
    lowerWord leftWord rightWord source


-- @@ L145-145 verbatim
end BinaryPhysicalLagrangeCoefficientTM


-- @@ L147-147 verbatim
namespace BinaryFieldInverseTM


-- @@ L149-149 verbatim
section


-- @@ L151-151 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L152-152 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L153-153 verbatim
open GapCVP.BinaryModularReductionTM GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L155-158 verbatim
/-- GapCVP reduction support. -/
@[expose] def binarySourceFieldInverseQuery
    (lower operand source : List Bool) : List Bool :=
  lengthPrefixedWord lower ++ lengthPrefixedWord operand ++ source


-- @@ L160-163 verbatim
/-- GapCVP reduction support. -/
def binarySourceFieldInverseSource
    (input : List Bool) : List Bool :=
  firstFieldSuffix (firstFieldSuffix input)


-- @@ L165-173 verbatim
/-- GapCVP reduction support. -/
noncomputable def factor400BinarySourceFieldInverseSourceComputable :
    BitTM
      binarySourceFieldInverseSource := by
  have h := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable
  change BitTM
    (fun input : List Bool => firstFieldSuffix (firstFieldSuffix input))
  exact h


-- @@ L175-180 verbatim
@[simp] theorem factor400BinarySourceFieldInverseSource_query
    (lower operand source : List Bool) :
    binarySourceFieldInverseSource
      (binarySourceFieldInverseQuery lower operand source) = source := by
  simp only [binarySourceFieldInverseSource, binarySourceFieldInverseQuery, List.append_assoc,
      firstFieldSuffix_valid]


-- @@ L182-188 verbatim
private def binarySourceFieldPowerPreparation
    (input : List Bool) : List Bool :=
  factor400BinarySourceFieldQuery
    (factor400BinarySourceLeftBits input)
    (factor400BinarySourceLowerBits input)
    (factor400BinarySourceRightBits input)
    (factor400BinarySourceFieldSuffix input)


-- @@ L190-212 verbatim
private noncomputable def factor400BinarySourceFieldPowerPreparationComputable :
    BitTM
      binarySourceFieldPowerPreparation := by
  have hlower := GapCVP.TMComposition.computableInPolyTime
    binarySourceLeftBitsComputable
    structuralPrefixWriterComputable
  have haccumulator := GapCVP.TMComposition.computableInPolyTime
    binarySourceLowerBitsComputable
    structuralPrefixWriterComputable
  have hoperand := GapCVP.TMComposition.computableInPolyTime
    binarySourceRightBitsComputable
    structuralPrefixWriterComputable
  have htail := pointwiseAppendComputable
    hoperand factor400BinarySourceFieldSuffixComputable
  have hright := pointwiseAppendComputable haccumulator htail
  have hcomplete := pointwiseAppendComputable hlower hright
  change BitTM
    (fun input =>
      lengthPrefixedWord (factor400BinarySourceLeftBits input) ++
      lengthPrefixedWord (factor400BinarySourceLowerBits input) ++
      lengthPrefixedWord (factor400BinarySourceRightBits input) ++
      factor400BinarySourceFieldSuffix input)
  simpa only [List.append_assoc, Function.comp_apply] using hcomplete


-- @@ L214-223 verbatim
@[simp] private theorem factor400BinarySourceFieldPowerPreparation_query
    (accumulator lower operand source : List Bool) :
    binarySourceFieldPowerPreparation
      (factor400BinarySourceFieldQuery
        accumulator lower operand source) =
      factor400BinarySourceFieldQuery
        lower accumulator operand source := by
  simp only [binarySourceFieldPowerPreparation, factor400BinarySourceLeftBits_query,
      factor400BinarySourceLowerBits_query, factor400BinarySourceRightBits_query,
          factor400BinarySourceFieldSuffix_query]


-- @@ L225-229 verbatim
/-- GapCVP reduction support. -/
def binarySourceFieldPowerCandidate
    (input : List Bool) : List Bool :=
  binarySourceMultiplyModWord
    (binarySourceFieldPowerPreparation input)


-- @@ L231-244 verbatim
/-- GapCVP reduction support. -/
noncomputable def factor400BinarySourceFieldPowerCandidateComputable
    (multiplyComputer :
      BitTM
        binarySourceMultiplyModWord) :
    BitTM
      binarySourceFieldPowerCandidate := by
  have h := GapCVP.TMComposition.computableInPolyTime
    factor400BinarySourceFieldPowerPreparationComputable multiplyComputer
  change BitTM
    (fun input : List Bool =>
      binarySourceMultiplyModWord
        (binarySourceFieldPowerPreparation input))
  exact h


-- @@ L246-261 verbatim
private theorem factor400BinarySourceFieldPowerCandidate_valid
    {degree : ℕ}
    (lower current operand : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    binarySourceFieldPowerCandidate
      (factor400BinarySourceFieldQuery
        (finiteWordBits current)
        (finiteWordBits lower)
        (finiteWordBits operand) source) =
      finiteWordBits
        (GapCVP.Core.EffectiveBinaryField.multiplyMod
          lower current operand) := by
  unfold binarySourceFieldPowerCandidate
  rw [factor400BinarySourceFieldPowerPreparation_query]
  exact binarySourceMultiplyModWord_valid
    lower current operand source


-- @@ L263-263 verbatim
end


-- @@ L265-265 verbatim
section


-- @@ L267-267 verbatim
open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder

-- @@ L268-268 verbatim
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.BinaryModularReductionTM

-- @@ L269-269 verbatim
open GapCVP.BinarySourceFieldMultiplicationTM


-- @@ L271-276 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourceFieldPowerStep {degree : ℕ}
    (lower operand : GapCVP.Core.EffectiveBinaryField.Word degree)
    (current : GapCVP.Core.EffectiveBinaryField.Word degree) :
    GapCVP.Core.EffectiveBinaryField.Word degree :=
  GapCVP.Core.EffectiveBinaryField.multiplyMod lower current operand


-- @@ L278-282 verbatim
/-- GapCVP reduction support. -/
@[expose] def sourceFieldPowerIterate {degree : ℕ}
    (lower operand : GapCVP.Core.EffectiveBinaryField.Word degree)
    (steps : ℕ) : GapCVP.Core.EffectiveBinaryField.Word degree :=
  ((sourceFieldPowerStep lower operand)^[steps]) operand


-- @@ L284-370 verbatim
private theorem factor400BinarySourceFieldPowerRotation_step
    {degree : ℕ}
    (lower current operand : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) :
    let anchor :=
      binarySourceFieldInverseQuery
        (finiteWordBits lower) (finiteWordBits operand) source
    sourceAnchoredGridRecordRotationOutput
        binarySourceFieldPowerCandidate
        (lengthPrefixedWord anchor ++
          lengthPrefixedWord (finiteWordBits current)) =
      lengthPrefixedWord anchor ++
        lengthPrefixedWord
          (finiteWordBits (sourceFieldPowerStep lower operand current)) := by
  dsimp
  let anchor :=
    binarySourceFieldInverseQuery
      (finiteWordBits lower) (finiteWordBits operand) source
  let state :=
    lengthPrefixedWord anchor ++
      lengthPrefixedWord (finiteWordBits current)
  have hpair :
      sourceAnchoredGridRankSourcePair state =
        factor400BinarySourceFieldQuery
          (finiteWordBits current)
          (finiteWordBits lower)
          (finiteWordBits operand) source := by
    unfold sourceAnchoredGridRankSourcePair
    dsimp only [state]
    rw [firstFieldSuffix_valid anchor
      (lengthPrefixedWord (finiteWordBits current))]
    rw [firstFieldContents_valid anchor
      (lengthPrefixedWord (finiteWordBits current))]
    have hcurrent :
        firstFieldContents
          (lengthPrefixedWord (finiteWordBits current)) =
          finiteWordBits current := by
      simpa only [List.append_nil] using
        firstFieldContents_valid (finiteWordBits current) []
    rw [hcurrent]
    simp only [anchor, factor400BinarySourceFieldQuery,
      binarySourceFieldInverseQuery, List.append_assoc]
  have hraw :
      sourceAnchoredGridRawCandidate
        binarySourceFieldPowerCandidate state =
      finiteWordBits (sourceFieldPowerStep lower operand current) := by
    unfold sourceAnchoredGridRawCandidate
    rw [hpair]
    simpa only [sourceFieldPowerStep] using
      factor400BinarySourceFieldPowerCandidate_valid
        lower current operand source
  have hfit :
      (finiteWordBits (sourceFieldPowerStep lower operand current)).length ≤
        anchor.length := by
    simp only [anchor, binarySourceFieldInverseQuery,
      List.length_append, lengthPrefixedWord_length,
      finiteWordBits, List.length_map, List.length_finRange]
    omega
  have hselector :
      sourceAnchoredGridCandidateSelector
        binarySourceFieldPowerCandidate state = true := by
    have hanchor : firstFieldContents state = anchor := by
      dsimp only [state]
      exact firstFieldContents_valid anchor
        (lengthPrefixedWord (finiteWordBits current))
    rw [sourceAnchoredGridCandidateSelector_eq, hraw, hanchor]
    exact decide_eq_true hfit
  have hguard :
      sourceAnchoredGridGuardedCandidate
        binarySourceFieldPowerCandidate state =
        finiteWordBits (sourceFieldPowerStep lower operand current) := by
    simp only [sourceAnchoredGridGuardedCandidate, hselector, hraw,
      ite_true]
  have hrotation :=
    sourceAnchoredGridRecordRotationOutput_records
      binarySourceFieldPowerCandidate anchor
      (finiteWordBits current) []
  simp only [List.append_nil] at hrotation
  have hguardRecords :
      sourceAnchoredGridGuardedCandidate
        binarySourceFieldPowerCandidate
        (lengthPrefixedWord anchor ++
          lengthPrefixedWord (finiteWordBits current)) =
        finiteWordBits (sourceFieldPowerStep lower operand current) := by
    exact hguard
  rw [hguardRecords] at hrotation
  exact hrotation


-- @@ L372-395 verbatim
theorem factor400BinarySourceFieldPowerRotation_iterate
    {degree : ℕ}
    (lower current operand : GapCVP.Core.EffectiveBinaryField.Word degree)
    (source : List Bool) (steps : ℕ) :
    let anchor :=
      binarySourceFieldInverseQuery
        (finiteWordBits lower) (finiteWordBits operand) source
    ((sourceAnchoredGridRecordRotationOutput
      binarySourceFieldPowerCandidate)^[steps])
      (lengthPrefixedWord anchor ++
        lengthPrefixedWord (finiteWordBits current)) =
      lengthPrefixedWord anchor ++
        lengthPrefixedWord
          (finiteWordBits
            (((sourceFieldPowerStep lower operand)^[steps]) current)) := by
  dsimp
  induction steps generalizing current with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ steps ih =>
      rw [Function.iterate_succ_apply,
        factor400BinarySourceFieldPowerRotation_step
          lower current operand source,
        ih (sourceFieldPowerStep lower operand current),
        Function.iterate_succ_apply]


-- @@ L397-397 verbatim
end


-- @@ L399-399 verbatim
end BinaryFieldInverseTM


-- @@ L401-401 verbatim
end GapCVP


-- @@ L403-403 verbatim
end
