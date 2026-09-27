/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part12C


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 12, continuation 04 -/


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
namespace GaussianAdaptivePhysicalColumnCellUpdateTM


-- @@ L27-27 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding


-- @@ L29-29 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.CLStructuralPrefixWriter


-- @@ L31-31 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.BinaryExplicitAffineRows


-- @@ L33-33 verbatim
open GapCVP.GaussianRowWorker GapCVP.GaussianAdaptivePivotStepTM


-- @@ L35-35 verbatim
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePackedStateLookupTM


-- @@ L37-37 verbatim
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM


-- @@ L39-39 verbatim
open GapCVP.GaussianAdaptivePhysicalColumnCellUpdateSemantics


-- @@ L41-41 verbatim
open GapCVP.SourceFourFamilyBooleanPredicateTM


-- @@ L43-43 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM


-- @@ L45-45 verbatim
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM


-- @@ L47-55 verbatim
private def gaussianPhysicalColumnSwappedCheckWord
    (column : List Bool → List Bool) : List Bool → List Bool :=
  gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow column)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary column)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary column)


-- @@ L57-68 verbatim
private noncomputable def gaussianPhysicalColumnSwappedCheckComputable
    {column : List Bool → List Bool}
    (hcolumn : BitTM column) :
    BitTM
      (gaussianPhysicalColumnSwappedCheckWord column) :=
  gaussianPhysicalColumnSwappedBitComputable
    (gaussianPhysicalColumnDynamicCheckComputable
      sourceExplicitAffineCellRowComputable hcolumn)
    (gaussianPhysicalColumnDynamicCheckComputable
      gaussianPhysicalColumnNextPivotUnaryComputable hcolumn)
    (gaussianPhysicalColumnDynamicCheckComputable
      gaussianPhysicalColumnCandidateUnaryComputable hcolumn)


-- @@ L70-77 verbatim
private def gaussianPhysicalColumnSwappedRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)


-- @@ L79-91 verbatim
private noncomputable def gaussianPhysicalColumnSwappedRhsComputable :
    BitTM
      gaussianPhysicalColumnSwappedRhsWord :=
  gaussianPhysicalColumnSwappedBitComputable
    (gaussianPhysicalColumnDynamicRhsComputable
      sourceExplicitAffineCellRowComputable
      sourceExplicitAffineCellColumnComputable)
    (gaussianPhysicalColumnDynamicRhsComputable
      gaussianPhysicalColumnNextPivotUnaryComputable
      sourceExplicitAffineCellColumnComputable)
    (gaussianPhysicalColumnDynamicRhsComputable
      gaussianPhysicalColumnCandidateUnaryComputable
      sourceExplicitAffineCellColumnComputable)


-- @@ L93-98 verbatim
private def gaussianPhysicalColumnClearGateWord : List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive)


-- @@ L100-107 verbatim
private noncomputable def gaussianPhysicalColumnClearGateComputable :
    BitTM
      gaussianPhysicalColumnClearGateWord :=
  fourFamilyBooleanAndComputable
    (fourFamilyBooleanNotOutputComputable
      gaussianPhysicalColumnRowIsPivotComputable)
    (gaussianPhysicalColumnSwappedCheckComputable
      gaussianPhysicalColumnCellActiveComputable)


-- @@ L109-112 verbatim
private def gaussianPhysicalColumnCandidateCheckWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicCheckWord
    gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn


-- @@ L114-119 verbatim
private noncomputable def gaussianPhysicalColumnCandidateCheckComputable :
    BitTM
      gaussianPhysicalColumnCandidateCheckWord :=
  gaussianPhysicalColumnDynamicCheckComputable
    gaussianPhysicalColumnCandidateUnaryComputable
    sourceExplicitAffineCellColumnComputable


-- @@ L121-124 verbatim
private def gaussianPhysicalColumnCandidateRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicRhsWord
    gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn


-- @@ L126-131 verbatim
private noncomputable def gaussianPhysicalColumnCandidateRhsComputable :
    BitTM
      gaussianPhysicalColumnCandidateRhsWord :=
  gaussianPhysicalColumnDynamicRhsComputable
    gaussianPhysicalColumnCandidateUnaryComputable
    sourceExplicitAffineCellColumnComputable


-- @@ L133-139 verbatim
private def gaussianPhysicalColumnPivotUpdatedCheckWord : List Bool → List Bool :=
  sourceExplicitAffineXorBits
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord)


-- @@ L141-149 verbatim
private noncomputable def gaussianPhysicalColumnPivotUpdatedCheckComputable :
    BitTM
      gaussianPhysicalColumnPivotUpdatedCheckWord :=
  sourceExplicitAffineXorBitsComputable
    (gaussianPhysicalColumnSwappedCheckComputable
      sourceExplicitAffineCellColumnComputable)
    (fourFamilyBooleanAndComputable
      gaussianPhysicalColumnClearGateComputable
      gaussianPhysicalColumnCandidateCheckComputable)


-- @@ L151-155 verbatim
private def gaussianPhysicalColumnPivotUpdatedRhsWord : List Bool → List Bool :=
  sourceExplicitAffineXorBits gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord)


-- @@ L157-164 verbatim
private noncomputable def gaussianPhysicalColumnPivotUpdatedRhsComputable :
    BitTM
      gaussianPhysicalColumnPivotUpdatedRhsWord :=
  sourceExplicitAffineXorBitsComputable
    gaussianPhysicalColumnSwappedRhsComputable
    (fourFamilyBooleanAndComputable
      gaussianPhysicalColumnClearGateComputable
      gaussianPhysicalColumnCandidateRhsComputable)


-- @@ L166-168 verbatim
private def gaussianPhysicalColumnOriginalCheckWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicCheckWord
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn


-- @@ L170-175 verbatim
private noncomputable def gaussianPhysicalColumnOriginalCheckComputable :
    BitTM
      gaussianPhysicalColumnOriginalCheckWord :=
  gaussianPhysicalColumnDynamicCheckComputable
    sourceExplicitAffineCellRowComputable
    sourceExplicitAffineCellColumnComputable


-- @@ L177-179 verbatim
private def gaussianPhysicalColumnOriginalRhsWord : List Bool → List Bool :=
  gaussianPhysicalColumnDynamicRhsWord
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn


-- @@ L181-186 verbatim
private noncomputable def gaussianPhysicalColumnOriginalRhsComputable :
    BitTM
      gaussianPhysicalColumnOriginalRhsWord :=
  gaussianPhysicalColumnDynamicRhsComputable
    sourceExplicitAffineCellRowComputable
    sourceExplicitAffineCellColumnComputable


-- @@ L188-193 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedCheckWord : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotUpdatedCheckWord
    gaussianPhysicalColumnOriginalCheckWord


-- @@ L195-202 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedCheckComputable :
    BitTM
      gaussianPhysicalColumnUpdatedCheckWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotSelectionComputable
    gaussianPhysicalColumnPivotUpdatedCheckComputable
    gaussianPhysicalColumnOriginalCheckComputable


-- @@ L204-209 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedRhsWord : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotUpdatedRhsWord
    gaussianPhysicalColumnOriginalRhsWord


-- @@ L211-218 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedRhsComputable :
    BitTM
      gaussianPhysicalColumnUpdatedRhsWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotSelectionComputable
    gaussianPhysicalColumnPivotUpdatedRhsComputable
    gaussianPhysicalColumnOriginalRhsComputable


-- @@ L220-227 verbatim
private theorem gaussianPhysicalColumnBinaryAdd_decide
    (first second : ZMod 2) :
    decide (first + second = (1 : ZMod 2)) =
      Bool.xor (decide (first = (1 : ZMod 2)))
        (decide (second = (1 : ZMod 2))) := by
  rcases effectiveBinary_eq_zero_or_one first with hfirst | hfirst <;>
    rcases effectiveBinary_eq_zero_or_one second with hsecond | hsecond <;>
    simp [hfirst, hsecond]


-- @@ L229-264 verbatim
private theorem gaussianPhysicalColumnSwapFormula
    {m : ℕ} (row candidate pivot : Fin m)
    (bit : Fin m → Bool) :
    ((decide (row.val = candidate.val) && bit pivot) ||
      ((decide (row.val = pivot.val) && bit candidate) ||
        (((!decide (row.val = candidate.val)) &&
          (!decide (row.val = pivot.val))) && bit row))) =
      bit (Equiv.swap candidate pivot row) := by
  by_cases hcandidate : row = candidate
  · subst row
    by_cases equal : candidate = pivot
    · subst pivot
      simp only [decide_true, Bool.true_and, Bool.not_true, Bool.and_self, Bool.false_and,
          Bool.or_false,
          Bool.or_self, Equiv.swap_self, Equiv.refl_apply]
    · have different : candidate.val ≠ pivot.val := by
        intro h
        exact equal (Fin.ext h)
      simp only [decide_true, Bool.true_and, different, decide_false, Bool.false_and,
          Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.or_self, Bool.or_false, Equiv.swap_apply_left]
  · have hcandidateVal : row.val ≠ candidate.val := by
      intro equal
      exact hcandidate (Fin.ext equal)
    by_cases hpivot : row = pivot
    · subst row
      simp only [hcandidateVal, decide_false, Bool.false_and, decide_true, Bool.true_and,
          Bool.not_false,
          Bool.not_true, Bool.and_false, Bool.or_false, Bool.false_or, Equiv.swap_apply_right]
    · have hpivotVal : row.val ≠ pivot.val := by
        intro equal
        exact hpivot (Fin.ext equal)
      rw [Equiv.swap_apply_of_ne_of_ne hcandidate hpivot]
      simp only [hcandidateVal, decide_false, Bool.false_and, hpivotVal, Bool.not_false,
          Bool.and_self,
          Bool.true_and, Bool.false_or]


-- @@ L266-282 verbatim
private theorem gaussianPhysicalColumnDecisionWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnDecisionWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      match findPivotOption state active with
      | none => [false]
      | some candidate => true :: List.replicate candidate.val true := by
  have hrows : 0 < m := by
    have hlt := row.isLt
    omega
  unfold gaussianPhysicalColumnDecisionWord
  rw [Function.comp_apply,
    gaussianPhysicalColumnDecisionQuery_query]
  exact gaussianPhysicalPivotDecisionOutput_effective
    state source active hrows


-- @@ L284-296 verbatim
private theorem gaussianPhysicalColumnCandidateUnary_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (candidate : Fin m)
    (found : findPivotOption state active = some candidate) :
    gaussianPhysicalColumnCandidateUnary
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate candidate.val true := by
  unfold gaussianPhysicalColumnCandidateUnary
  rw [Function.comp_apply,
    gaussianPhysicalColumnDecisionWord_effective
      state source row column active, found]
  simp only [List.tail_cons]


-- @@ L298-310 verbatim
theorem gaussianPhysicalColumnPivotPresent_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnPivotPresent
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      (findPivotOption state active).isSome := by
  unfold gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnPivotPresentWord
  simp only [Function.comp_apply]
  rw [gaussianPhysicalColumnDecisionWord_effective
    state source row column active]
  cases findPivotOption state active <;> rfl


-- @@ L312-329 verbatim
private theorem gaussianPhysicalColumnRowIsCandidateWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (candidate : Fin m)
    (found : findPivotOption state active = some candidate) :
    gaussianPhysicalColumnRowIsCandidateWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row.val = candidate.val)] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  exact fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnCandidateUnary
    input row.val candidate.val
    (gaussianPhysicalColumnCellRow_query row.val column.val active.val
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)


-- @@ L331-350 verbatim
private theorem gaussianPhysicalColumnRowIsPivotWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) (pivot : Fin m)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnRowIsPivotWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row.val = pivot.val)] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  apply fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalColumnCellRow gaussianPhysicalColumnNextPivotUnary
    input row.val pivot.val
  · exact gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  · simpa only [boundary] using
      gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val


-- @@ L352-430 verbatim
private theorem gaussianPhysicalColumnSwappedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active selected : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val)
    (columnWorker : List Bool → List Bool)
    (selectedWord :
      columnWorker
          (gaussianPhysicalColumnCellQuery
            row.val column.val active.val
            (effectiveGaussianPackedStateWord state source)) =
        List.replicate selected.val true) :
    gaussianPhysicalColumnSwappedCheckWord columnWorker
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((swapRows state.system candidate pivot).check row selected =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have horiginal := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCellRow columnWorker
    row selected hstate
    (gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source))
    selectedWord
  have hnext : gaussianPhysicalColumnNextPivotUnary input =
      List.replicate pivot.val true := by
    simpa only [boundary] using
      (gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val)
  have hpivot := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnNextPivotUnary columnWorker
    pivot selected hstate hnext selectedWord
  have hcandidate := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCandidateUnary columnWorker
    candidate selected hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    selectedWord
  have hrowCandidate :=
    gaussianPhysicalColumnRowIsCandidateWord_effective
      state source row column active candidate found
  have hrowPivot := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hswap := gaussianPhysicalColumnSwappedBitWord_bits
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary columnWorker)
    input (decide (row.val = candidate.val))
    (decide (row.val = pivot.val))
    (decide (state.system.check row selected = (1 : ZMod 2)))
    (decide (state.system.check pivot selected = (1 : ZMod 2)))
    (decide (state.system.check candidate selected = (1 : ZMod 2)))
    hrowCandidate hrowPivot horiginal hpivot hcandidate
  change gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCellRow columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnNextPivotUnary columnWorker)
    (gaussianPhysicalColumnDynamicCheckWord
      gaussianPhysicalColumnCandidateUnary columnWorker)
    input = _
  rw [hswap]
  exact congrArg (fun bit : Bool => [bit])
    (gaussianPhysicalColumnSwapFormula row candidate pivot
      (fun current =>
        decide (state.system.check current selected = (1 : ZMod 2))))


-- @@ L432-506 verbatim
private theorem gaussianPhysicalColumnSwappedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnSwappedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((swapRows state.system candidate pivot).rhs row =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have horiginal := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCellRow
    gaussianPhysicalColumnCellColumn row column hstate
    (gaussianPhysicalColumnCellRow_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source))
    hcolumn
  have hnext : gaussianPhysicalColumnNextPivotUnary input =
      List.replicate pivot.val true := by
    simpa only [boundary] using
      (gaussianPhysicalColumnNextPivotUnary_query
        state source row.val column.val active.val)
  have hpivot := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnNextPivotUnary
    gaussianPhysicalColumnCellColumn pivot column hstate
    hnext hcolumn
  have hcandidate := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hrowCandidate :=
    gaussianPhysicalColumnRowIsCandidateWord_effective
      state source row column active candidate found
  have hrowPivot := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hswap := gaussianPhysicalColumnSwappedBitWord_bits
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)
    input (decide (row.val = candidate.val))
    (decide (row.val = pivot.val))
    (decide (state.system.rhs row = (1 : ZMod 2)))
    (decide (state.system.rhs pivot = (1 : ZMod 2)))
    (decide (state.system.rhs candidate = (1 : ZMod 2)))
    hrowCandidate hrowPivot horiginal hpivot hcandidate
  change gaussianPhysicalColumnSwappedBitWord
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCellRow gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnNextPivotUnary gaussianPhysicalColumnCellColumn)
    (gaussianPhysicalColumnDynamicRhsWord
      gaussianPhysicalColumnCandidateUnary gaussianPhysicalColumnCellColumn)
    input = _
  rw [hswap]
  exact congrArg (fun bit : Bool => [bit])
    (gaussianPhysicalColumnSwapFormula row candidate pivot
      (fun current => decide (state.system.rhs current = (1 : ZMod 2))))


-- @@ L508-559 verbatim
private theorem gaussianPhysicalColumnClearGateWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnClearGateWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (row ≠ pivot ∧
        (swapRows state.system candidate pivot).check row active =
          (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnRowIsPivotWord_effective
    state source row column active pivot boundary
  have hnot := fourFamilyBooleanNotOutput_bit
    gaussianPhysicalColumnRowIsPivotWord input
    (decide (row.val = pivot.val)) hrow
  have hactive := gaussianPhysicalColumnSwappedCheckWord_effective
    state source row column active active candidate pivot
    found boundary gaussianPhysicalColumnCellActive
    (gaussianPhysicalColumnCellActive_query
      row.val column.val active.val
      (effectiveGaussianPackedStateWord state source))
  have hand := fourFamilyBooleanAndOutput_bits
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive)
    input (!(decide (row.val = pivot.val)))
    (decide
      ((swapRows state.system candidate pivot).check row active =
        (1 : ZMod 2))) hnot hactive
  change sourceFourFamilyBooleanAndOutput
    (sourceFourFamilyBooleanNotOutput
      gaussianPhysicalColumnRowIsPivotWord)
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellActive) input = _
  rw [hand]
  by_cases heq : row = pivot
  · subst row
    simp only [decide_true, Bool.not_true, Bool.false_and, ne_eq, not_true_eq_false, false_and,
        decide_false]
  · have hv : row.val ≠ pivot.val := by
      intro h
      exact heq (Fin.ext h)
    by_cases hbit :
        (swapRows state.system candidate pivot).check row active =
          (1 : ZMod 2) <;>
      simp [heq, hv, hbit]


-- @@ L561-644 verbatim
private theorem gaussianPhysicalColumnPivotUpdatedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnPivotUpdatedCheckWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((clearTargets pivot active (List.finRange m)
          (applyOperation state (.swap candidate pivot))).system.check
            row column = (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  let swapped := swapRows state.system candidate pivot
  let condition := row ≠ pivot ∧
    swapped.check row active = (1 : ZMod 2)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hswapped := gaussianPhysicalColumnSwappedCheckWord_effective
    state source row column active column candidate pivot
    found boundary gaussianPhysicalColumnCellColumn hcolumn
  have hgate := gaussianPhysicalColumnClearGateWord_effective
    state source row column active candidate pivot found boundary
  have hcandidate := gaussianPhysicalColumnDynamicCheckWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hterm := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnClearGateWord
    gaussianPhysicalColumnCandidateCheckWord input
    (decide condition)
    (decide (state.system.check candidate column = (1 : ZMod 2)))
    hgate hcandidate
  have hxor := sourceExplicitAffineXorBits_valid
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord)
    input
    (decide (swapped.check row column = (1 : ZMod 2)))
    (decide condition &&
      decide (state.system.check candidate column = (1 : ZMod 2)))
    hswapped hterm
  change sourceExplicitAffineXorBits
    (gaussianPhysicalColumnSwappedCheckWord
      gaussianPhysicalColumnCellColumn)
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateCheckWord) input = _
  rw [hxor]
  rw [clearTargets_check_finRange]
  change
    [Bool.xor
      (decide (swapped.check row column = (1 : ZMod 2)))
      (decide condition &&
        decide (state.system.check candidate column = (1 : ZMod 2)))] =
      [decide
        ((if condition then
          swapped.check row column + swapped.check pivot column
        else
          swapped.check row column) = (1 : ZMod 2))]
  by_cases hcondition : condition
  · simp only [hcondition, decide_true, Bool.true_and, ite_true]
    rw [gaussianPhysicalColumnBinaryAdd_decide]
    have hpivotEntry : swapped.check pivot column =
        state.system.check candidate column := by
      change state.system.check
        (Equiv.swap candidate pivot pivot) column =
          state.system.check candidate column
      rw [Equiv.swap_apply_right]
    rw [hpivotEntry]
  · simp only [hcondition, decide_false, Bool.false_and, Bool.bne_false, ↓reduceIte]


-- @@ L646-726 verbatim
private theorem gaussianPhysicalColumnPivotUpdatedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n)
    (candidate pivot : Fin m)
    (found : findPivotOption state active = some candidate)
    (boundary : state.nextPivot = pivot.val) :
    gaussianPhysicalColumnPivotUpdatedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide
        ((clearTargets pivot active (List.finRange m)
          (applyOperation state (.swap candidate pivot))).system.rhs
            row = (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  let swapped := swapRows state.system candidate pivot
  let condition := row ≠ pivot ∧
    swapped.check row active = (1 : ZMod 2)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hswapped := gaussianPhysicalColumnSwappedRhsWord_effective
    state source row column active candidate pivot found boundary
  have hgate := gaussianPhysicalColumnClearGateWord_effective
    state source row column active candidate pivot found boundary
  have hcandidate := gaussianPhysicalColumnDynamicRhsWord_effective
    state source input gaussianPhysicalColumnCandidateUnary
    gaussianPhysicalColumnCellColumn candidate column hstate
    (gaussianPhysicalColumnCandidateUnary_effective
      state source row column active candidate found)
    hcolumn
  have hterm := fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnClearGateWord
    gaussianPhysicalColumnCandidateRhsWord input
    (decide condition)
    (decide (state.system.rhs candidate = (1 : ZMod 2)))
    hgate hcandidate
  have hxor := sourceExplicitAffineXorBits_valid
    gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord)
    input
    (decide (swapped.rhs row = (1 : ZMod 2)))
    (decide condition &&
      decide (state.system.rhs candidate = (1 : ZMod 2)))
    hswapped hterm
  change sourceExplicitAffineXorBits
    gaussianPhysicalColumnSwappedRhsWord
    (sourceFourFamilyBooleanAndOutput
      gaussianPhysicalColumnClearGateWord
      gaussianPhysicalColumnCandidateRhsWord) input = _
  rw [hxor]
  rw [clearTargets_rhs_finRange]
  change
    [Bool.xor
      (decide (swapped.rhs row = (1 : ZMod 2)))
      (decide condition &&
        decide (state.system.rhs candidate = (1 : ZMod 2)))] =
      [decide
        ((if condition then
          swapped.rhs row + swapped.rhs pivot
        else
          swapped.rhs row) = (1 : ZMod 2))]
  by_cases hcondition : condition
  · simp only [hcondition, decide_true, Bool.true_and, ite_true]
    rw [gaussianPhysicalColumnBinaryAdd_decide]
    have hpivotEntry : swapped.rhs pivot =
        state.system.rhs candidate := by
      change state.system.rhs
        (Equiv.swap candidate pivot pivot) =
          state.system.rhs candidate
      rw [Equiv.swap_apply_right]
    rw [hpivotEntry]
  · simp only [hcondition, decide_false, Bool.false_and, Bool.bne_false, ↓reduceIte]


-- @@ L728-780 verbatim
theorem gaussianPhysicalColumnUpdatedCheckWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnUpdatedCheckWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide ((columnStep state active).system.check row column =
        (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnCellRow_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  cases found : findPivotOption state active with
  | none =>
      have hpresent : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [found, Option.isSome_none] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      have horiginal := gaussianPhysicalColumnDynamicCheckWord_effective
        state source input gaussianPhysicalColumnCellRow
        gaussianPhysicalColumnCellColumn row column hstate hrow hcolumn
      have hstep : columnStep state active = state := by
        simp only [columnStep, found, dite_eq_ite, ite_self]
      unfold gaussianPhysicalColumnUpdatedCheckWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      change gaussianPhysicalColumnOriginalCheckWord input = _
      rw [hstep]
      exact horiginal
  | some candidate =>
      have habove := (findPivotOption_some state active candidate found).1
      have hactive : state.nextPivot < m := habove.trans_lt candidate.isLt
      let pivot : Fin m := ⟨state.nextPivot, hactive⟩
      have hpresent : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [found, Option.isSome_some] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      unfold gaussianPhysicalColumnUpdatedCheckWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      simp only [↓reduceIte]
      have hupdated := gaussianPhysicalColumnPivotUpdatedCheckWord_effective
        state source row column active candidate pivot found rfl
      simp only [columnStep, hactive, ↓reduceDIte, found]
      exact hupdated


-- @@ L782-834 verbatim
theorem gaussianPhysicalColumnUpdatedRhsWord_effective
    {m n : ℕ} (state : State m n) (source : List Bool)
    (row : Fin m) (column active : Fin n) :
    gaussianPhysicalColumnUpdatedRhsWord
        (gaussianPhysicalColumnCellQuery row.val column.val active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide ((columnStep state active).system.rhs row =
        (1 : ZMod 2))] := by
  let input := gaussianPhysicalColumnCellQuery
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hstate : gaussianPhysicalColumnCellPackedState input =
      effectiveGaussianPackedStateWord state source :=
    gaussianPhysicalColumnCellPackedState_query
      row.val column.val active.val
        (effectiveGaussianPackedStateWord state source)
  have hrow := gaussianPhysicalColumnCellRow_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  have hcolumn := gaussianPhysicalColumnCellColumn_query
    row.val column.val active.val
      (effectiveGaussianPackedStateWord state source)
  cases found : findPivotOption state active with
  | none =>
      have hpresent : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [found, Option.isSome_none] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      have horiginal := gaussianPhysicalColumnDynamicRhsWord_effective
        state source input gaussianPhysicalColumnCellRow
        gaussianPhysicalColumnCellColumn row column hstate hrow hcolumn
      have hstep : columnStep state active = state := by
        simp only [columnStep, found, dite_eq_ite, ite_self]
      unfold gaussianPhysicalColumnUpdatedRhsWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      change gaussianPhysicalColumnOriginalRhsWord input = _
      rw [hstep]
      exact horiginal
  | some candidate =>
      have habove := (findPivotOption_some state active candidate found).1
      have hactive : state.nextPivot < m := habove.trans_lt candidate.isLt
      let pivot : Fin m := ⟨state.nextPivot, hactive⟩
      have hpresent : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [found, Option.isSome_some] using
            gaussianPhysicalColumnPivotPresent_effective state source row column active
      unfold gaussianPhysicalColumnUpdatedRhsWord
        binaryGaussianDynamicBranchOutput
      rw [hpresent]
      simp only [↓reduceIte]
      have hupdated := gaussianPhysicalColumnPivotUpdatedRhsWord_effective
        state source row column active candidate pivot found rfl
      simp only [columnStep, hactive, ↓reduceDIte, found]
      exact hupdated


-- @@ L836-836 verbatim
end GaussianAdaptivePhysicalColumnCellUpdateTM


-- @@ L838-838 verbatim
namespace GaussianAdaptivePhysicalColumnStateTM


-- @@ L840-840 verbatim
open Turing GapCVP.Core GapCVP.Core.EffectiveBinaryGaussian GapCVP.BinaryEncoding

-- @@ L841-841 verbatim
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceCanonicalFixedWordTuringTM

-- @@ L842-842 verbatim
open GapCVP.SourceOriginalSourcePreservingTM GapCVP.CLStructuralPrefixWriter

-- @@ L843-843 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.SourceFourFamilyBooleanPredicateTM

-- @@ L844-844 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

-- @@ L845-845 verbatim
open GapCVP.SourceFourFamilyDiagonalMembershipPredicateTM

-- @@ L846-846 verbatim
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

-- @@ L847-847 verbatim
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM GapCVP.BinaryExplicitAffineRows

-- @@ L848-848 verbatim
open GapCVP.Factor400BinaryPhysicalWorkers GapCVP.GaussianRowWorker

-- @@ L849-849 verbatim
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptiveEliminationCorrectness

-- @@ L850-850 verbatim
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianAdaptivePhysicalStateCellTM

-- @@ L851-851 verbatim
open GapCVP.GaussianAdaptivePackedStateLookupTM

-- @@ L852-852 verbatim
open GapCVP.GaussianAdaptivePhysicalCandidateCatalogueTM


-- @@ L854-856 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnActiveUnary : List Bool → List Bool :=
  firstFieldContents


-- @@ L858-862 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnActiveUnaryComputable :
    BitTM
      gaussianPhysicalColumnActiveUnary :=
  firstFieldContentsComputable


-- @@ L864-866 verbatim
/-- GapCVP reduction support. -/
@[expose] def gaussianPhysicalColumnCurrentState : List Bool → List Bool :=
  firstFieldSuffix


-- @@ L868-872 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnCurrentStateComputable :
    BitTM
      gaussianPhysicalColumnCurrentState :=
  firstFieldSuffixComputable


-- @@ L874-876 verbatim
private def gaussianPhysicalColumnOldNextUnary : List Bool → List Bool :=
  firstFieldContents ∘ firstFieldSuffix ∘ firstFieldSuffix ∘
    gaussianPhysicalColumnCurrentState


-- @@ L878-887 verbatim
private noncomputable def gaussianPhysicalColumnOldNextUnaryComputable :
    BitTM
      gaussianPhysicalColumnOldNextUnary := by
  have hcheck := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    firstFieldSuffixComputable
  have hrhs := GapCVP.TMComposition.computableInPolyTime
    hcheck firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hrhs firstFieldContentsComputable


-- @@ L889-892 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotPresent
    (input : List Bool) : Bool :=
  (gaussianPhysicalPivotDecisionOutput input).headD false


-- @@ L894-925 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotPresentComputable :
    BitTM
      (fun input => gaussianPhysicalColumnPivotPresent input :: input) := by
  have hbit := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotDecisionComputable
    binaryGaussianFirstCellComputable
  have hpreserved := originalSourcePreservingComputable hbit
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved factor400KeepFirstDropSecondComputable
  convert hphysical using 1
  funext input
  change gaussianPhysicalColumnPivotPresent input :: input =
    factor400KeepFirstDropSecondWord
      (originalSourcePreservingOutput
        (binaryGaussianFirstCellWord ∘
          gaussianPhysicalPivotDecisionOutput) input)
  cases hpivot : gaussianPhysicalPivotDecisionOutput input with
  | nil =>
      simp only [gaussianPhysicalColumnPivotPresent, hpivot, List.headD_eq_head?_getD,
          List.head?_nil,
          Option.getD_none, factor400KeepFirstDropSecondWord, originalSourcePreservingOutput,
              binaryGaussianFirstCellWord,
          Function.comp_apply, OutputPolynomialCompositionClosure.markerConditionalOutput,
              List.cons_append, List.nil_append,
          List.tail_cons]
  | cons first remaining =>
      simp only [gaussianPhysicalColumnPivotPresent, hpivot, List.headD_eq_head?_getD,
          List.head?_cons,
          Option.getD_some, factor400KeepFirstDropSecondWord, originalSourcePreservingOutput,
              Function.comp_apply,
          binaryGaussianFirstCellWord_valid, List.cons_append, List.nil_append, List.tail_cons]


-- @@ L927-930 verbatim
private def gaussianPhysicalColumnNextSuccessor : List Bool → List Bool :=
  fourFamilyComputedUnarySumOutput
    gaussianPhysicalColumnOldNextUnary
    (fun _ : List Bool => [true])


-- @@ L932-937 verbatim
private noncomputable def gaussianPhysicalColumnNextSuccessorComputable :
    BitTM
      gaussianPhysicalColumnNextSuccessor :=
  fourFamilyComputedUnarySumComputable
    gaussianPhysicalColumnOldNextUnaryComputable
    (sourceFixedWordComputable [true])


-- @@ L939-944 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnNextPivotUnary : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotPresent
    gaussianPhysicalColumnNextSuccessor
    gaussianPhysicalColumnOldNextUnary


-- @@ L946-953 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnNextPivotUnaryComputable :
    BitTM
      gaussianPhysicalColumnNextPivotUnary :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotPresentComputable
    gaussianPhysicalColumnNextSuccessorComputable
    gaussianPhysicalColumnOldNextUnaryComputable


-- @@ L955-961 verbatim
@[simp] theorem gaussianPhysicalColumnActiveUnary_query
    (column : ℕ) (state : List Bool) :
    gaussianPhysicalColumnActiveUnary
        (gaussianPhysicalPivotColumnQuery column state) =
      List.replicate column true := by
  simp only [gaussianPhysicalColumnActiveUnary, gaussianPhysicalPivotColumnQuery,
      firstFieldContents_valid]


-- @@ L963-968 verbatim
@[simp] theorem gaussianPhysicalColumnCurrentState_query
    (column : ℕ) (state : List Bool) :
    gaussianPhysicalColumnCurrentState
        (gaussianPhysicalPivotColumnQuery column state) = state := by
  simp only [gaussianPhysicalColumnCurrentState, gaussianPhysicalPivotColumnQuery,
      firstFieldSuffix_valid]


-- @@ L970-980 verbatim
@[simp] private theorem gaussianPhysicalColumnOldNextUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPhysicalColumnOldNextUnary
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate state.nextPivot true := by
  simp only [gaussianPhysicalColumnOldNextUnary, gaussianPhysicalColumnCurrentState,
      gaussianPhysicalPivotColumnQuery, effectiveGaussianPackedStateWord, List.append_assoc,
          Function.comp_apply,
      firstFieldSuffix_valid, firstFieldContents_valid]


-- @@ L982-993 verbatim
theorem gaussianPhysicalColumnPivotPresent_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnPivotPresent
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      (findPivotOption state column).isSome := by
  unfold gaussianPhysicalColumnPivotPresent
  rw [gaussianPhysicalPivotDecisionOutput_effective
    state source column hrows]
  cases findPivotOption state column <;> rfl


-- @@ L995-1010 verbatim
private theorem gaussianPhysicalColumnNextSuccessor_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n) :
    gaussianPhysicalColumnNextSuccessor
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (state.nextPivot + 1) true := by
  apply fourFamilyComputedUnarySumOutput_valid
    gaussianPhysicalColumnOldNextUnary
    (fun _ : List Bool => [true])
    (gaussianPhysicalPivotColumnQuery column.val
      (effectiveGaussianPackedStateWord state source))
    state.nextPivot 1
  · exact gaussianPhysicalColumnOldNextUnary_effective
      state source column
  · rfl


-- @@ L1012-1018 verbatim
private theorem gaussianPhysicalColumn_foundPivot_next_lt
    {m n : ℕ} (state : State m n)
    (column : Fin n) (row : Fin m)
    (hfound : findPivotOption state column = some row) :
    state.nextPivot < m := by
  have hle := (findPivotOption_some state column row hfound).1
  exact lt_of_le_of_lt hle row.isLt


-- @@ L1020-1051 verbatim
theorem gaussianPhysicalColumnNextPivotUnary_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnNextPivotUnary
        (gaussianPhysicalPivotColumnQuery column.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate (columnStep state column).nextPivot true := by
  let input := gaussianPhysicalPivotColumnQuery column.val
    (effectiveGaussianPackedStateWord state source)
  have hmarker := gaussianPhysicalColumnPivotPresent_effective
    state source column hrows
  change gaussianPhysicalColumnNextPivotUnary input = _
  unfold gaussianPhysicalColumnNextPivotUnary
    binaryGaussianDynamicBranchOutput
  cases hfound : findPivotOption state column with
  | none =>
      have hfalse : gaussianPhysicalColumnPivotPresent input = false := by
        simpa only [hfound, Option.isSome_none] using hmarker
      rw [hfalse, ite_eq_right Bool.false_ne_true]
      rw [gaussianPhysicalColumnOldNextUnary_effective]
      by_cases hactive : state.nextPivot < m <;>
        simp [columnStep, hactive, hfound]
  | some row =>
      have htrue : gaussianPhysicalColumnPivotPresent input = true := by
        simpa only [hfound, Option.isSome_some] using hmarker
      have hactive : state.nextPivot < m :=
        gaussianPhysicalColumn_foundPivot_next_lt
          state column row hfound
      rw [htrue, ite_eq_left rfl]
      rw [gaussianPhysicalColumnNextSuccessor_effective]
      simp only [columnStep, hactive, ↓reduceDIte, hfound, clearTargets_pivots]


-- @@ L1053-1084 verbatim
private theorem effectiveGaussianColumnStepPivotWord
    {m n : ℕ} (state : State m n)
    (active column : Fin n) :
    effectiveGaussianStatePivotWord
        (columnStep state active) column =
      if (findPivotOption state active).isSome &&
          decide (active = column) then
        true :: List.replicate state.nextPivot true
      else
        effectiveGaussianStatePivotWord state column := by
  cases hfound : findPivotOption state active with
  | none =>
      by_cases hactive : state.nextPivot < m <;>
        simp [columnStep, hactive, hfound]
  | some row =>
      have hactive : state.nextPivot < m :=
        gaussianPhysicalColumn_foundPivot_next_lt
          state active row hfound
      by_cases heq : active = column
      · subst column
        simp only [effectiveGaussianStatePivotWord,
            effectiveGaussianStatePivotRowOption, columnStep,
            hactive, ↓reduceDIte,
            hfound, applyOperation, clearTargets_pivots, decide_true, List.find?_cons_of_pos,
                Option.map_some,
            Option.isSome_some, Bool.and_self, ↓reduceIte]
      · simp only [effectiveGaussianStatePivotWord,
          effectiveGaussianStatePivotRowOption, columnStep,
          hactive, ↓reduceDIte,
            hfound, applyOperation, clearTargets_pivots, heq, decide_false, Bool.false_eq_true,
                not_false_eq_true,
            List.find?_cons_of_neg, Option.isSome_some, Bool.and_false, ↓reduceIte]


-- @@ L1086-1089 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnPivotRecordOuter :
    List Bool → List Bool :=
  firstFieldSuffix ∘ firstFieldSuffix


-- @@ L1091-1096 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotRecordOuterComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordOuter :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldSuffixComputable


-- @@ L1098-1105 verbatim
@[simp] theorem gaussianPhysicalColumnPivotRecordOuter_word
    (rank width active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnPivotRecordOuter
        (gaussianPhysicalPivotRecordWord rank width active state) =
      gaussianPhysicalPivotColumnQuery active state := by
  simp only [gaussianPhysicalColumnPivotRecordOuter, gaussianPhysicalPivotRecordWord,
      List.append_assoc,
      Function.comp_apply, firstFieldSuffix_valid]


-- @@ L1107-1111 verbatim
private def gaussianPhysicalColumnOldPivotQuery
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
    (lengthPrefixedWord [] ++
      gaussianPhysicalPivotRecordState input)


-- @@ L1113-1129 verbatim
private noncomputable def gaussianPhysicalColumnOldPivotQueryComputable :
    BitTM
      gaussianPhysicalColumnOldPivotQuery := by
  have hrank := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalPivotRecordRowComputable
    structuralPrefixWriterComputable
  have hzero := sourceFixedWordComputable
    (lengthPrefixedWord ([] : List Bool))
  have hphysical := pointwiseAppendComputable hrank
    (pointwiseAppendComputable hzero
      gaussianPhysicalPivotRecordStateComputable)
  change BitTM
    (fun input =>
      lengthPrefixedWord (gaussianPhysicalPivotRecordRow input) ++
        (lengthPrefixedWord [] ++
          gaussianPhysicalPivotRecordState input))
  simpa only [Function.comp_apply] using hphysical


-- @@ L1131-1138 verbatim
@[simp] private theorem gaussianPhysicalColumnOldPivotQuery_word
    (rank width active : ℕ) (state : List Bool) :
    gaussianPhysicalColumnOldPivotQuery
        (gaussianPhysicalPivotRecordWord rank width active state) =
      affineCellQuery rank 0 state := by
  simp only [gaussianPhysicalColumnOldPivotQuery, gaussianPhysicalPivotRecordRow_word,
      gaussianPhysicalPivotRecordState_word, affineCellQuery, List.replicate_zero,
          List.append_assoc]


-- @@ L1140-1142 verbatim
private def gaussianPhysicalColumnOldPivotWord : List Bool → List Bool :=
  gaussianPackedStatePivotCellWord ∘
    gaussianPhysicalColumnOldPivotQuery


-- @@ L1144-1149 verbatim
private noncomputable def gaussianPhysicalColumnOldPivotComputable :
    BitTM
      gaussianPhysicalColumnOldPivotWord :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnOldPivotQueryComputable
    gaussianPackedStatePivotCellComputable


-- @@ L1151-1163 verbatim
private theorem gaussianPhysicalColumnOldPivotWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) :
    gaussianPhysicalColumnOldPivotWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord state column := by
  unfold gaussianPhysicalColumnOldPivotWord
  rw [Function.comp_apply,
    gaussianPhysicalColumnOldPivotQuery_word]
  exact gaussianPackedStatePivotCellWord_query
    state source column


-- @@ L1165-1169 verbatim
private def gaussianPhysicalColumnPivotRecordActiveEq :
    List Bool → List Bool :=
  fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn


-- @@ L1171-1176 verbatim
private noncomputable def gaussianPhysicalColumnPivotRecordActiveEqComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordActiveEq :=
  fourFamilyComputedUnaryEqBitComputable
    gaussianPhysicalPivotRecordRowComputable
    gaussianPhysicalPivotRecordColumnComputable


-- @@ L1178-1182 verbatim
private def gaussianPhysicalColumnPivotRecordPresentWord :
    List Bool → List Bool :=
  binaryGaussianFirstCellWord ∘
    gaussianPhysicalPivotDecisionOutput ∘
    gaussianPhysicalColumnPivotRecordOuter


-- @@ L1184-1191 verbatim
private noncomputable def gaussianPhysicalColumnPivotRecordPresentComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordPresentWord := by
  have hdecision := GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnPivotRecordOuterComputable
    gaussianPhysicalPivotDecisionComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hdecision binaryGaussianFirstCellComputable


-- @@ L1193-1197 verbatim
private def gaussianPhysicalColumnPivotRecordUpdateMarker :
    List Bool → List Bool :=
  sourceFourFamilyBooleanAndOutput
    gaussianPhysicalColumnPivotRecordPresentWord
    gaussianPhysicalColumnPivotRecordActiveEq


-- @@ L1199-1204 verbatim
private noncomputable def gaussianPhysicalColumnPivotRecordUpdateMarkerComputable :
    BitTM
      gaussianPhysicalColumnPivotRecordUpdateMarker :=
  fourFamilyBooleanAndComputable
    gaussianPhysicalColumnPivotRecordPresentComputable
    gaussianPhysicalColumnPivotRecordActiveEqComputable


-- @@ L1206-1208 verbatim
private def gaussianPhysicalColumnNewPivotWord
    (input : List Bool) : List Bool :=
  [true] ++ gaussianPhysicalPivotRecordNextUnary input


-- @@ L1210-1215 verbatim
private noncomputable def gaussianPhysicalColumnNewPivotComputable :
    BitTM
      gaussianPhysicalColumnNewPivotWord :=
  pointwiseAppendComputable
    (sourceFixedWordComputable [true])
    gaussianPhysicalPivotRecordNextUnaryComputable


-- @@ L1217-1247 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalComputedMarkerPreservingComputable
    {marker : List Bool → List Bool}
    (computer : BitTM marker) :
    BitTM
      (fun input => (marker input).headD false :: input) := by
  have hbit := GapCVP.TMComposition.computableInPolyTime
    computer binaryGaussianFirstCellComputable
  have hpreserved := originalSourcePreservingComputable hbit
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hpreserved factor400KeepFirstDropSecondComputable
  convert hphysical using 1
  funext input
  change (marker input).headD false :: input =
    factor400KeepFirstDropSecondWord
      (originalSourcePreservingOutput
        (binaryGaussianFirstCellWord ∘ marker) input)
  cases hmarker : marker input with
  | nil =>
      simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none,
          factor400KeepFirstDropSecondWord,
          originalSourcePreservingOutput, binaryGaussianFirstCellWord, Function.comp_apply,
          OutputPolynomialCompositionClosure.markerConditionalOutput, hmarker, List.cons_append,
              List.nil_append,
          List.tail_cons]
  | cons bit remaining =>
      simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
          factor400KeepFirstDropSecondWord,
          originalSourcePreservingOutput, Function.comp_apply, hmarker,
              binaryGaussianFirstCellWord_valid, List.cons_append,
          List.nil_append, List.tail_cons]


-- @@ L1249-1251 verbatim
private def gaussianPhysicalColumnPivotRecordShouldUpdate
    (input : List Bool) : Bool :=
  (gaussianPhysicalColumnPivotRecordUpdateMarker input).headD false


-- @@ L1253-1258 verbatim
private noncomputable def gaussianPhysicalColumnPivotRecordShouldUpdateComputable :
    BitTM
      (fun input =>
        gaussianPhysicalColumnPivotRecordShouldUpdate input :: input) :=
  gaussianPhysicalComputedMarkerPreservingComputable
    gaussianPhysicalColumnPivotRecordUpdateMarkerComputable


-- @@ L1260-1265 verbatim
private def gaussianPhysicalColumnUpdatedPivotWord :
    List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotRecordShouldUpdate
    gaussianPhysicalColumnNewPivotWord
    gaussianPhysicalColumnOldPivotWord


-- @@ L1267-1273 verbatim
private noncomputable def gaussianPhysicalColumnUpdatedPivotComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotWord :=
  binaryGaussianDynamicBranchComputable
    gaussianPhysicalColumnPivotRecordShouldUpdateComputable
    gaussianPhysicalColumnNewPivotComputable
    gaussianPhysicalColumnOldPivotComputable


-- @@ L1275-1307 verbatim
private theorem gaussianPhysicalColumnPivotRecordActiveEq_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) :
    gaussianPhysicalColumnPivotRecordActiveEq
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [decide (column = active)] := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have heq := fourFamilyComputedUnaryEqBitOutput_valid
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn input
    column.val active.val
    (gaussianPhysicalPivotRecordRow_word
      column.val width active.val
      (effectiveGaussianPackedStateWord state source))
    (gaussianPhysicalPivotRecordColumn_word
      column.val width active.val
      (effectiveGaussianPackedStateWord state source))
  change gaussianPhysicalColumnPivotRecordActiveEq input = _
  change fourFamilyComputedUnaryEqBitOutput
    gaussianPhysicalPivotRecordRow
    gaussianPhysicalPivotRecordColumn input = _
  rw [heq]
  by_cases h : column = active
  · subst active
    simp only [decide_true]
  · have hv : column.val ≠ active.val := by
      intro hv
      exact h (Fin.ext hv)
    simp only [hv, decide_false, h]


-- @@ L1309-1324 verbatim
private theorem gaussianPhysicalColumnPivotRecordPresentWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnPivotRecordPresentWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [(findPivotOption state active).isSome] := by
  unfold gaussianPhysicalColumnPivotRecordPresentWord
  simp only [Function.comp_apply,
    gaussianPhysicalColumnPivotRecordOuter_word]
  rw [gaussianPhysicalPivotDecisionOutput_effective
    state source active hrows]
  cases findPivotOption state active <;>
    simp [binaryGaussianFirstCellWord,
      GapCVP.OutputPolynomialCompositionClosure.markerConditionalOutput]


-- @@ L1326-1346 verbatim
private theorem gaussianPhysicalColumnPivotRecordUpdateMarker_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnPivotRecordUpdateMarker
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      [(findPivotOption state active).isSome &&
        decide (column = active)] := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have hpresent := gaussianPhysicalColumnPivotRecordPresentWord_effective
    state source column active width hrows
  have hequal := gaussianPhysicalColumnPivotRecordActiveEq_effective
    state source column active width
  exact fourFamilyBooleanAndOutput_bits
    gaussianPhysicalColumnPivotRecordPresentWord
    gaussianPhysicalColumnPivotRecordActiveEq input
    (findPivotOption state active).isSome
    (decide (column = active)) hpresent hequal


-- @@ L1348-1395 verbatim
private theorem gaussianPhysicalColumnUpdatedPivotWord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotWord
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianStatePivotWord
        (columnStep state active) column := by
  let input := gaussianPhysicalPivotRecordWord
    column.val width active.val
    (effectiveGaussianPackedStateWord state source)
  have hmarker := gaussianPhysicalColumnPivotRecordUpdateMarker_effective
    state source column active width hrows
  have hnext := gaussianPhysicalPivotRecordNextUnary_word
    state source column.val width active.val
  have hold := gaussianPhysicalColumnOldPivotWord_effective
    state source column active width
  have hsemantic := effectiveGaussianColumnStepPivotWord
    state active column
  change gaussianPhysicalColumnUpdatedPivotWord input = _
  unfold gaussianPhysicalColumnUpdatedPivotWord
    binaryGaussianDynamicBranchOutput
    gaussianPhysicalColumnPivotRecordShouldUpdate
  rw [hmarker]
  cases hfound : findPivotOption state active with
  | none =>
      simp only [Option.isSome_none, Bool.false_and,
        List.headD_cons, Bool.false_eq_true, ↓reduceIte]
      rw [hold, hsemantic, hfound]
      simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | some row =>
      by_cases heq : column = active
      · subst column
        simp only [Option.isSome_some, decide_true,
          Bool.and_self, List.headD_cons, ↓reduceIte]
        change [true] ++
          gaussianPhysicalPivotRecordNextUnary input = _
        rw [hnext, hsemantic, hfound]
        simp only [List.cons_append, List.nil_append, Option.isSome_some, decide_true,
            Bool.and_self, ↓reduceIte]
      · have hreverse : active ≠ column := Ne.symm heq
        simp only [Option.isSome_some, heq, decide_false,
          Bool.and_false, List.headD_cons,
          Bool.false_eq_true, ↓reduceIte]
        rw [hold, hsemantic, hfound]
        simp only [Option.isSome_some, hreverse, decide_false, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte]


-- @@ L1397-1400 verbatim
/-- GapCVP reduction support. -/
@[expose] def gaussianPhysicalColumnPivotWidthOutput : List Bool → List Bool :=
  gaussianDenseStateDimensionUnary ∘
    gaussianPhysicalColumnCurrentState


-- @@ L1402-1408 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnPivotWidthComputable :
    BitTM
      gaussianPhysicalColumnPivotWidthOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnCurrentStateComputable
    gaussianDenseStateDimensionUnaryComputable


-- @@ L1410-1414 verbatim
/-- Width certificate for the physical Gaussian pivot-column catalogue. -/
noncomputable def gaussianPhysicalColumnPivotWidth :
    SourceQaryMaskDynamicGridWidth where
  output := gaussianPhysicalColumnPivotWidthOutput
  computer := gaussianPhysicalColumnPivotWidthComputable


-- @@ L1416-1421 verbatim
/-- The pivot-width machine computes its declared output function. -/
theorem gaussianPhysicalColumnPivotWidth_output
    (input : List Bool) :
    gaussianPhysicalColumnPivotWidth.output input =
      gaussianPhysicalColumnPivotWidthOutput input := by
  rfl


-- @@ L1423-1426 verbatim
private def gaussianPhysicalColumnUpdatedPivotRecordOutput :
    List Bool → List Bool :=
  (fun word => lengthPrefixedWord word) ∘
    gaussianPhysicalColumnUpdatedPivotWord


-- @@ L1428-1433 verbatim
private noncomputable def gaussianPhysicalColumnUpdatedPivotRecordComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotRecordOutput :=
  GapCVP.TMComposition.computableInPolyTime
    gaussianPhysicalColumnUpdatedPivotComputable
    structuralPrefixWriterComputable


-- @@ L1435-1440 verbatim
/-- GapCVP reduction support. -/
def gaussianPhysicalColumnUpdatedPivotCatalogueOutput :
    List Bool → List Bool :=
  maskDynamicGridRecordCatalogueOutput
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable


-- @@ L1442-1448 verbatim
/-- GapCVP reduction support. -/
noncomputable def gaussianPhysicalColumnUpdatedPivotCatalogueComputable :
    BitTM
      gaussianPhysicalColumnUpdatedPivotCatalogueOutput :=
  maskDynamicGridRecordCatalogueComputable
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable


-- @@ L1450-1464 verbatim
theorem gaussianPhysicalColumnPivotWidth_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnPivotWidth.output
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      List.replicate n true := by
  change gaussianDenseStateDimensionUnary
    (gaussianPhysicalColumnCurrentState
      (gaussianPhysicalPivotColumnQuery active.val
        (effectiveGaussianPackedStateWord state source))) = _
  rw [gaussianPhysicalColumnCurrentState_query]
  exact gaussianDenseStateDimensionUnary_effective
    state source hrows


-- @@ L1466-1479 verbatim
private theorem gaussianPhysicalColumnUpdatedPivotCatalogueOutput_valid
    (input : List Bool) (count : ℕ)
    (hwidth : gaussianPhysicalColumnPivotWidth.output input =
      List.replicate count true) :
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput input =
      (List.range count).flatMap (fun rank =>
        gaussianPhysicalColumnUpdatedPivotRecordOutput
          (lengthPrefixedWord (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource
              gaussianPhysicalColumnPivotWidth input)) := by
  exact maskDynamicGridRecordCatalogueOutput_valid
    gaussianPhysicalColumnPivotWidth
    gaussianPhysicalColumnUpdatedPivotRecordComputable
    input count hwidth


-- @@ L1481-1496 verbatim
private theorem gaussianPhysicalColumnPivotGeneratedRecord_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (rank : ℕ) (hrows : 0 < m) :
    lengthPrefixedWord (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource
          gaussianPhysicalColumnPivotWidth
          (gaussianPhysicalPivotColumnQuery active.val
            (effectiveGaussianPackedStateWord state source)) =
      gaussianPhysicalPivotRecordWord rank n active.val
        (effectiveGaussianPackedStateWord state source) := by
  unfold sourceQaryMaskDynamicGridBaseSource
  rw [gaussianPhysicalColumnPivotWidth_effective
    state source active hrows]
  simp only [gaussianPhysicalPivotRecordWord,
    List.append_assoc]


-- @@ L1498-1511 verbatim
private theorem gaussianPhysicalColumnUpdatedPivotRecordOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (column active : Fin n)
    (width : ℕ) (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotRecordOutput
        (gaussianPhysicalPivotRecordWord column.val width active.val
          (effectiveGaussianPackedStateWord state source)) =
      lengthPrefixedWord
        (effectiveGaussianStatePivotWord
          (columnStep state active) column) := by
  unfold gaussianPhysicalColumnUpdatedPivotRecordOutput
  rw [Function.comp_apply,
    gaussianPhysicalColumnUpdatedPivotWord_effective
      state source column active width hrows]


-- @@ L1513-1566 verbatim
theorem gaussianPhysicalColumnUpdatedPivotCatalogueOutput_effective
    {m n : ℕ} (state : State m n)
    (source : List Bool) (active : Fin n)
    (hrows : 0 < m) :
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput
        (gaussianPhysicalPivotColumnQuery active.val
          (effectiveGaussianPackedStateWord state source)) =
      effectiveGaussianPackedPivotCatalogue
        (columnStep state active) := by
  let input := gaussianPhysicalPivotColumnQuery active.val
    (effectiveGaussianPackedStateWord state source)
  have hwidth : gaussianPhysicalColumnPivotWidth.output input =
      List.replicate n true :=
    gaussianPhysicalColumnPivotWidth_effective
      state source active hrows
  have hcatalogue :=
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput_valid
      input n hwidth
  calc
    gaussianPhysicalColumnUpdatedPivotCatalogueOutput input =
        (List.range n).flatMap (fun rank =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (lengthPrefixedWord (List.replicate rank true) ++
              sourceQaryMaskDynamicGridBaseSource
                gaussianPhysicalColumnPivotWidth input)) :=
      hcatalogue
    _ = (List.range n).flatMap (fun rank =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (gaussianPhysicalPivotRecordWord rank n active.val
              (effectiveGaussianPackedStateWord state source))) := by
      apply List.flatMap_congr
      intro rank _
      exact congrArg gaussianPhysicalColumnUpdatedPivotRecordOutput
        (gaussianPhysicalColumnPivotGeneratedRecord_effective
          state source active rank hrows)
    _ = (List.finRange n).flatMap (fun column =>
          gaussianPhysicalColumnUpdatedPivotRecordOutput
            (gaussianPhysicalPivotRecordWord column.val n active.val
              (effectiveGaussianPackedStateWord state source))) :=
      gaussianPhysicalPivot_range_flatMap_finRange n _
    _ = (List.finRange n).flatMap (fun column =>
          lengthPrefixedWord
            (effectiveGaussianStatePivotWord
              (columnStep state active) column)) := by
      apply List.flatMap_congr
      intro column _
      exact gaussianPhysicalColumnUpdatedPivotRecordOutput_effective
        state source column active n hrows
    _ = effectiveGaussianPackedPivotCatalogue
          (columnStep state active) := by
      unfold effectiveGaussianPackedPivotCatalogue
        binaryGaussianPivotBatchStream
        sourceMixedRadixOriginalSourceQueryStream
      rw [List.flatMap_map]


-- @@ L1568-1568 verbatim
end GaussianAdaptivePhysicalColumnStateTM



-- @@ L1571-1571 verbatim
end GapCVP


-- @@ L1573-1573 verbatim
end
