/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part07E


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 07, continuation 06 -/


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
namespace CNFFiveFamilyForbiddenWholeClauseExactSourceTM


-- @@ L27-27 verbatim
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM


-- @@ L29-29 verbatim
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceGridDescriptorTM


-- @@ L31-31 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM


-- @@ L33-33 verbatim
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM


-- @@ L35-35 verbatim
open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM


-- @@ L37-37 verbatim
open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM


-- @@ L39-39 verbatim
open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert


-- @@ L41-41 verbatim
end CNFFiveFamilyForbiddenWholeClauseExactSourceTM


-- @@ L43-43 verbatim
namespace CNFFiveFamilyIndependentAnchoredFamilyStreamTM


-- @@ L45-45 verbatim
open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert

-- @@ L46-46 verbatim
open GapCVP.SourceUniformTuringTM GapCVP.SourceFormulaStructuralDecoder

-- @@ L47-47 verbatim
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalUnaryGridIndexTM

-- @@ L48-48 verbatim
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CLStructuralPrefixWriter

-- @@ L49-49 verbatim
open GapCVP.CNFBoundedRecordFoldTM GapCVP.CNFFlatPhysicalBinaryAppendTM

-- @@ L50-50 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM


-- @@ L52-55 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentSourceCountWord
    (count : Polynomial ℕ) (original : List Bool) : List Bool :=
  List.replicate (count.eval original.length) true


-- @@ L57-62 verbatim
/-- GapCVP reduction support. -/
noncomputable def fiveFamilyIndependentSourceCountComputable
    (count : Polynomial ℕ) :
    BitTM
      (fiveIndependentSourceCountWord count) :=
  polynomialValueUnaryComputable count


-- @@ L64-67 verbatim
private def fiveIndependentSourceRankDescriptorWord
    (count : Polynomial ℕ) (original : List Bool) : List Bool :=
  sourceCanonicalUnaryGridIndexOutput
    (fiveIndependentSourceCountWord count original ++ [false])


-- @@ L69-82 verbatim
private noncomputable def fiveFamilyIndependentSourceRankDescriptorComputable
    (count : Polynomial ℕ) :
    BitTM
      (fiveIndependentSourceRankDescriptorWord count) := by
  have query := pointwiseAppendComputable
    (fiveFamilyIndependentSourceCountComputable count)
    (constantWordComputable [false])
  have physical := GapCVP.TMComposition.computableInPolyTime
    query sourceCanonicalUnaryGridIndexComputable
  change BitTM
    (fun original => sourceCanonicalUnaryGridIndexOutput
      (fiveIndependentSourceCountWord
        count original ++ [false]))
  simpa only [Function.comp_def] using physical


-- @@ L84-87 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentSourceRankWords
    (count : ℕ) : List (List Bool) :=
  (List.range count).map fun rank => List.replicate rank true


-- @@ L89-96 verbatim
@[simp] private theorem fiveFamilyIndependentSourceRankWords_descriptors
    (count : ℕ) :
    (fiveIndependentSourceRankWords count).flatMap
        lengthPrefixedWord =
      sourceCanonicalUnaryGridIndexDescriptors count := by
  simp only [fiveIndependentSourceRankWords,
    sourceCanonicalUnaryGridIndexDescriptors, List.flatMap_map]
  rfl


-- @@ L98-105 verbatim
@[simp] private theorem fiveFamilyIndependentSourceRankDescriptorWord_valid
    (count : Polynomial ℕ) (original : List Bool) :
    fiveIndependentSourceRankDescriptorWord
        count original =
      sourceCanonicalUnaryGridIndexDescriptors
        (count.eval original.length) := by
  simp only [fiveIndependentSourceRankDescriptorWord, fiveIndependentSourceCountWord,
      sourceCanonicalUnaryGridIndexOutput_valid, List.append_nil]


-- @@ L107-118 verbatim
private def fiveIndependentAnchoredFamilyFoldInput
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveIndependentSourceCountWord count original ++
    false ::
      (lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        fiveIndependentSourceRankDescriptorWord
          count original)


-- @@ L120-145 verbatim
private noncomputable def fiveFamilyIndependentAnchoredFamilyFoldInputComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAnchoredFamilyFoldInput
        bound count machine) := by
  have anchor := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatOriginalSourceAnchorComputable bound machine)
    structuralPrefixWriterComputable
  have seed := pointwiseAppendComputable
    anchor (fiveFamilyIndependentSourceRankDescriptorComputable count)
  have delimiter := GapCVP.TMComposition.computableInPolyTime
    seed (prependBitComputable false)
  have physical := pointwiseAppendComputable
    (fiveFamilyIndependentSourceCountComputable count) delimiter
  change BitTM
    (fun original =>
      fiveIndependentSourceCountWord count original ++
        false ::
          (lengthPrefixedWord
            (fiveFlatOriginalSourceAnchorWord
              bound machine original) ++
            fiveIndependentSourceRankDescriptorWord
              count original))
  simpa only [Function.comp_def] using physical


-- @@ L147-156 verbatim
private def fiveIndependentAnchoredFamilyCatalogueWord
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool) : List Bool :=
  boundedRecordFoldOutput
    (sourceAnchoredGridRecordRotationOutput candidate)
    (fiveIndependentAnchoredFamilyFoldInput
      bound count machine original)


-- @@ L158-177 verbatim
private noncomputable def fiveFamilyIndependentAnchoredFamilyCatalogueComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentAnchoredFamilyFoldInputComputable
      bound count machine)
    (sourceAnchoredGridRecordFoldComputable computer)
  change BitTM
    (fun original =>
      boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput candidate)
        (fiveIndependentAnchoredFamilyFoldInput
          bound count machine original))
  simpa only [Function.comp_def] using physical


-- @@ L179-237 verbatim
private theorem fiveFamilyIndependentAnchoredFamilyCatalogueWord_valid
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool)
    (hfit : ∀ rank : Fin (count.eval original.length),
      (candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length) :
    fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate original =
      lengthPrefixedWord
        (fiveFlatOriginalSourceAnchorWord
          bound machine original) ++
        (fiveIndependentSourceRankWords
          (count.eval original.length)).flatMap
            (fun rank => lengthPrefixedWord
              (candidate (lengthPrefixedWord rank ++
                fiveFlatOriginalSourceAnchorWord
                  bound machine original))) := by
  let size := count.eval original.length
  let ranks := fiveIndependentSourceRankWords size
  have hranks : ranks.length = size := by
    simp only [fiveIndependentSourceRankWords, List.length_map, List.length_range, ranks]
  have hfit' : ∀ rank ∈ ranks,
      (candidate
        (lengthPrefixedWord rank ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length := by
    intro rank hrank
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hrank
    have hlt : index < size := by
      simpa only [List.mem_range] using hindex
    exact hfit ⟨index, hlt⟩
  have hseed :
      fiveIndependentAnchoredFamilyFoldInput
        bound count machine original =
        unaryBoundedFoldWord ranks.length
          (lengthPrefixedWord
              (fiveFlatOriginalSourceAnchorWord
                bound machine original) ++
            ranks.flatMap lengthPrefixedWord ++ []) := by
    simp only [fiveIndependentAnchoredFamilyFoldInput, fiveIndependentSourceCountWord,
        fiveFamilyIndependentSourceRankDescriptorWord_valid, unaryBoundedFoldWord, hranks,
        fiveFamilyIndependentSourceRankWords_descriptors, List.append_nil, ranks, size]
  unfold fiveIndependentAnchoredFamilyCatalogueWord
  rw [hseed,
    boundedRecordFoldOutput_sourceAnchoredGridRecordRanks
      candidate
      (fiveFlatOriginalSourceAnchorWord
        bound machine original)
      ranks [] hfit']
  simp only [List.append_nil, ranks, size]


-- @@ L239-248 verbatim
/-- GapCVP reduction support. -/
def fiveIndependentAnchoredFamilyBundledStreamWord
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool) : List Bool :=
  firstFieldSuffix
    (fiveIndependentAnchoredFamilyCatalogueWord
      bound count machine candidate original)


-- @@ L250-268 verbatim
/-- Internal support shared across GapCVP continuation modules. -/
noncomputable def fiveIndependentAnchoredFamilyBundledStreamComputable
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (fiveIndependentAnchoredFamilyBundledStreamWord
        bound count machine candidate) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyIndependentAnchoredFamilyCatalogueComputable
      bound count machine computer)
    firstFieldSuffixComputable
  change BitTM
    (fun original => firstFieldSuffix
      (fiveIndependentAnchoredFamilyCatalogueWord
        bound count machine candidate original))
  simpa only [Function.comp_def] using physical


-- @@ L270-301 verbatim
theorem fiveFamilyIndependentAnchoredFamilyBundledStreamWord_valid
    (bound count : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (candidate : List Bool → List Bool)
    (original : List Bool)
    (hfit : ∀ rank : Fin (count.eval original.length),
      (candidate
        (lengthPrefixedWord (List.replicate rank.val true) ++
          fiveFlatOriginalSourceAnchorWord
            bound machine original)).length ≤
        (fiveFlatOriginalSourceAnchorWord
          bound machine original).length) :
    fiveIndependentAnchoredFamilyBundledStreamWord
        bound count machine candidate original =
      (fiveIndependentSourceRankWords
        (count.eval original.length)).flatMap
          (fun rank => lengthPrefixedWord
            (candidate (lengthPrefixedWord rank ++
              fiveFlatOriginalSourceAnchorWord
                bound machine original))) := by
  unfold fiveIndependentAnchoredFamilyBundledStreamWord
  rw [fiveFamilyIndependentAnchoredFamilyCatalogueWord_valid
    bound count machine candidate original hfit]
  exact firstFieldSuffix_valid
    (fiveFlatOriginalSourceAnchorWord bound machine original)
    ((fiveIndependentSourceRankWords
      (count.eval original.length)).flatMap
        (fun rank => lengthPrefixedWord
          (candidate (lengthPrefixedWord rank ++
            fiveFlatOriginalSourceAnchorWord
              bound machine original))))


-- @@ L303-303 verbatim
end CNFFiveFamilyIndependentAnchoredFamilyStreamTM


-- @@ L305-305 verbatim
namespace CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM


-- @@ L307-307 verbatim
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation

-- @@ L308-308 verbatim
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding

-- @@ L309-309 verbatim
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter

-- @@ L310-310 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

-- @@ L311-311 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM

-- @@ L312-312 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM

-- @@ L313-313 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM

-- @@ L314-314 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM

-- @@ L315-315 verbatim
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM

-- @@ L316-316 verbatim
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM

-- @@ L317-317 verbatim
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM

-- @@ L318-318 verbatim
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM


-- @@ L320-342 verbatim
theorem fiveFamilyActualAnnotatedRecord_fits_originalAnchor
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool)
    (clause : Clause
      (rowWidth bound machine original)
      (completePhaseSymbolCount machine.tm)) :
    (flatSourceClauseAnnotatedRecord clause).length ≤
      (fiveFlatOriginalSourceAnchorWord
        bound machine original).length := by
  have hbound := flatSourceClauseAnnotatedRecord_length_le clause
  have hpolynomial := flatSourceAnnotatedClauseLengthBound_eq_polynomial
    bound machine original
  change
    (flatSourceClauseAnnotatedRecord clause).length ≤
      flatSourceAnnotatedClauseLengthBound
        (rowWidth bound machine original)
        (completePhaseSymbolCount machine.tm) at hbound
  rw [hpolynomial] at hbound
  simp only [fiveFlatOriginalSourceAnchorWord,
    List.length_append, List.length_replicate]
  omega


-- @@ L344-344 verbatim
end CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM


-- @@ L346-346 verbatim
end GapCVP


-- @@ L348-348 verbatim
end
