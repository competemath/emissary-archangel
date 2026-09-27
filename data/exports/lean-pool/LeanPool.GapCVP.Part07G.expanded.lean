/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.GapCVP.Part07F


-- @@ L11-11 verbatim
/-! # GapCVP proof, part 07, continuation 07 -/


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
namespace CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM


-- @@ L27-27 verbatim
open Computability Turing GapCVP.CL GapCVP.CLNondeterminism GapCVP.CLCompleteVerifierSimulation


-- @@ L29-29 verbatim
open GapCVP.CLCellRowBounds GapCVP.CLPaddedAcceptanceCompiler GapCVP.BinaryEncoding


-- @@ L31-31 verbatim
open GapCVP.SourceUniformTuringTM GapCVP.CLStructuralPrefixWriter


-- @@ L33-33 verbatim
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.CNFFiveFamilyFlatCandidateGenerationTM


-- @@ L35-35 verbatim
open GapCVP.CNFFiveFamilyFlatIndexedCatalogueTM GapCVP.CNFFiveFamilyFlatIndexedRankArithmeticTM


-- @@ L37-37 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorCatalogueTM


-- @@ L39-39 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtLeastClauseWorkerTM


-- @@ L41-41 verbatim
open GapCVP.CNFFiveFamilyFlatRowMajorAtMostClauseWorkerTM


-- @@ L43-43 verbatim
open GapCVP.CNFFiveFamilyFlatAcceptanceClauseFoldTM


-- @@ L45-45 verbatim
open GapCVP.CNFFiveFamilyPackedInitialCellDecoderTM


-- @@ L47-47 verbatim
open GapCVP.CNFFiveFamilyForbiddenWholeClauseExactSourceTM


-- @@ L49-49 verbatim
open GapCVP.CNFFiveFamilyIndependentAnchoredFamilyStreamTM


-- @@ L51-56 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentFixedFamilyStreamWord
    {α : Type} (indices : List α)
    (stream : α → List Bool → List Bool)
    (original : List Bool) : List Bool :=
  indices.foldr (fun index output => stream index original ++ output) []


-- @@ L58-77 verbatim
private noncomputable def fiveFamilyIndependentFixedFamilyStreamComputable
    {α : Type} (indices : List α)
    (stream : α → List Bool → List Bool)
    (computers : ∀ index ∈ indices,
      BitTM (stream index)) :
    BitTM
      (fiveIndependentFixedFamilyStreamWord indices stream) := by
  induction indices with
  | nil =>
      exact constantWordComputable []
  | cons index remaining ih =>
      have hfirst := computers index (by simp only [List.mem_cons, true_or])
      have hrest := ih (fun next hnext =>
        computers next (by simp only [List.mem_cons, hnext, or_true]))
      have physical := pointwiseAppendComputable hfirst hrest
      change BitTM
        (fun original => stream index original ++
          fiveIndependentFixedFamilyStreamWord
            remaining stream original)
      exact physical


-- @@ L79-92 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentAtLeastBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1))


-- @@ L94-107 verbatim
private noncomputable def fiveFamilyIndependentAtLeastBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAtLeastBundledStreamWord bound machine) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyFlatRowMajorAtLeastClauseRecordComputable
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1))


-- @@ L109-116 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentAtMostFixedPairWorker
    (grid : Polynomial ℕ)
    (alphabet first second : ℕ) : List Bool → List Bool :=
  if first < second then
    fiveFlatRowMajorAtMostClauseRecordWord grid first second
  else
    fiveFlatRowMajorAtLeastClauseRecordWord grid alphabet


-- @@ L118-132 verbatim
private noncomputable def fiveFamilyIndependentAtMostFixedPairWorkerComputable
    (grid : Polynomial ℕ)
    (alphabet first second : ℕ) :
    BitTM
      (fiveIndependentAtMostFixedPairWorker
        grid alphabet first second) := by
  by_cases hpair : first < second
  · simpa only [fiveIndependentAtMostFixedPairWorker, hpair,
      ↓reduceIte] using
      fiveFamilyFlatRowMajorAtMostClauseRecordComputable
        grid first second
  · simpa only [fiveIndependentAtMostFixedPairWorker, hpair,
      ↓reduceIte] using
      fiveFamilyFlatRowMajorAtLeastClauseRecordComputable
        grid alphabet


-- @@ L134-150 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentAtMostFixedPairBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveIndependentAtMostFixedPairWorker
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      pair.1.val pair.2.val)


-- @@ L152-169 verbatim
private noncomputable def fiveFamilyIndependentAtMostFixedPairBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (pair : Symbol (completePhaseSymbolCount machine.tm) ×
      Symbol (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentAtMostFixedPairBundledStreamWord
        bound machine pair) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (fiveFamilyFlatIndexedGridPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyIndependentAtMostFixedPairWorkerComputable
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)
      pair.1.val pair.2.val)


-- @@ L171-181 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentAtMostBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentFixedFamilyStreamWord
    (fiveFamilyRowMajorSymbolPairs
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentAtMostFixedPairBundledStreamWord
      bound machine)


-- @@ L183-196 verbatim
private noncomputable def fiveFamilyIndependentAtMostBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAtMostBundledStreamWord bound machine) :=
  fiveFamilyIndependentFixedFamilyStreamComputable
    (fiveFamilyRowMajorSymbolPairs
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentAtMostFixedPairBundledStreamWord
      bound machine)
    (fun pair _ =>
      fiveFamilyIndependentAtMostFixedPairBundledStreamComputable
        bound machine pair)


-- @@ L198-207 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentInitialBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine (fiveFlatWholePackedInitialClauseRecordWord
      bound machine)


-- @@ L209-218 verbatim
private noncomputable def fiveFamilyIndependentInitialBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentInitialBundledStreamWord bound machine) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound (fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine (fiveFamilyFlatWholePackedInitialClauseRecordComputable
      bound machine)


-- @@ L220-228 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentAcceptanceBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  lengthPrefixedWord
    (fiveFlatWholeAcceptanceClauseRecordWord
      bound machine original)


-- @@ L230-245 verbatim
private noncomputable def fiveFamilyIndependentAcceptanceBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentAcceptanceBundledStreamWord
        bound machine) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    (fiveFamilyFlatWholeAcceptanceClauseRecordComputable
      bound machine)
    structuralPrefixWriterComputable
  change BitTM
    (fun original => lengthPrefixedWord
      (fiveFlatWholeAcceptanceClauseRecordWord
        bound machine original))
  simpa only [Function.comp_def] using physical


-- @@ L247-262 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentForbiddenFixedTupleWorker
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  if paddedAcceptancePhaseSymbolAllowed machine symbols = false then
    fiveForbiddenExactWindowWholeClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      symbols.1.val symbols.2.1.val
      symbols.2.2.1.val symbols.2.2.2.val
  else
    fiveFlatRowMajorAtLeastClauseRecordWord
      (fiveFamilyFlatIndexedGridPolynomial bound machine)
      (completePhaseSymbolCount machine.tm + 1)


-- @@ L264-282 verbatim
private noncomputable def fiveFamilyIndependentForbiddenFixedTupleWorkerComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentForbiddenFixedTupleWorker
        bound machine symbols) := by
  by_cases hforbidden :
      paddedAcceptancePhaseSymbolAllowed machine symbols = false
  · simpa only [fiveIndependentForbiddenFixedTupleWorker, hforbidden, ↓reduceIte] using
        fiveFamilyForbiddenExactWindowWholeClauseRecordComputable
            (fiveFamilyFlatIndexedGridPolynomial bound machine)
          symbols.1.val symbols.2.1.val symbols.2.2.1.val symbols.2.2.2.val
  · simpa only [fiveIndependentForbiddenFixedTupleWorker, hforbidden, Bool.true_eq_false,
      ↓reduceIte] using
        fiveFamilyFlatRowMajorAtLeastClauseRecordComputable (fiveFamilyFlatIndexedGridPolynomial
            bound machine)
          (completePhaseSymbolCount machine.tm + 1)


-- @@ L284-297 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentForbiddenFixedTupleBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    List Bool → List Bool :=
  fiveIndependentAnchoredFamilyBundledStreamWord
    bound
    (nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveIndependentForbiddenFixedTupleWorker
      bound machine symbols)


-- @@ L299-313 verbatim
private noncomputable def fiveFamilyIndependentForbiddenFixedTupleBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (symbols : WindowSymbols (completePhaseSymbolCount machine.tm)) :
    BitTM
      (fiveIndependentForbiddenFixedTupleBundledStreamWord
        bound machine symbols) :=
  fiveIndependentAnchoredFamilyBundledStreamComputable
    bound
    (nondeterministicTableauDimensionPolynomial bound machine *
      fiveFamilyFlatIndexedGridPolynomial bound machine)
    machine
    (fiveFamilyIndependentForbiddenFixedTupleWorkerComputable
      bound machine symbols)


-- @@ L315-325 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentForbiddenBundledStreamWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    List Bool → List Bool :=
  fiveIndependentFixedFamilyStreamWord
    (fiveFamilyRowMajorWindowSymbols
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentForbiddenFixedTupleBundledStreamWord
      bound machine)


-- @@ L327-341 verbatim
private noncomputable def fiveFamilyIndependentForbiddenBundledStreamComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentForbiddenBundledStreamWord
        bound machine) :=
  fiveFamilyIndependentFixedFamilyStreamComputable
    (fiveFamilyRowMajorWindowSymbols
      (completePhaseSymbolCount machine.tm))
    (fiveIndependentForbiddenFixedTupleBundledStreamWord
      bound machine)
    (fun symbols _ =>
      fiveFamilyIndependentForbiddenFixedTupleBundledStreamComputable
        bound machine symbols)


-- @@ L343-358 verbatim
/-- GapCVP reduction support. -/
@[expose] def fiveIndependentActualBundledCatalogueWord
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (original : List Bool) : List Bool :=
  fiveIndependentAtLeastBundledStreamWord
      bound machine original ++
    (fiveIndependentAtMostBundledStreamWord
      bound machine original ++
      (fiveIndependentInitialBundledStreamWord
        bound machine original ++
        (fiveIndependentAcceptanceBundledStreamWord
          bound machine original ++
          fiveIndependentForbiddenBundledStreamWord
            bound machine original)))


-- @@ L360-395 verbatim
/-- GapCVP reduction support. -/
noncomputable def fiveFamilyIndependentActualBundledCatalogueComputable
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    BitTM
      (fiveIndependentActualBundledCatalogueWord
        bound machine) := by
  have hleast := fiveFamilyIndependentAtLeastBundledStreamComputable
    bound machine
  have hmost := fiveFamilyIndependentAtMostBundledStreamComputable
    bound machine
  have hinitial := fiveFamilyIndependentInitialBundledStreamComputable
    bound machine
  have haccept := fiveFamilyIndependentAcceptanceBundledStreamComputable
    bound machine
  have hforbidden := fiveFamilyIndependentForbiddenBundledStreamComputable
    bound machine
  have physical := pointwiseAppendComputable
    hleast (pointwiseAppendComputable
      hmost (pointwiseAppendComputable
        hinitial (pointwiseAppendComputable
          haccept hforbidden)))
  change BitTM
    (fun original =>
      fiveIndependentAtLeastBundledStreamWord
        bound machine original ++
      (fiveIndependentAtMostBundledStreamWord
        bound machine original ++
        (fiveIndependentInitialBundledStreamWord
          bound machine original ++
          (fiveIndependentAcceptanceBundledStreamWord
            bound machine original ++
            fiveIndependentForbiddenBundledStreamWord
              bound machine original))))
  exact physical


-- @@ L397-397 verbatim
end CNFFiveFamilyIndependentFiveFamilyBundledCatalogueTM



-- @@ L400-400 verbatim
end GapCVP


-- @@ L402-402 verbatim
end
