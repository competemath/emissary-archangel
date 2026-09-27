/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.PreparationUniqueness


-- @@ L10-15 verbatim
/-!
# Sequence-level Weierstrass division bridge

This file packages the analytic quotient and remainder sequence operators for
prepared divisors so the local complex-geometry development can reuse them.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open scoped ENNReal NNReal Topology


-- @@ L22-22 verbatim
namespace LocalComplexGeometry.WPTBridge.DivisionCore


-- @@ L24-24 verbatim
open ClassicalComplexWPT


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-32 verbatim
/-- Analytic divisor-tail/dividend input for WPT's total sequence division maps. -/
def divisionInput {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) : L1Sequence × L1Sequence :=
  (preparedTailSeq r d a z, (weightedCoefficientSeries p r).sum z)


-- @@ L34-38 verbatim
/-- Sequence quotient supplied by the pinned WPT division operator. -/
def quotientSeq {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) : L1Sequence :=
  seqDivisionQuotientGlobal d (divisionInput p r a z)


-- @@ L40-44 verbatim
/-- Sequence remainder supplied by the pinned WPT division operator. -/
def remainderSeq {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) : L1Sequence :=
  seqDivisionRemainderGlobal d (divisionInput p r a z)


-- @@ L46-51 verbatim
theorem preparedTailSeq_zero {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (ha0 : ∀ i, a i 0 = 0) :
    preparedTailSeq r d a 0 = 0 := by
  classical
  unfold preparedTailSeq
  simp [ha0]


-- @@ L53-57 verbatim
theorem norm_divisionInput_fst_zero_lt_one {n d : ℕ} (r : ℝ≥0)
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (a : Fin d → Base n → ℂ) (ha0 : ∀ i, a i 0 = 0) :
    ‖(divisionInput p r a 0).1‖ < 1 := by
  simp [divisionInput, preparedTailSeq_zero r a ha0]


-- @@ L59-65 verbatim
theorem analyticAt_divisionInput {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (divisionInput p r a) 0 := by
  exact (analyticAt_preparedTailSeq r a ha).prod
    (analyticAt_weightedCoefficientSeries_sum p r hrp)


-- @@ L67-75 verbatim
theorem analyticAt_quotientSeq {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    AnalyticAt ℂ (quotientSeq p r a) 0 := by
  have hout := analyticAt_seqDivisionQuotientGlobal d (divisionInput p r a 0)
    (norm_divisionInput_fst_zero_lt_one r p a ha0)
  exact hout.comp (analyticAt_divisionInput p r hrp a ha)


-- @@ L77-85 verbatim
theorem analyticAt_remainderSeq {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    AnalyticAt ℂ (remainderSeq p r a) 0 := by
  have hout := analyticAt_seqDivisionRemainderGlobal d (divisionInput p r a 0)
    (norm_divisionInput_fst_zero_lt_one r p a ha0)
  exact hout.comp (analyticAt_divisionInput p r hrp a ha)


-- @@ L87-105 verbatim
/-- Pointwise uniqueness of the sequence quotient and low-degree remainder. -/
theorem quotient_remainderSeq_unique {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n)
    (hsmall : ‖preparedTailSeq r d a z‖ < 1)
    (q remainder : L1Sequence)
    (hfactor : (weightedCoefficientSeries p r).sum z =
      seqLowShift d q + convolution q (preparedTailSeq r d a z) + remainder)
    (hsupport : seqHighShift d remainder = 0) :
    q = quotientSeq p r a z ∧ remainder = remainderSeq p r a z := by
  have hcanonical := seqDivisionGlobal_factorization d (preparedTailSeq r d a z)
    ((weightedCoefficientSeries p r).sum z) hsmall
  have hcanonicalSupport := seqHighShift_divisionRemainderGlobal d
    (preparedTailSeq r d a z) ((weightedCoefficientSeries p r).sum z) hsmall
  exact seqDivision_factorizations_unique d (preparedTailSeq r d a z) hsmall
    ((weightedCoefficientSeries p r).sum z) q remainder
    (quotientSeq p r a z) (remainderSeq p r a z) hfactor hsupport
    (by simpa [quotientSeq, remainderSeq, divisionInput] using hcanonical)
    (by simpa [remainderSeq, divisionInput] using hcanonicalSupport)


-- @@ L107-107 verbatim
end


-- @@ L109-109 verbatim
end LocalComplexGeometry.WPTBridge.DivisionCore
