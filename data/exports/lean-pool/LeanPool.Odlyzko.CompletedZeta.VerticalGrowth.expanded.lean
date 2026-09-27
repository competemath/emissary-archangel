/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredRepresentative
import Mathlib.Tactic.ArithMult.Init


-- @@ L12-16 verbatim
/-!
# Vertical Growth

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
section


-- @@ L24-24 verbatim
open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units

-- @@ L25-25 verbatim
open scoped nonZeroDivisors


-- @@ L27-27 verbatim
namespace NumberField.Odlyzko


-- @@ L29-29 verbatim
open mixedEmbedding


-- @@ L31-31 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L33-54 verbatim
theorem norm_centeredPositiveClassThetaIntegral_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} {b : ℝ}
    (hsb : s.re ≤ b) :
    ‖centeredPositiveClassThetaIntegral K I s‖ ≤
      ∫ y in positiveUnitFundamentalParamSet (K := K),
        ‖centeredNonzeroFractionalShapeThetaMellinKernel K
          (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) (b : ℂ) y‖ := by
  rw [centeredPositiveClassThetaIntegral_eq_numerator K I]
  rw [centeredPositiveClassThetaIntegral]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_ae
  · exact
      (integrableOn_positive_centeredNonzeroFractionalShapeThetaMellinKernel_mk0
        K (fractionalIdealNumerator K I) s).norm
  · exact
      (integrableOn_positive_centeredNonzeroFractionalShapeThetaMellinKernel_mk0
        K (fractionalIdealNumerator K I) (b : ℂ)).norm
  · filter_upwards
      [ae_restrict_mem measurableSet_positiveUnitFundamentalParamSet] with y hy
    exact norm_centeredNonzeroFractionalShapeThetaMellinKernel_mono K
      (I := FractionalIdeal.mk0 K (fractionalIdealNumerator K I))
      (le_of_lt hy.2) hsb


-- @@ L56-57 verbatim
theorem abs_le_max_abs_endpoints {a b σ : ℝ} (hσ : σ ∈ Set.Icc a b) :
    |σ| ≤ max |a| |b| := by grind


-- @@ L59-61 verbatim
/-- A centered class theta vertical radius used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaVerticalRadius (a b : ℝ) : ℝ :=
  max (max |a| |b|) (max |1 - b| |1 - a|) + 1


-- @@ L63-66 verbatim
theorem one_le_centeredClassThetaVerticalRadius (a b : ℝ) :
    1 ≤ centeredClassThetaVerticalRadius a b := by
  unfold centeredClassThetaVerticalRadius
  simp


-- @@ L68-106 verbatim
theorem norm_vertical_pole_factors_le
    {a b σ t : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ‖(σ : ℂ) + t * I‖ ≤
        centeredClassThetaVerticalRadius a b * (1 + |t|) ∧
      ‖1 - ((σ : ℂ) + t * I)‖ ≤
        centeredClassThetaVerticalRadius a b * (1 + |t|) := by
  let D := centeredClassThetaVerticalRadius a b
  have hD : 1 ≤ D := one_le_centeredClassThetaVerticalRadius a b
  have hσabs : |σ| ≤ D := by
    refine (abs_le_max_abs_endpoints hσ).trans ?_
    dsimp [D, centeredClassThetaVerticalRadius]
    grind
  have honesub : |1 - σ| ≤ D := by
    have hmem : 1 - σ ∈ Set.Icc (1 - b) (1 - a) := by
      grind
    refine (abs_le_max_abs_endpoints hmem).trans ?_
    dsimp [D, centeredClassThetaVerticalRadius]
    grind
  have ht : 0 ≤ |t| := abs_nonneg t
  constructor
  · calc
      ‖(σ : ℂ) + t * I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ ≤ D + |t| := add_le_add hσabs le_rfl
      _ ≤ D * (1 + |t|) := by nlinarith
  · have heq :
        1 - ((σ : ℂ) + t * I) = ((1 - σ : ℝ) : ℂ) + (-t) * I := by
      apply Complex.ext <;> simp
    calc
      ‖1 - ((σ : ℂ) + t * I)‖ =
          ‖((1 - σ : ℝ) : ℂ) + (-t) * I‖ := by simp_all
      _ ≤ ‖((1 - σ : ℝ) : ℂ)‖ + ‖(-(t : ℂ)) * I‖ :=
        norm_add_le _ _
      _ = |1 - σ| + |t| := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one]
      _ ≤ D + |t| := add_le_add honesub le_rfl
      _ ≤ D * (1 + |t|) := by nlinarith


-- @@ L108-113 verbatim
/-- A centered positive class theta norm bound used in the Odlyzko-bound argument. -/
noncomputable def centeredPositiveClassThetaNormBound
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ℝ) : ℝ :=
  ∫ y in positiveUnitFundamentalParamSet (K := K),
    ‖centeredNonzeroFractionalShapeThetaMellinKernel K
      (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) (b : ℂ) y‖


-- @@ L115-119 verbatim
omit [IsTotallyComplex K] in
theorem centeredPositiveClassThetaNormBound_nonneg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ℝ) :
    0 ≤ centeredPositiveClassThetaNormBound K I b :=
  integral_nonneg fun _ ↦ norm_nonneg _


-- @@ L121-127 verbatim
/-- A pole cleared centered class theta vertical bound used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredClassThetaVerticalBound
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : ℝ) : ℝ :=
  (Module.finrank ℚ K : ℝ) *
      (centeredPositiveClassThetaNormBound K I b +
        centeredPositiveClassThetaNormBound K (traceDualIdealUnit K I) (1 - a)) *
      centeredClassThetaVerticalRadius a b ^ 2 + 1


-- @@ L129-137 verbatim
omit [IsTotallyComplex K] in
theorem poleClearedCenteredClassThetaVerticalBound_nonneg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a b : ℝ) :
    0 ≤ poleClearedCenteredClassThetaVerticalBound K I a b := by
  unfold poleClearedCenteredClassThetaVerticalBound
  have hI := centeredPositiveClassThetaNormBound_nonneg K I b
  have hdual :=
    centeredPositiveClassThetaNormBound_nonneg K (traceDualIdealUnit K I) (1 - a)
  positivity


-- @@ L139-196 verbatim
theorem norm_poleClearedCenteredClassThetaIntegral_vertical_le
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {a b σ t : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ‖poleClearedCenteredClassThetaIntegral K I ((σ : ℂ) + t * Complex.I)‖ ≤
      poleClearedCenteredClassThetaVerticalBound K I a b * (1 + |t|) ^ 2 := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  let D := centeredClassThetaVerticalRadius a b
  let P := centeredPositiveClassThetaNormBound K I b
  let Q :=
    centeredPositiveClassThetaNormBound K (traceDualIdealUnit K I) (1 - a)
  have hD : 0 ≤ D := (one_le_centeredClassThetaVerticalRadius a b).trans' zero_le_one
  have hfac := norm_vertical_pole_factors_le (t := t) hσ
  have hsbound : ‖s‖ ≤ D * (1 + |t|) := by
    grind
  have : ‖1 - s‖ ≤ D * (1 + |t|) := by grind
  have hA : ‖centeredPositiveClassThetaIntegral K I s‖ ≤ P := by
    apply norm_centeredPositiveClassThetaIntegral_le
    dsimp [s]
    simpa using hσ.2
  have hB :
      ‖centeredPositiveClassThetaIntegral K
          (traceDualIdealUnit K I) (1 - s)‖ ≤ Q := by
    apply norm_centeredPositiveClassThetaIntegral_le
    dsimp [s]
    simp only [ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_one, sub_zero]
    grind
  have hone : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  unfold poleClearedCenteredClassThetaIntegral
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_natCast, norm_one]
  have hadd :
      ‖centeredPositiveClassThetaIntegral K I s +
          centeredPositiveClassThetaIntegral K
            (traceDualIdealUnit K I) (1 - s)‖ ≤ P + Q :=
    (norm_add_le _ _).trans (add_le_add hA hB)
  have hmain :
      (Module.finrank ℚ K : ℝ) * ‖s‖ * ‖1 - s‖ *
          ‖centeredPositiveClassThetaIntegral K I s +
            centeredPositiveClassThetaIntegral K
              (traceDualIdealUnit K I) (1 - s)‖ ≤
        (Module.finrank ℚ K : ℝ) * (P + Q) * D ^ 2 * (1 + |t|) ^ 2 := by
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) *
          (D * (1 + |t|)) * (D * (1 + |t|)) * (P + Q) := by
        gcongr
      _ = _ := by ring
  calc
    (Module.finrank ℚ K : ℝ) * ‖s‖ * ‖1 - s‖ *
          ‖centeredPositiveClassThetaIntegral K I s +
            centeredPositiveClassThetaIntegral K
              (traceDualIdealUnit K I) (1 - s)‖ + 1 ≤
        (Module.finrank ℚ K : ℝ) * (P + Q) * D ^ 2 *
          (1 + |t|) ^ 2 + 1 := by simp_all
    _ ≤ poleClearedCenteredClassThetaVerticalBound K I a b *
          (1 + |t|) ^ 2 := by
      dsimp [poleClearedCenteredClassThetaVerticalBound, D, P, Q]
      nlinarith


-- @@ L198-198 verbatim
end NumberField.Odlyzko


-- @@ L200-200 verbatim
end


-- @@ L202-202 verbatim
section


-- @@ L204-204 verbatim
open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units

-- @@ L205-205 verbatim
open scoped nonZeroDivisors


-- @@ L207-207 verbatim
namespace NumberField.Odlyzko


-- @@ L209-209 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]


-- @@ L211-216 verbatim
open Classical in
/-- A centered fractional class normalization norm used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalClassNormalizationNorm : ℝ :=
  ‖(torsionOrder K : ℂ)⁻¹ *
      (2 : ℂ) ^ nrComplexPlaces K *
      (shapeThetaIntegralConstant K : ℂ)‖


-- @@ L218-225 verbatim
open Classical in
/-- A pole cleared completed dedekind zeta vertical bound used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaVerticalBound
    (a b : ℝ) : ℝ :=
  ∑ C : ClassGroup (𝓞 K),
    centeredFractionalClassNormalizationNorm K *
      poleClearedCenteredClassThetaVerticalBound K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b


-- @@ L227-236 verbatim
omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCompletedDedekindZetaVerticalBound_nonneg (a b : ℝ) :
    0 ≤ poleClearedCompletedDedekindZetaVerticalBound K a b := by
  unfold poleClearedCompletedDedekindZetaVerticalBound
  apply Finset.sum_nonneg
  intro C _
  exact mul_nonneg
    (norm_nonneg _)
    (poleClearedCenteredClassThetaVerticalBound_nonneg K _ a b)


-- @@ L238-268 verbatim
open Classical in
theorem norm_poleClearedCompletedDedekindZetaContinuation_vertical_le
    {a b σ t : ℝ} (hσ : σ ∈ Set.Icc a b) :
    ‖poleClearedCompletedDedekindZetaContinuation K
        ((σ : ℂ) + t * I)‖ ≤
      poleClearedCompletedDedekindZetaVerticalBound K a b *
        (1 + |t|) ^ 2 := by
  rw [poleClearedCompletedDedekindZetaContinuation]
  refine (norm_sum_le _ _).trans ?_
  rw [poleClearedCompletedDedekindZetaVerticalBound, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro C _
  rw [poleClearedCenteredFractionalClassContribution, norm_mul]
  calc
    ‖(torsionOrder K : ℂ)⁻¹ * (2 : ℂ) ^ nrComplexPlaces K *
          (shapeThetaIntegralConstant K : ℂ)‖ *
        ‖poleClearedCenteredClassThetaIntegral K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))
          ((σ : ℂ) + t * I)‖ ≤
      centeredFractionalClassNormalizationNorm K *
        (poleClearedCenteredClassThetaVerticalBound K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b *
            (1 + |t|) ^ 2) := by
      unfold centeredFractionalClassNormalizationNorm
      exact mul_le_mul_of_nonneg_left
        (norm_poleClearedCenteredClassThetaIntegral_vertical_le K _ hσ)
        (norm_nonneg _)
    _ = centeredFractionalClassNormalizationNorm K *
          poleClearedCenteredClassThetaVerticalBound K
            (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) a b *
          (1 + |t|) ^ 2 := by ring


-- @@ L270-270 verbatim
end NumberField.Odlyzko


-- @@ L272-272 verbatim
end
