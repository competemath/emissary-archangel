/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzParseval


-- @@ L15-22 verbatim
/-!
# Pairings for the double Riesz transform on test functions

The operator in this file is the inverse Fourier integral from
`Comparison.rieszTest`. Its even, real multiplier gives both the bilinear
transpose identity and the Hermitian Fourier pairing. No extension to an
operator on all of `L²` is used.
-/


-- @@ L24-24 verbatim
@[expose] public section




-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open MeasureTheory

-- @@ L31-31 verbatim
open scoped FourierTransform ComplexConjugate RealInnerProductSpace


-- @@ L33-33 verbatim
namespace NavierStokesR3.RieszTestOperators


-- @@ L35-35 verbatim
open ProblemStatement Comparison


-- @@ L37-42 verbatim
/-- The transformed test can be paired with any integrable complex function. -/
theorem integrable_rieszTest_mul (i j : Fin 3) (ψ : ComplexTest)
    {f : Space → ℂ} (hf : Integrable f) :
    Integrable (fun x : Space => rieszTest i j ψ x * f x) := by
  apply hf.bdd_mul (continuous_rieszTest i j ψ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_rieszTest_le_integral i j ψ)


-- @@ L44-48 verbatim
/-- The integrable input may also be placed on the left of the pairing. -/
theorem integrable_mul_rieszTest (i j : Fin 3) (ψ : ComplexTest)
    {f : Space → ℂ} (hf : Integrable f) :
    Integrable (fun x : Space => f x * rieszTest i j ψ x) := by
  simpa only [mul_comm] using integrable_rieszTest_mul i j ψ hf


-- @@ L50-54 verbatim
/-- The Hermitian pairing with a Schwartz test is integrable. -/
theorem integrable_rieszTest_mul_conj (i j : Fin 3) (ψ φ : ComplexTest) :
    Integrable (fun x : Space => rieszTest i j ψ x * conj (φ x)) :=
  integrable_rieszTest_mul i j ψ
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp φ.integrable)


-- @@ L56-71 verbatim
/-- Fourier duality with the inverse Fourier kernel. -/
theorem integral_fourierInv_mul {f g : Space → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : Space, 𝓕⁻ (f : Space → ℂ) x * g x) =
      ∫ ξ : Space, f ξ * 𝓕 (g : Space → ℂ) (-ξ) := by
  have hflip : (-innerₗ Space).flip = -innerₗ Space := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm y x).symm
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -innerₗ Space)
    (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
    Real.continuous_fourierChar (innerSL ℝ).continuous₂.neg hf hg
  rw [hflip] at h
  simp only [smul_eq_mul] at h
  change (∫ x : Space, 𝓕⁻ f x * g x) = ∫ ξ : Space, f ξ * 𝓕⁻ g ξ at h
  simpa only [Real.fourierInv_eq_fourier_neg] using h


-- @@ L73-78 verbatim
/-- Conjugation changes the inverse Fourier kernel into the Fourier kernel. -/
theorem fourierInv_conj_apply (f : Space → ℂ) (ξ : Space) :
    𝓕⁻ (fun x => conj (f x)) ξ = conj (𝓕 (f : Space → ℂ) ξ) := by
  rw [Real.fourierInv_eq_fourier_neg,
    SchwartzParseval.fourier_conj_apply,
    Real.fourierInv_eq_fourier_neg, neg_neg]


-- @@ L80-86 verbatim
/-- Pair the actual double Riesz transform with a Schwartz function in Fourier space. -/
theorem rieszTest_pairing_fourier (i j : Fin 3) (ψ φ : ComplexTest) :
    (∫ x : Space, rieszTest i j ψ x * φ x) =
      ∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 (ψ : Space → ℂ) ξ * 𝓕 (φ : Space → ℂ) (-ξ) := by
  change (∫ x : Space, rieszTest i j ψ x * φ x) =
      ∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 ψ ξ * 𝓕 φ (-ξ)
  exact integral_fourierInv_mul (integrable_rieszMultiplier i j ψ) φ.integrable


-- @@ L88-101 verbatim
/-- Hermitian Fourier pairing for the actual double Riesz transform. -/
theorem rieszTest_pairing_fourier_conj (i j : Fin 3) (ψ φ : ComplexTest) :
    (∫ x : Space, rieszTest i j ψ x * conj (φ x)) =
      ∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 (ψ : Space → ℂ) ξ * conj (𝓕 (φ : Space → ℂ) ξ) := by
  change (∫ x : Space, rieszTest i j ψ x * conj (φ x)) =
      ∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 ψ ξ * conj (𝓕 φ ξ)
  have hφ : Integrable (fun x : Space => conj (φ x)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp φ.integrable
  rw [rieszTest, integral_fourierInv_mul (integrable_rieszMultiplier i j ψ) hφ]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [SchwartzParseval.fourier_conj_apply,
    Real.fourierInv_eq_fourier_neg, neg_neg]
  simp only [EulerSobolev.schwartzFourier_apply, SchwartzMap.fourier_coe]


-- @@ L103-125 verbatim
/-- The even Riesz multiplier makes the bilinear pairing symmetric. -/
theorem rieszTest_selfAdjoint (i j : Fin 3) (ψ φ : ComplexTest) :
    (∫ x : Space, rieszTest i j ψ x * φ x) =
      ∫ x : Space, ψ x * rieszTest i j φ x := by
  rw [rieszTest_pairing_fourier]
  calc
    (∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 ψ ξ * 𝓕 φ (-ξ)) =
        ∫ ξ : Space, (rieszSymbol i j ξ : ℂ) * 𝓕 φ ξ * 𝓕 ψ (-ξ) := by
      rw [← (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving.integral_comp
        (LinearIsometryEquiv.neg ℝ (E := Space)).toHomeomorph.measurableEmbedding
        (fun ξ : Space => (rieszSymbol i j ξ : ℂ) * 𝓕 ψ ξ * 𝓕 φ (-ξ))]
      apply integral_congr_ae
      filter_upwards [] with ξ
      change (rieszSymbol i j (-ξ) : ℂ) * 𝓕 ψ (-ξ) * 𝓕 φ (-(-ξ)) =
        (rieszSymbol i j ξ : ℂ) * 𝓕 φ ξ * 𝓕 ψ (-ξ)
      rw [rieszSymbol_neg, neg_neg]
      ring
    _ = ∫ x : Space, rieszTest i j φ x * ψ x :=
      (rieszTest_pairing_fourier i j φ ψ).symm
    _ = ∫ x : Space, ψ x * rieszTest i j φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _


-- @@ L127-127 verbatim
end NavierStokesR3.RieszTestOperators
