/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ConeGaussianIntegral


-- @@ L10-10 verbatim
/-! TODO: Add doc-string. -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-17 verbatim
open Complex Ideal IsDedekindDomain MeasureTheory NumberField NumberField.Units
  NumberField.InfinitePlace

-- @@ L18-18 verbatim
open scoped nonZeroDivisors


-- @@ L20-20 verbatim
namespace NumberField.Odlyzko


-- @@ L22-22 verbatim
open mixedEmbedding fundamentalCone


-- @@ L24-24 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L26-32 verbatim
private theorem eventually_forall_pos_complexPlace :
    ∀ᵐ q : InfinitePlace K → ℝ
  ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0)),
      ∀ w, 0 < q w := by
  apply Measure.ae_pi_le_pi
  exact Filter.eventually_pi fun _ ↦
    ae_restrict_mem measurableSet_Ioi


-- @@ L34-52 verbatim
theorem norm_complexPlaceMellinGaussian
    (x : K) (s : ℂ) (q : InfinitePlace K → ℝ) (hq : ∀ w, 0 < q w) :
    (‖complexPlaceMellinGaussian K x s q‖ : ℂ) =
      complexPlaceMellinGaussian K x (s.re : ℂ) q := by
  classical
  rw [complexPlaceMellinGaussian, complexPlaceMellinGaussian, norm_prod]
  push_cast
  apply Finset.prod_congr rfl
  intro w _
  simp only [← Complex.ofReal_pow]
  have harg :
      -(2 * (Real.pi : ℂ) * ((w x) ^ 2 : ℝ) * ((q w) ^ 2 : ℝ)) =
        ((-(2 * Real.pi * (w x) ^ 2 * (q w) ^ 2) : ℝ) : ℂ) := by simp
  rw [harg]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq w),
    Complex.norm_exp, Complex.ofReal_mul,
    Complex.ofReal_cpow (hq w).le]
  simp only [Complex.ofReal_re]
  simp


-- @@ L54-66 verbatim
theorem idealSetElement_injective (J : (Ideal (𝓞 K))⁰) :
    Function.Injective (idealSetElement K J) := by
  intro a b hab
  apply Subtype.ext
  calc
    (a : mixedSpace K) =
        mixedEmbedding K (idealSetElement K J a) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]
    _ = mixedEmbedding K (idealSetElement K J b) := congrArg _ hab
    _ = (b : mixedSpace K) := by
      rw [idealSetElement, mixedEmbedding_preimageOfMemIntegerSet,
        idealSetEquiv_apply]


-- @@ L68-68 verbatim
variable [IsTotallyComplex K]


-- @@ L70-94 verbatim
theorem integral_norm_complexPlaceMellinGaussian
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ q : InfinitePlace K → ℝ,
      ‖complexPlaceMellinGaussian K x s q‖
      ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) =
      ‖((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor (s.re : ℂ)) ^ nrComplexPlaces K *
        ((((|Algebra.norm ℚ x| : ℚ) : ℝ)) : ℂ) ^ (-(s.re : ℂ))‖ := by
  let μ := Measure.pi
    (fun _ : InfinitePlace K ↦ (volume : Measure ℝ).restrict (Set.Ioi 0))
  have heq :
      ((∫ q, ‖complexPlaceMellinGaussian K x s q‖ ∂μ) : ℂ) =
        ∫ q, complexPlaceMellinGaussian K x (s.re : ℂ) q ∂μ := by
    apply integral_congr_ae
    filter_upwards [eventually_forall_pos_complexPlace K] with q hq
    exact norm_complexPlaceMellinGaussian K x s q hq
  dsimp [μ] at heq
  rw [integral_complexPlaceMellinGaussian K hx hs
    (s := (s.re : ℂ))] at heq
  calc
    (∫ q, ‖complexPlaceMellinGaussian K x s q‖ ∂μ) =
        ‖((∫ q, ‖complexPlaceMellinGaussian K x s q‖ ∂μ) : ℂ)‖ := by
      rw [integral_complex_ofReal, Complex.norm_real,
        Real.norm_of_nonneg]
      exact integral_nonneg fun _ ↦ norm_nonneg _
    _ = _ := congrArg norm heq


-- @@ L96-112 verbatim
theorem summable_integral_norm_idealSet_complexPlaceMellinGaussian
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun a : idealSet K J ↦
        ∫ q : InfinitePlace K → ℝ,
          ‖complexPlaceMellinGaussian K (idealSetElement K J a) s q‖
          ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) := by
  have hbase :=
    (summable_idealSet_inverseNormPower K J
      (s := (s.re : ℂ)) hs).norm
  refine (hbase.mul_left
    ‖((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor (s.re : ℂ)) ^
      nrComplexPlaces K‖).congr fun a ↦ ?_
  rw [integral_norm_complexPlaceMellinGaussian K
    (idealSetElement_ne_zero K J a) (lt_trans zero_lt_one hs),
    absNorm_idealSetElement K J a, norm_mul]
  simp


-- @@ L114-114 verbatim
end NumberField.Odlyzko
