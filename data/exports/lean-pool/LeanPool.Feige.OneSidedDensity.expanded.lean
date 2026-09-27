/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import LeanPool.Feige.LikelihoodRatio
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L11-17 verbatim
/-!
# Log-concavity of scaled one-sided exponential densities

The common part in each insertion edge is a convolution of positive and
negative scaled exponentials.  This file verifies the four-point
log-concavity condition for each individual one-sided exponential factor.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped ENNReal


-- @@ L23-23 verbatim
namespace Feige

-- @@ L24-24 verbatim
namespace LikelihoodRatio


-- @@ L26-28 verbatim
/-- Density of `aE`, up to the canonical Lebesgue interpretation. -/
noncomputable def rightExponentialDensity (a x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x then ENNReal.ofReal (Real.exp (-x / a) / a) else 0


-- @@ L30-33 verbatim
theorem measurable_rightExponentialDensity (a : ℝ) :
    Measurable (rightExponentialDensity a) := by
  unfold rightExponentialDensity
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const


-- @@ L35-60 verbatim
/-- A positive scaled exponential density satisfies the multiplicative
four-point form of log-concavity, including its zero extension outside its
half-line support. -/
theorem fourPointLogConcave_rightExponentialDensity
    {a : ℝ} (ha : 0 < a) :
    FourPointLogConcave (rightExponentialDensity a) := by
  intro r p q s hrp hpq hrs hsq hsum
  by_cases hr : 0 ≤ r
  · have hp : 0 ≤ p := hr.trans hrp
    have hq : 0 ≤ q := hp.trans hpq
    have hs : 0 ≤ s := hr.trans hrs
    simp only [rightExponentialDensity, ite_eq_left hr, ite_eq_left hp, ite_eq_left hq,
      ite_eq_left hs]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_nonneg _) ha.le),
      ← ENNReal.ofReal_mul (div_nonneg (Real.exp_nonneg _) ha.le)]
    apply ENNReal.ofReal_le_ofReal
    have hreal :
        (Real.exp (-r / a) / a) * (Real.exp (-q / a) / a) =
          (Real.exp (-p / a) / a) * (Real.exp (-s / a) / a) := by
      field_simp [ne_of_gt ha]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp [ne_of_gt ha]
      linarith
    exact hreal.le
  · simp [rightExponentialDensity, hr]


-- @@ L62-71 verbatim
/-- Reflection of a four-point log-concave function is again four-point
log-concave. -/
theorem FourPointLogConcave.reflect {f : ℝ → ℝ≥0∞}
    (hf : FourPointLogConcave f) :
    FourPointLogConcave (fun x ↦ f (-x)) := by
  intro r p q s hrp hpq hrs hsq hsum
  have h := hf
    (r := -q) (p := -p) (q := -r) (s := -s)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  simpa [mul_comm] using h


-- @@ L73-75 verbatim
/-- Density of `-bE`. -/
noncomputable def leftExponentialDensity (b x : ℝ) : ℝ≥0∞ :=
  rightExponentialDensity b (-x)


-- @@ L77-79 verbatim
theorem measurable_leftExponentialDensity (b : ℝ) :
    Measurable (leftExponentialDensity b) := by
  exact (measurable_rightExponentialDensity b).comp measurable_neg


-- @@ L81-84 verbatim
theorem fourPointLogConcave_leftExponentialDensity
    {b : ℝ} (hb : 0 < b) :
    FourPointLogConcave (leftExponentialDensity b) := by
  exact (fourPointLogConcave_rightExponentialDensity hb).reflect


-- @@ L86-86 verbatim
end LikelihoodRatio

-- @@ L87-87 verbatim
end Feige
