/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith


-- @@ L12-16 verbatim
/-!
# ENNReal Half Scale

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open scoped ENNReal


-- @@ L22-22 verbatim
namespace CKN.Foundation.Measure


-- @@ L24-36 verbatim
/-- For `t > 0` and any extended nonnegative real `X`,
`ENNReal.ofReal A * X / ENNReal.ofReal (t/2) = ENNReal.ofReal (2*A/t) * X`. -/
theorem ofReal_mul_div_ofReal_half {A t : ℝ} (ht : 0 < t) (X : ℝ≥0∞) :
    ENNReal.ofReal A * X / ENNReal.ofReal (t / 2) = ENNReal.ofReal (2 * A / t) * X := by
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht]
  calc ENNReal.ofReal A * X / ENNReal.ofReal (t / 2)
      = (ENNReal.ofReal A / ENNReal.ofReal (t / 2)) * X := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ = ENNReal.ofReal (A / (t / 2)) * X := by rw [ENNReal.ofReal_div_of_pos ht2]
    _ = ENNReal.ofReal (2 * A / t) * X := by
        congr 1
        field_simp


-- @@ L38-55 verbatim
/-- For `t > 0` and any extended nonnegative real `X`,
`ENNReal.ofReal B * X / (ENNReal.ofReal (t/2))^2 = ENNReal.ofReal (4*B/t^2) * X`. -/
theorem ofReal_mul_div_ofReal_half_sq {B t : ℝ} (ht : 0 < t) (X : ℝ≥0∞) :
    ENNReal.ofReal B * X / (ENNReal.ofReal (t / 2)) ^ 2 =
      ENNReal.ofReal (4 * B / t ^ 2) * X := by
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht]
  rw [← ENNReal.ofReal_pow ht2.le]
  have hq : (0 : ℝ) < (t / 2) ^ 2 := by positivity
  calc ENNReal.ofReal B * X / ENNReal.ofReal ((t / 2) ^ 2)
      = (ENNReal.ofReal B / ENNReal.ofReal ((t / 2) ^ 2)) * X := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ = ENNReal.ofReal (B / (t / 2) ^ 2) * X := by rw [ENNReal.ofReal_div_of_pos hq]
    _ = ENNReal.ofReal (4 * B / t ^ 2) * X := by
        congr 1
        have ht_ne : t ≠ 0 := by linarith only [ht]
        field_simp [ht_ne]
        norm_num


-- @@ L57-57 verbatim
end CKN.Foundation.Measure
