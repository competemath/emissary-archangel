/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.Space.Integrals.NormPow

-- @@ L10-33 verbatim
/-!

# Regularized powers of the norm on space

## i. Overview

This file contains basic API for regularized powers of the norm on `Space d`, namely
`x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)`.

## ii. Key results

- `normRegularizedPow` : The regularized norm power `x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)`.
- `normRegularizedPow_pos` : Positivity for nonzero regularization parameter.
- `normRegularizedPow_hasTemperateGrowth` : Temperate growth of regularized norm powers.
- `normRegularizedPow_measurable` : Measurability of regularized norm powers.

## iii. Table of contents

- A. Regularized powers of the norm

## iv. References

* None.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
namespace Space


-- @@ L41-41 verbatim
open MeasureTheory Function


-- @@ L43-47 verbatim
/-!

## A. Regularized powers of the norm

-/


-- @@ L49-51 verbatim
/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)`. -/
def normRegularizedPow (d : ℕ) (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)


-- @@ L53-54 verbatim
lemma normRegularizedPow_eq (d : ℕ) (ε s : ℝ) :
    normRegularizedPow d ε s = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) := rfl


-- @@ L56-58 verbatim
/-- For a nonzero regularization parameter, `‖x‖² + ε²` is positive. -/
lemma norm_sq_add_unit_sq_pos {d : ℕ} (ε : ℝˣ) (x : Space d) : 0 < ‖x‖ ^ 2 + ε ^ 2 :=
    Left.add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_iff.mpr <| Units.ne_zero ε)


-- @@ L60-63 verbatim
/-- The regularized norm power is positive for nonzero regularization parameter. -/
lemma normRegularizedPow_pos (d : ℕ) (ε : ℝˣ) (s : ℝ) (x : Space d) :
    0 < normRegularizedPow d ε s x :=
  Real.rpow_pos_of_pos (norm_sq_add_unit_sq_pos ε x) (s / 2)


-- @@ L65-77 verbatim
/-- The regularized norm power has temperate growth. -/
lemma normRegularizedPow_hasTemperateGrowth (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    HasTemperateGrowth (normRegularizedPow d ε s) := by
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε.1⁻¹ • x
  have h123 : normRegularizedPow d ε s = f1 ∘ f2 ∘ f3 := by
    ext
    simp only [normRegularizedPow, f1, f2, f3, comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg ↑ε) (add_nonneg (zero_le_one' _) (sq_nonneg _))]
    simp [mul_add, mul_pow, add_comm]
  rw [h123]
  fun_prop


-- @@ L79-83 verbatim
@[fun_prop]
lemma normRegularizedPow_measurable (d : ℕ) (ε s : ℝ) :
    Measurable (normRegularizedPow d ε s) := by
  rw [normRegularizedPow_eq]
  fun_prop


-- @@ L85-85 verbatim
end Space
