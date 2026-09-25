/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import SpherePacking.MagicFunction.a.Eigenfunction
public import SpherePacking.MagicFunction.a.SpecialValues
public import SpherePacking.MagicFunction.b.Eigenfunction
public import SpherePacking.MagicFunction.b.SpecialValues
public import SpherePacking.Tactic.NormNumI


-- @@ L16-19 verbatim
/-! # Viazovska's Magic Function

In this file, we define Viazovska's magic funtction `g`.
-/


-- @@ L21-21 verbatim
@[expose] public section

-- @@ L22-22 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L24-25 verbatim
open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.Fourier
  MagicFunction.b.Fourier MagicFunction.a.SpecialValues MagicFunction.b.SpecialValues


-- @@ L27-31 expanded
/-- The Magic Function, `g`. -/
noncomputable def g : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  ((π * I) / 8640) • a + (I / (240 * π)) • b


-- @@ L33-33 verbatim
section Zero


-- @@ L35-41 verbatim
theorem g_zero : g 0 = 1 := by
  simp only [g, add_apply, smul_apply, a_zero, neg_mul, smul_eq_mul, b_zero, mul_zero, add_zero]
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero


-- @@ L43-51 verbatim
theorem fourier_g_zero : (FourierTransform.fourierCLE ℂ _) g 0 = 1 := by
  simp only [g, map_add, map_smul, eig_a, eig_b, add_apply, smul_apply, a_zero, smul_eq_mul]
  have : (-b) 0 = -(b 0) := rfl
  ring_nf
  simp only [I_sq, mul_neg, mul_one, neg_mul, neg_neg, this, b_zero, neg_zero, mul_zero, one_div,
    zero_mul, add_zero]
  apply Complex.mul_inv_cancel
  norm_cast
  exact pi_ne_zero


-- @@ L53-54 verbatim
theorem g_zero_eq_fourier_g_zero : g 0 = (FourierTransform.fourierCLE ℂ _) g 0 := by
  rw [g_zero, fourier_g_zero]


-- @@ L56-56 verbatim
end Zero
