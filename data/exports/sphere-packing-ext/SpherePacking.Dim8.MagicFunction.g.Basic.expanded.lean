/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

module
public import SpherePacking.Dim8.MagicFunction.a.Schwartz.Basic
public import SpherePacking.Dim8.MagicFunction.b.Schwartz.Basic
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.FourierPermutations
import SpherePacking.Dim8.MagicFunction.a.SpecialValues
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.FourierPermutations
import SpherePacking.Dim8.MagicFunction.b.SpecialValues
import SpherePacking.Tactic.NormNumI



-- @@ L17-21 verbatim
/-!
# Viazovska's Magic Function (`g`)

Defines Viazovska's magic function `g` and its normalization at `0`.
-/


-- @@ L23-23 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L25-26 verbatim
open SchwartzMap Complex Real MagicFunction.FourierEigenfunctions MagicFunction.a.SpecialValues
  MagicFunction.b.SpecialValues


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-31 expanded
/-- The Magic Function, `g`. -/
@[expose]
public def g : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) :=
  ((π * I) / 8640) • a - (I / (240 * π)) • b


-- @@ L33-36 verbatim
/-- Normalization of `g` at the origin. -/
public theorem g_zero : g 0 = 1 := by
  simp [g, a_zero, b_zero, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1


-- @@ L38-44 expanded
/-- Normalization of the Fourier transform of `g` at the origin. -/
public theorem fourier_g_zero :
    FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 8)) ℂ) g 0 = 1 := by
  -- Use linearity + eigenfunction identities, then evaluate at `0`.
  
  simp only [g, map_sub, map_smul, MagicFunction.a.Fourier.eig_a, MagicFunction.b.Fourier.eig_b,
    sub_apply, smul_apply, smul_eq_mul]
  simp [a_zero, b_zero, sub_eq_add_neg, div_eq_mul_inv]
  field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast pi_ne_zero]; ring_nf; norm_num1


-- @@ L46-49 expanded
/-- The values `g 0` and `𝓕 g 0` agree. -/
public theorem g_zero_eq_fourier_g_zero :
    g 0 = FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 8)) ℂ) g 0 := by
  rw [g_zero, fourier_g_zero]


-- @@ L51-51 verbatim
end
