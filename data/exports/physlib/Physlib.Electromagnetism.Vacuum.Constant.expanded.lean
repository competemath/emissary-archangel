/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.IsExtrema

-- @@ L9-38 verbatim
/-!

# The constant electric and magnetic fields

## i. Overview

In this module we define the electromagnetic potential which gives rise to a
given constant electric and magnetic field matrix.

We will show that this electromagnetic potential is an extrema of the free-space
electromagnetic action.

## ii. Key results

## iii. Table of contents

- A. The definition of the potential
- B. Smoothness of the potential
- C. The scalar potential
- D. The vector potential
  - D.1. Time derivative of the vector potential
  - D.2. Space derivative of the vector potential
- E. The electric field
- F. The magnetic field
- G. Is extrema

## iv. References

* None.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
namespace Electromagnetism

-- @@ L43-43 verbatim
open Module realLorentzTensor

-- @@ L44-44 verbatim
open TensorSpecies

-- @@ L45-45 verbatim
open Tensor ContDiff


-- @@ L47-47 verbatim
namespace ElectromagneticPotential


-- @@ L49-49 verbatim
open TensorSpecies

-- @@ L50-50 verbatim
open Tensor

-- @@ L51-51 verbatim
open SpaceTime

-- @@ L52-52 verbatim
open TensorProduct

-- @@ L53-53 verbatim
open minkowskiMatrix

-- @@ L54-54 verbatim
open InnerProductSpace

-- @@ L55-55 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L56-56 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L58-65 verbatim
/-!

## A. The definition of the potential

The electromagnetic potential which gives rise to a constant electric field `E₀`
and a constant magnetic field matrix `B₀`.

-/

-- @@ L66-66 verbatim
open Matrix

-- @@ L67-67 verbatim
set_option linter.unusedVariables false

-- @@ L68-76 verbatim
/-- An electric potential which gives a given constant E-field and B-field. -/
@[nolint unusedArguments]
noncomputable def constantEB {d : ℕ} (c : SpeedOfLight)
    (E₀ : EuclideanSpace ℝ (Fin d)) (B₀ : Fin d × Fin d → ℝ)
    (B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)) : ElectromagneticPotential d where
  val := fun x μ =>
  match μ with
  | Sum.inl _ => - (1/c) * ⟪E₀, Space.basis.repr x.space⟫_ℝ
  | Sum.inr i => (1/2) * ∑ j, B₀ (i, j) * x.space j


-- @@ L78-84 verbatim
/-!

## B. Smoothness of the potential

The potential is smooth.

-/


-- @@ L86-109 verbatim
lemma constantEB_smooth {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    ContDiff ℝ ∞ (constantEB c E₀ B₀ B₀_antisymm) := by
  rw [← Lorentz.Vector.contDiff_apply]
  intro μ
  match μ with
  | Sum.inl _ =>
      simp [constantEB]
      apply ContDiff.neg
      apply ContDiff.mul
      · fun_prop
      apply ContDiff.inner
      · fun_prop
      · fun_prop
  | Sum.inr i =>
      simp [constantEB]
      apply ContDiff.mul
      · fun_prop
      · apply ContDiff.sum
        intro j _
        apply ContDiff.mul
        · fun_prop
        fun_prop


-- @@ L111-117 verbatim
/-!

## C. The scalar potential

The scalar potential of the electromagnetic potential is given by `-⟪E₀, x⟫`.

-/


-- @@ L119-126 verbatim
lemma constantEB_scalarPotential {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).scalarPotential c = fun _ x =>
      -⟪E₀, Space.basis.repr x⟫_ℝ := by
  ext t x
  simp [scalarPotential, timeSlice, constantEB, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]


-- @@ L128-134 verbatim
/-!

## D. The vector potential

The vector potential of the electromagnetic potential is `(1 / 2) * ∑ j, B₀ (i, j) * x j `.

-/


-- @@ L136-143 verbatim
lemma constantEB_vectorPotential {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).vectorPotential c = fun _ x => WithLp.toLp 2 fun i =>
      (1 / 2) * ∑ j, B₀ (i, j) * x j := by
  ext t x i
  simp [vectorPotential, timeSlice, constantEB, Equiv.coe_fn_mk,
    Function.curry_apply, Function.comp_apply]


-- @@ L145-149 verbatim
/-!

### D.1. Time derivative of the vector potential

-/

-- @@ L150-150 verbatim
open Time


-- @@ L152-158 verbatim
@[simp]
lemma constantEB_vectorPotential_time_deriv {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} (t : Time) (x : Space d) :
    ∂ₜ ((constantEB c E₀ B₀ B₀_antisymm).vectorPotential c · x) t = 0 := by
  rw [constantEB_vectorPotential]
  simp


-- @@ L160-164 verbatim
/-!

### D.2. Space derivative of the vector potential

-/


-- @@ L166-186 verbatim
lemma constantEB_vectorPotential_space_deriv {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} (t : Time) (x : Space d) (i j : Fin d) :
    Space.deriv i ((constantEB c E₀ B₀ B₀_antisymm).vectorPotential c t · j) x =
    (1 / 2) * B₀ (j, i) := by
  rw [constantEB_vectorPotential]
  rw [Space.deriv_eq]
  rw [fderiv_const_mul (by fun_prop)]
  rw [fderiv_fun_sum (by fun_prop)]
  simp only [one_div, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
  rw [Finset.sum_eq_single i]
  · rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq]
  · intro k _ hk
    rw [fderiv_const_mul (by fun_prop)]
    simp [← Space.deriv_eq]
    rw [Space.deriv_component_diff]
    simp only [or_true]
    exact id (Ne.symm hk)
  · simp


-- @@ L188-192 verbatim
/-!

## E. The electric field

-/


-- @@ L194-207 verbatim
@[simp]
lemma constantEB_electricField {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).electricField c = fun _ _ => E₀ := by
  funext t x
  rw [electricField_eq]
  simp [constantEB_scalarPotential]
  erw [Space.grad_neg]
  conv_lhs =>
    enter [1, 1,1, x]
    rw [real_inner_comm, Space.basis_repr_inner_eq, real_inner_comm]
  rw [Space.grad_inner_right]
  simp


-- @@ L209-213 verbatim
/-!

## F. The magnetic field

-/


-- @@ L215-230 verbatim
@[simp]
lemma constantEB_magneticFieldMatrix {c : SpeedOfLight}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    (constantEB c E₀ B₀ B₀_antisymm).magneticFieldMatrix c = fun _ _ => B₀ := by
  funext t x
  funext i
  match i with
  | (i, j) =>
  rw [magneticFieldMatrix_eq_vectorPotential]
  rw [constantEB_vectorPotential_space_deriv, constantEB_vectorPotential_space_deriv]
  conv_lhs =>
    enter [2]
    rw [B₀_antisymm]
  ring
  apply constantEB_smooth.differentiable (by simp)


-- @@ L232-236 verbatim
/-!

## G. Is extrema

-/


-- @@ L238-246 verbatim
lemma constantEB_isExtrema {𝓕 : FreeSpace}
    {E₀ : EuclideanSpace ℝ (Fin d)} {B₀ : Fin d × Fin d → ℝ}
    {B₀_antisymm : ∀ i j, B₀ (i, j) = - B₀ (j, i)} :
    IsExtrema 𝓕 (constantEB 𝓕.c E₀ B₀ B₀_antisymm) 0 := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix]
  · intro t x
    simp
  · exact constantEB_smooth
  · exact contDiff_zero_fun


-- @@ L248-248 verbatim
end ElectromagneticPotential


-- @@ L250-250 verbatim
end Electromagnetism
