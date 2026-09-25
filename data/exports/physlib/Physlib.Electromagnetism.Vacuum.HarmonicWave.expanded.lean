/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Vacuum.IsPlaneWave

-- @@ L9-54 verbatim
/-!

# Harmonic Wave in Vacuum

## i. Overview

In this module we define the electromagnetic potential for a monochromatic harmonic wave
travelling in the x-direction in free space, and prove various properties about it,
including that it satisfies Maxwell's equations in free space, that it is a plane wave.

We work here in a general dimension `d` so we use the magnetic field is the
form of a matrix rather than a vector.

## ii. Key results

- `harmonicWaveX` : Definition of the electromagnetic
  potential for a harmonic wave travelling in the x-direction.
- `harmonicWaveX_isExtrema` : The harmonic wave satisfies Maxwell's equations in free space.
- `harmonicWaveX_isPlaneWave` : The harmonic wave is a plane wave.
- `harmonicWaveX_polarization_ellipse` : The polarization ellipse equation for the harmonic wave.

## iii. Table of contents

- A. The electromagnetic potential for a harmonic wave
  - A.1. Differentiability of the electromagnetic potential
  - A.2. Smoothness of the electromagnetic potential
- B. The scalar potential
- C. The vector potential
  - C.1. Components of the vector potential
  - C.2. Space derivatives of the vector potential
- D. The electric field
  - D.1. Components of the electric field
  - D.2. Spatial derivatives of the electric field
  - D.3. Time derivatives of the electric field
  - D.4. Divergence of the electric field
- E. The magnetic field matrix for a harmonic wave
  - E.1. Components of the magnetic field matrix
  - E.2. Space derivatives of the magnetic field matrix
- F. Maxwell's equations for a harmonic wave
- G. The harmonic wave is a plane wave
- H. Polarization ellipse of the harmonic wave

## iv. References

* None.
-/


-- @@ L56-56 verbatim
@[expose] public section

-- @@ L57-57 verbatim
namespace Electromagnetism


-- @@ L59-59 verbatim
open Space Module

-- @@ L60-60 verbatim
open Time

-- @@ L61-61 verbatim
open ClassicalMechanics


-- @@ L63-63 verbatim
variable (OM : OpticalMedium)

-- @@ L64-64 verbatim
open Matrix

-- @@ L65-65 verbatim
open Real


-- @@ L67-67 verbatim
namespace ElectromagneticPotential

-- @@ L68-68 verbatim
open InnerProductSpace


-- @@ L70-74 verbatim
/-!

## A. The electromagnetic potential for a harmonic wave

-/


-- @@ L76-85 verbatim
/-- The electromagnetic potential for a Harmonic wave travelling in the `x`-direction
  with wave number `k`. -/
noncomputable def harmonicWaveX (𝓕 : FreeSpace) (k : ℝ) (E₀ : Fin d → ℝ)
  (φ : Fin d → ℝ) : ElectromagneticPotential d.succ where
  val := fun x μ =>
  match μ with
  | Sum.inl 0 => 0
  | Sum.inr 0 => 0
  | Sum.inr ⟨Nat.succ i, h⟩ => -E₀ ⟨i, Nat.succ_lt_succ_iff.mp h⟩ * 1 / (𝓕.c * k) *
      Real.sin (k * (𝓕.c * x.time 𝓕.c - x.space 0) + φ ⟨i, Nat.succ_lt_succ_iff.mp h⟩)


-- @@ L87-91 verbatim
@[simp]
lemma harmonicWaveX_inl_zero {d} (𝓕 : FreeSpace) (k : ℝ) (E₀ : Fin d → ℝ) (φ : Fin d → ℝ)
    (x : SpaceTime d.succ) :
    harmonicWaveX 𝓕 k E₀ φ x (Sum.inl 0) = 0 := by
  simp [harmonicWaveX]


-- @@ L93-98 verbatim
@[simp]
lemma harmonicWaveX_inr_zero {d} (𝓕 : FreeSpace) (k : ℝ) (E₀ : Fin d → ℝ) (φ : Fin d → ℝ)
    (x : SpaceTime d.succ) :
    harmonicWaveX 𝓕 k E₀ φ x (Sum.inr 0) = 0 := by
  simp [harmonicWaveX]
  rfl


-- @@ L100-104 verbatim
/-!

### A.1. Differentiability of the electromagnetic potential

-/


-- @@ L106-116 verbatim
lemma harmonicWaveX_differentiable {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    Differentiable ℝ (harmonicWaveX 𝓕 k E₀ φ) := by
  rw [← Lorentz.Vector.differentiable_apply]
  intro μ
  match μ with
  | Sum.inl 0 => simp
  | Sum.inr ⟨0, h⟩ => simp
  | Sum.inr ⟨Nat.succ i, h⟩ =>
    simp [harmonicWaveX]
    fun_prop


-- @@ L118-122 verbatim
/-!

### A.2. Smoothness of the electromagnetic potential

-/


-- @@ L124-134 verbatim
lemma harmonicWaveX_contDiff {d} (n : WithTop ℕ∞) (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    ContDiff ℝ n (harmonicWaveX 𝓕 k E₀ φ) := by
  rw [← Lorentz.Vector.contDiff_apply]
  intro μ
  match μ with
  | Sum.inl 0 => simp [harmonicWaveX]; fun_prop
  | Sum.inr ⟨0, h⟩ => simp [harmonicWaveX]; fun_prop
  | Sum.inr ⟨Nat.succ i, h⟩ =>
    simp [harmonicWaveX]
    fun_prop


-- @@ L136-142 verbatim
/-!

## B. The scalar potential

The scalar potential of the harmonic wave is zero.

-/


-- @@ L144-150 verbatim
@[simp]
lemma harmonicWaveX_scalarPotential_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    (harmonicWaveX 𝓕 k E₀ φ).scalarPotential 𝓕.c = 0 := by
  ext x
  simp [harmonicWaveX, scalarPotential]
  rfl


-- @@ L152-156 verbatim
/-!

## C. The vector potential

-/


-- @@ L158-162 verbatim
/-!

### C.1. Components of the vector potential

-/


-- @@ L164-169 verbatim
@[simp]
lemma harmonicWaveX_vectorPotential_zero_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x 0 = 0 := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice]
  rfl


-- @@ L171-177 verbatim
lemma harmonicWaveX_vectorPotential_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x i.succ =
    - E₀ i * 1 / (𝓕.c * k) * Real.sin (k * (t.val * 𝓕.c - x 0) + φ i) := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice, Fin.succ]
  left
  ring_nf


-- @@ L179-186 verbatim
lemma harmonicWaveX_vectorPotential_succ' {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : ℕ)
    (hi : i.succ < d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).vectorPotential 𝓕.c t x ⟨i.succ, hi⟩ =
    - E₀ ⟨i, by grind⟩ * 1 / (𝓕.c * k) * Real.sin (k * (t.val * 𝓕.c - x 0) + φ ⟨i, by grind⟩) := by
  simp [harmonicWaveX, vectorPotential, SpaceTime.timeSlice]
  left
  ring_nf


-- @@ L188-192 verbatim
/-!

### C.2. Space derivatives of the vector potential

-/


-- @@ L194-194 verbatim
open Space

-- @@ L195-213 verbatim
@[simp]
lemma harmonicWaveX_vectorPotential_space_deriv_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (j : Fin d)
    (i : Fin d.succ) :
    Space.deriv j.succ (fun x => vectorPotential 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i) x
    = 0 := by
  match i with
  | 0 => simp
  | ⟨Nat.succ i, hi⟩ =>
    have transverse_deriv_eq_zero : ∀ (g : ℝ → ℝ), Differentiable ℝ g →
        Space.deriv j.succ (fun y => g (y 0)) x = 0 := by
      intro g hg
      rw [Space.deriv_eq, show (fun y : Space d.succ => g (y 0)) = g ∘ (fun y => y 0) from rfl,
        fderiv_comp _ hg.differentiableAt (by fun_prop)]
      simp [← Space.deriv_eq, Space.deriv_component, Fin.succ_ne_zero]
    simp only [harmonicWaveX_vectorPotential_succ', mul_one]
    exact transverse_deriv_eq_zero
      (fun u => -E₀ ⟨i, by grind⟩ / (𝓕.c.val * k) *
        sin (k * (t.val * 𝓕.c.val - u) + φ ⟨i, by grind⟩)) (by fun_prop)


-- @@ L215-215 verbatim
open Space

-- @@ L216-231 verbatim
@[simp]
lemma harmonicWaveX_vectorPotential_succ_space_deriv_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    Space.deriv 0 (fun x => vectorPotential 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i.succ) x
    = E₀ i / 𝓕.c.val * Real.cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  simp [harmonicWaveX_vectorPotential_succ]
  rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sin (by fun_prop)]
  simp only [fderiv_add_const, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (by fun_prop), fderiv_const_sub]
  simp only [smul_neg, _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_neg]
  rw [← Space.deriv_eq_fderiv_basis, Space.deriv_component]
  simp only [↓reduceIte, mul_one]
  field_simp


-- @@ L233-237 verbatim
/-!

## D. The electric field

-/


-- @@ L239-243 verbatim
/-!

### D.1. Components of the electric field

-/

-- @@ L244-250 verbatim
lemma harmonicWaveX_electricField_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x 0 = 0 := by
  simp [ElectromagneticPotential.electricField]
  rw [← Time.deriv_euclid]
  simp only [harmonicWaveX_vectorPotential_zero_eq_zero, Time.deriv_const]
  exact vectorPotential_differentiable_time _ (harmonicWaveX_differentiable 𝓕 k E₀ φ) x


-- @@ L252-266 verbatim
lemma harmonicWaveX_electricField_succ {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ =
    E₀ i * Real.cos (k * 𝓕.c * t.val - k * x 0 + φ i) := by
  simp [ElectromagneticPotential.electricField]
  rw [← Time.deriv_euclid]
  simp [harmonicWaveX_vectorPotential_succ]
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sin (by fun_prop), fderiv_add_const, fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_sub_const, fderiv_mul_const (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  field_simp
  exact vectorPotential_differentiable_time _ (harmonicWaveX_differentiable 𝓕 k E₀ φ) x


-- @@ L268-272 verbatim
/-!

### D.2. Spatial derivatives of the electric field

-/


-- @@ L274-292 verbatim
lemma harmonicWaveX_electricField_space_deriv_same {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d.succ) :
    Space.deriv i (fun x => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i) x
    = 0 := by
  match i with
  | 0 => simp [harmonicWaveX_electricField_zero]
  | ⟨Nat.succ i, hi⟩ =>
    have transverse_deriv_cos_eq_zero : ∀ (C a k b : ℝ) (l : Fin d) (y : Space d.succ),
        Space.deriv l.succ (fun x => C * Real.cos (a - k * x 0 + b)) y = 0 := by
      intro C a k b l y
      rw [Space.deriv_eq, show (fun x : Space d.succ => C * Real.cos (a - k * x 0 + b))
          = (fun u => C * Real.cos (a - k * u + b)) ∘ (fun x => x 0) from rfl,
        fderiv_comp _ (by fun_prop) (by fun_prop)]
      simp [← Space.deriv_eq, Space.deriv_component, Fin.succ_ne_zero]
    rw [← Fin.succ_mk _ _ (by grind)]
    conv_lhs =>
      enter [2, x]
      rw [harmonicWaveX_electricField_succ _ _ hk]
    apply transverse_deriv_cos_eq_zero


-- @@ L294-298 verbatim
/-!

### D.3. Time derivatives of the electric field

-/


-- @@ L300-315 verbatim
lemma harmonicWaveX_electricField_succ_time_deriv {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (i : Fin d) :
    Time.deriv (fun t => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x i.succ) t
    = - k * 𝓕.c * E₀ i * Real.sin (k * 𝓕.c * t.val - k * x 0 + φ i) := by
  conv_lhs =>
    enter [1, t]
    rw [harmonicWaveX_electricField_succ _ _ hk]
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop)]
  simp only [Nat.succ_eq_add_one, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    neg_mul]
  rw [fderiv_cos (by fun_prop)]
  simp only [fderiv_add_const, neg_smul, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_neg, neg_inj]
  rw [fderiv_sub_const, fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, Time.fderiv_val, smul_eq_mul, mul_one]
  ring


-- @@ L317-321 verbatim
/-!

### D.4. Divergence of the electric field

-/


-- @@ L323-329 verbatim
@[simp]
lemma harmonicWaveX_div_electricField_eq_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) :
    Space.div (fun x => electricField 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x) x = 0 := by
  simp [Space.div]
  exact Finset.sum_eq_zero fun i _ =>
    harmonicWaveX_electricField_space_deriv_same 𝓕 k hk E₀ φ t x i


-- @@ L331-334 verbatim
/-!

## E. The magnetic field matrix for a harmonic wave
-/


-- @@ L336-340 verbatim
/-!

### E.1. Components of the magnetic field matrix

-/


-- @@ L342-348 verbatim
@[simp]
lemma harmonicWaveX_magneticFieldMatrix_succ_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i j : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (i.succ, j.succ) = 0 := by
  rw [magneticFieldMatrix_eq_vectorPotential _ (harmonicWaveX_differentiable 𝓕 k E₀ φ)]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_space_deriv_succ, sub_self]


-- @@ L350-361 verbatim
lemma harmonicWaveX_magneticFieldMatrix_zero_succ {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (0, i.succ) =
    (- E₀ i / 𝓕.c.val) * cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  rw [magneticFieldMatrix_eq_vectorPotential _ (harmonicWaveX_differentiable 𝓕 k E₀ φ)]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_zero_eq_zero, Space.deriv_const,
    zero_sub]
  rw [harmonicWaveX_vectorPotential_succ_space_deriv_zero]
  simp only [Nat.succ_eq_add_one]
  ring
  exact hk


-- @@ L363-372 verbatim
lemma harmonicWaveX_magneticFieldMatrix_succ_zero {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    (harmonicWaveX 𝓕 k E₀ φ).magneticFieldMatrix 𝓕.c t x (i.succ, 0) =
    (E₀ i / 𝓕.c.val) * cos (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  rw [magneticFieldMatrix_eq_vectorPotential _ (harmonicWaveX_differentiable 𝓕 k E₀ φ)]
  simp only [Nat.succ_eq_add_one, harmonicWaveX_vectorPotential_zero_eq_zero, Space.deriv_const,
    sub_zero]
  rw [harmonicWaveX_vectorPotential_succ_space_deriv_zero]
  exact hk


-- @@ L374-378 verbatim
/-!

### E.2. Space derivatives of the magnetic field matrix

-/


-- @@ L380-413 verbatim
lemma harmonicWaveX_magneticFieldMatrix_space_deriv_succ {d} (𝓕 : FreeSpace) (k : ℝ)
    (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i j : Fin d.succ) (l : Fin d) :
    Space.deriv l.succ (fun x => magneticFieldMatrix 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x (i, j)) x
    = 0 := by
  have transverse_deriv_cos_eq_zero : ∀ (C a k b : ℝ) (l : Fin d) (y : Space d.succ),
      Space.deriv l.succ (fun x => C * Real.cos (a - k * x 0 + b)) y = 0 := by
    intro C a k b l y
    rw [Space.deriv_eq, show (fun x : Space d.succ => C * Real.cos (a - k * x 0 + b))
        = (fun u => C * Real.cos (a - k * u + b)) ∘ (fun x => x 0) from rfl,
      fderiv_comp _ (by fun_prop) (by fun_prop)]
    simp [← Space.deriv_eq, Space.deriv_component, Fin.succ_ne_zero]
  match i, j with
  | 0, 0 => simp
  | ⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩ =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_succ _ _]
    simp
  | 0, ⟨Nat.succ j, hj⟩ =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
    apply transverse_deriv_cos_eq_zero
  | ⟨Nat.succ j, hj⟩, 0 =>
    conv_lhs =>
      enter [2, x]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_zero _ k hk]
    apply transverse_deriv_cos_eq_zero


-- @@ L415-436 verbatim
lemma harmonicWaveX_magneticFieldMatrix_zero_succ_space_deriv_zero {d} (𝓕 : FreeSpace) (k : ℝ)
    (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ)
    (i : Fin d) :
    Space.deriv 0 (fun x => magneticFieldMatrix 𝓕.c (harmonicWaveX 𝓕 k E₀ φ) t x (0, i.succ)) x
    = -E₀ i * k / 𝓕.c.val * sin (𝓕.c.val * k * t.val - k * x 0 + φ i) := by
  conv_lhs =>
    enter [2, x]
    rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
  rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]
  simp only [Nat.succ_eq_add_one, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    neg_mul]
  rw [fderiv_cos (by fun_prop)]
  simp only [fderiv_add_const, neg_smul, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_neg]
  rw [fderiv_const_sub]
  simp only [_root_.neg_apply, mul_neg, neg_neg]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq, Space.deriv_component]
  simp only [↓reduceIte, mul_one]
  ring


-- @@ L438-442 verbatim
/-!

## F. Maxwell's equations for a harmonic wave

-/


-- @@ L444-478 verbatim
lemma harmonicWaveX_isExtrema {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    IsExtrema 𝓕 (harmonicWaveX 𝓕 k E₀ φ) 0 := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix]
  intro t x
  apply And.intro
  /- Gauss's law -/
  · simp
    rw [harmonicWaveX_div_electricField_eq_zero 𝓕 k hk E₀ φ t x]
  /- Ampère's law -/
  · intro i
    rw [Fin.sum_univ_succ]
    conv_rhs =>
      enter [1, 2, 2, i]
      rw [harmonicWaveX_magneticFieldMatrix_space_deriv_succ _ _ hk]
    simp
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp
      rw [← Time.deriv_euclid]
      conv_lhs =>
        enter [1, t]
        rw [harmonicWaveX_electricField_zero 𝓕 k E₀]
      simp only [Time.deriv_const]
      exact electricField_differentiable_time (harmonicWaveX_contDiff 2 𝓕 k E₀ φ) x
    rw [harmonicWaveX_magneticFieldMatrix_zero_succ_space_deriv_zero _ k hk]
    rw [← Time.deriv_euclid]
    rw [harmonicWaveX_electricField_succ_time_deriv _ _ hk]
    field_simp
    simp [𝓕.c_sq]
    field_simp
    tauto
    exact electricField_differentiable_time (harmonicWaveX_contDiff 2 𝓕 k E₀ φ) x
  · apply harmonicWaveX_contDiff
  · change ContDiff ℝ _ (fun _ => 0)
    fun_prop


-- @@ L480-484 verbatim
/-!

## G. The harmonic wave is a plane wave

-/


-- @@ L486-540 verbatim
lemma harmonicWaveX_isPlaneWave {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) :
    IsPlaneWave 𝓕 (harmonicWaveX 𝓕 k E₀ φ) ⟨Space.basis 0, by simp⟩ := by
  apply And.intro
  · use fun u => WithLp.toLp 2 fun i =>
      match i with
      | 0 => 0
      | ⟨Nat.succ i, h⟩ => E₀ ⟨i, by grind⟩ * cos (-k * u + φ ⟨i, by grind⟩)
    ext t x i
    match i with
    | 0 =>
      simp [harmonicWaveX_electricField_zero, planeWave]
      rfl
    | ⟨Nat.succ i, h⟩ =>
      simp only [Nat.succ_eq_add_one, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_electricField_succ _ _ hk]
      simp [planeWave]
      left
      ring_nf
  · use fun u ij =>
      match ij with
      | (0, 0) => 0
      | (0, ⟨Nat.succ j, hj⟩) =>
        (- E₀ ⟨j, by grind⟩ / 𝓕.c.val) * cos (-k * u + φ ⟨j, by grind⟩)
      | (⟨Nat.succ i, hi⟩, 0) =>
        (E₀ ⟨i, by grind⟩ / 𝓕.c.val) * cos (-k * u + φ ⟨i, by grind⟩)
      | (⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩) => 0
    intro t x
    ext ij
    match ij with
    | (0, 0) =>
      simp only [Nat.succ_eq_add_one, magneticFieldMatrix_diag_eq_zero, inner_basis, neg_mul]
      rfl
    | (⟨0, h0⟩, ⟨Nat.succ j, hj⟩) =>
      simp only [Nat.succ_eq_add_one, Fin.zero_eta, inner_basis, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_zero_succ _ k hk]
      simp only [Nat.succ_eq_add_one, mul_eq_mul_left_iff, div_eq_zero_iff, neg_eq_zero,
        SpeedOfLight.val_ne_zero, or_false]
      left
      ring_nf
    | (⟨Nat.succ i, hi⟩, ⟨0, h0⟩) =>
      simp only [Nat.succ_eq_add_one, Fin.zero_eta, inner_basis, neg_mul]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_zero _ k hk]
      simp only [Nat.succ_eq_add_one, mul_eq_mul_left_iff, div_eq_zero_iff,
        SpeedOfLight.val_ne_zero, or_false]
      left
      ring_nf
    | (⟨Nat.succ i, hi⟩, ⟨Nat.succ j, hj⟩) =>
      simp only [Nat.succ_eq_add_one]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [← Fin.succ_mk _ _ (by grind)]
      rw [harmonicWaveX_magneticFieldMatrix_succ_succ _ _]


-- @@ L542-546 verbatim
/-!

## H. Polarization ellipse of the harmonic wave

-/


-- @@ L548-593 verbatim
open Real in
lemma harmonicWaveX_polarization_ellipse {d} (𝓕 : FreeSpace) (k : ℝ) (hk : k ≠ 0)
    (E₀ : Fin d → ℝ) (φ : Fin d → ℝ) (t : Time) (x : Space d.succ) (hi : ∀ i, E₀ i ≠ 0) :
    2 * d * ∑ i : Fin d, ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i) ^ 2 -
    2 * ∑ i, ∑ j, ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i) *
      ((harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x j.succ / E₀ j) *
      Real.cos (φ j - φ i) =
    ∑ i, ∑ j, Real.sin (φ j - φ i) ^ 2 := by
  have h1 (i : Fin d) : (harmonicWaveX 𝓕 k E₀ φ).electricField 𝓕.c t x i.succ / E₀ i
    = Real.cos (k * 𝓕.c * t.val - k * x 0 + φ i) := by
    rw [harmonicWaveX_electricField_succ 𝓕 k hk E₀ φ t x i]
    field_simp [hi i]
  conv_lhs =>
    enter [1, 2, 2, i]
    rw [h1]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [h1, h1]
  let τ := k * 𝓕.c * t.val - k * x 0
  have hij (i j : Fin d) :
      cos (τ + φ i) ^ 2 + cos (τ + φ j) ^ 2
      - 2 * cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) = sin (φ j - φ i) ^ 2 := by
    simp only [cos_add, sin_sub, cos_sub]
    nlinarith [sin_sq_add_cos_sq τ, sin_sq_add_cos_sq (φ i), sin_sq_add_cos_sq (φ j)]
  symm
  calc _
    _ = ∑ (i : Fin d), ∑ (j : Fin d), (cos (τ + φ i) ^ 2 + cos (τ + φ j) ^ 2
        - 2 * cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i)) := by
      simp [← hij]
    _ = 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ j) ^ 2
        - 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) := by
      rw [two_mul]
      conv_rhs =>
        enter [1, 1]
        rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr
      funext i
      rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr
      funext j
      ring
    _ = 2 * d * ∑ (j : Fin d), cos (τ + φ j) ^ 2
        - 2 * ∑ (i : Fin d), ∑ (j : Fin d), cos (τ + φ i) * cos (τ + φ j) * cos (φ j - φ i) := by
      rw [Finset.sum_const, Finset.card_fin]
      ring


-- @@ L595-595 verbatim
end ElectromagneticPotential


-- @@ L597-597 verbatim
end Electromagnetism
