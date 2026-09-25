/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
public import Physlib.Electromagnetism.Dynamics.IsExtrema

-- @@ L10-55 verbatim
/-!

# Electromagnetic wave equation

## i. Overview

In this module we define a proposition `IsPlaneWave` on electromagnetic potentials
which is true if the potential corresponds to a plane wave.
From this we derive various properties of plane waves including
the orthogonality of the electric field, magnetic field and direction of propagation,
in general dimensions.

## ii. Key results

- `IsPlaneWave` : The proposition defining plane waves.
- `IsPlaneWave.electricFunction` : The electric function corresponding to a plane wave.
- `IsPlaneWave.magneticFunction` : The magnetic function corresponding to a plane wave.
- `IsPlaneWave.magneticFieldMatrix_eq_propogator_cross_electricField` :
    The magnetic field expressed in terms of the electric field and direction of propagation.
- `IsPlaneWave.electricField_eq_propogator_cross_magneticFieldMatrix` :
    The electric field expressed in terms of the magnetic field and direction of propagation.

## iii. Table of contents

- A. The property of being a plane wave
  - A.1. The electric and magnetic functions from a plane wave
    - A.1.1. Electric function and magnetic function in terms of E and B fields
    - A.1.2. Uniqueness of the electric function
    - A.1.3. Uniqueness of the magnetic function
  - A.2. Differentiability conditions
  - A.3. Time derivative of electric and magnetic fields of a plane wave
  - A.4. Space derivative of electric and magnetic fields of a plane wave
  - A.5. Space derivative in terms of time derivative
- B. The magnetic field in terms of the electric field
  - B.1. Time derivative of the magnetic field in terms of electric field
  - B.2. Space derivative of the magnetic field in terms of electric field
  - B.3. Magnetic field equal propogator cross electric field up to constant
- C. The electric field in terms of the magnetic field
  - C.1. The time derivative of the electric field in terms of magnetic field
  - C.2. The space derivative of the electric field in terms of magnetic field
  - C.3. Electric field equal propogator cross magnetic field up to constant

## iv. References

* None.
-/


-- @@ L57-57 verbatim
@[expose] public section


-- @@ L59-59 verbatim
namespace Electromagnetism


-- @@ L61-61 verbatim
open Space Module

-- @@ L62-62 verbatim
open Time

-- @@ L63-63 verbatim
open ClassicalMechanics


-- @@ L65-65 verbatim
open Matrix

-- @@ L66-69 verbatim
/-!

## A. The property of being a plane wave
-/

-- @@ L70-70 verbatim
namespace ElectromagneticPotential

-- @@ L71-71 verbatim
open InnerProductSpace


-- @@ L73-79 verbatim
/-- The proposition on a electromagnetic potential which is true if
  it corresponds to a plane wave. -/
def IsPlaneWave {d : ℕ} (𝓕 : FreeSpace)
    (A : ElectromagneticPotential d) (s : Direction d) : Prop :=
  (∃ E₀, A.electricField 𝓕.c = planeWave E₀ 𝓕.c s) ∧
  (∃ (B₀ : ℝ → Fin d × Fin d → ℝ), ∀ t x, A.magneticFieldMatrix 𝓕.c t x =
    B₀ (⟪x, s.unit⟫_ℝ - 𝓕.c * t))

-- @@ L80-80 verbatim
namespace IsPlaneWave

-- @@ L81-84 verbatim
/-!

### A.1. The electric and magnetic functions from a plane wave
-/


-- @@ L86-91 verbatim
/-- The corresponding electric field function from `ℝ` to `EuclideanSpace ℝ (Fin d)`
  of a plane wave. -/
noncomputable def electricFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (hA : IsPlaneWave 𝓕 A s) : ℝ → EuclideanSpace ℝ (Fin d) :=
  Classical.choose hA.1


-- @@ L93-98 verbatim
lemma electricField_eq_electricFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (t : Time) (x : Space d) :
    A.electricField 𝓕.c t x =
    P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c * t) :=
  congrFun (congrFun (Classical.choose_spec P.1) t) x


-- @@ L100-105 verbatim
/-- The corresponding magnetic field function from `ℝ` to
  `Fin d × Fin d → ℝ` of a plane wave. -/
noncomputable def magneticFunction {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (hA : IsPlaneWave 𝓕 A s) : ℝ → Fin d × Fin d → ℝ :=
  Classical.choose hA.2


-- @@ L107-112 verbatim
lemma magneticFieldMatrix_eq_magneticFunction {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (t : Time) (x : Space d) :
    A.magneticFieldMatrix 𝓕.c t x =
    P.magneticFunction (⟪x, s.unit⟫_ℝ - 𝓕.c * t) :=
  Classical.choose_spec P.2 t x


-- @@ L114-118 verbatim
/-!

#### A.1.1. Electric function and magnetic function in terms of E and B fields

-/


-- @@ L120-128 verbatim
lemma electricFunction_eq_electricField {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) :
    P.electricFunction = fun u =>
    A.electricField 𝓕.c ⟨(- u)/𝓕.c.1⟩ (0 : Space d) := by
  funext u
  rw [P.electricField_eq_electricFunction, inner_zero_left, zero_sub]
  congr 1
  field_simp


-- @@ L130-138 verbatim
lemma magneticFunction_eq_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) :
    P.magneticFunction = fun u =>
    A.magneticFieldMatrix 𝓕.c ⟨(- u)/𝓕.c.1⟩ (0 : Space d) := by
  funext u
  rw [P.magneticFieldMatrix_eq_magneticFunction, inner_zero_left, zero_sub]
  congr 1
  field_simp


-- @@ L140-144 verbatim
/-!

#### A.1.2. Uniqueness of the electric function

-/


-- @@ L146-154 verbatim
lemma electricFunction_unique {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s) (E1 : ℝ → EuclideanSpace ℝ (Fin d))
    (hE₁ : A.electricField 𝓕.c = planeWave E1 𝓕.c s) :
    E1 = P.electricFunction := by
  funext x
  obtain ⟨t, rfl⟩ : ∃ t, x = ⟪0, s.unit⟫_ℝ - 𝓕.c * t := by use (- x/𝓕.c); field_simp; simp
  rw [← P.electricField_eq_electricFunction, hE₁]
  rfl


-- @@ L156-160 verbatim
/-!

#### A.1.3. Uniqueness of the magnetic function

-/


-- @@ L162-171 verbatim
lemma magneticFunction_unique {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d}
    (P : IsPlaneWave 𝓕 A s)
    (B1 : ℝ → Fin d × Fin d → ℝ)
    (hB₁ : ∀ t x, A.magneticFieldMatrix 𝓕.c t x =
      B1 (⟪x, s.unit⟫_ℝ - 𝓕.c * t)) :
    B1 = P.magneticFunction := by
  funext x
  obtain ⟨t, rfl⟩ : ∃ t, x = ⟪0, s.unit⟫_ℝ - 𝓕.c * t := by use (- x/𝓕.c); field_simp; simp
  rw [← P.magneticFieldMatrix_eq_magneticFunction, hB₁]


-- @@ L173-177 verbatim
/-!

### A.2. Differentiability conditions

-/


-- @@ L179-189 verbatim
lemma electricFunction_differentiable {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ P.electricFunction := by
  rw [electricFunction_eq_electricField]
  change Differentiable ℝ (↿(electricField 𝓕.c A) ∘ fun u => ({ val := -u / 𝓕.c.val }, 0))
  apply (electricField_differentiable hA).comp
  refine Differentiable.prodMk ?_ ?_
  · change Differentiable ℝ (Time.toRealCLE.symm ∘ fun u => -u / 𝓕.c.val)
    fun_prop
  · fun_prop


-- @@ L191-204 verbatim
lemma magneticFunction_differentiable {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (ij : Fin d × Fin d) :
    Differentiable ℝ (fun u => P.magneticFunction u ij) := by
  rw [magneticFunction_eq_magneticFieldMatrix]
  simp only
  change Differentiable ℝ (↿(fun t x => A.magneticFieldMatrix 𝓕.c t x ij) ∘
    fun u => ({ val := -u / 𝓕.c.val }, 0))
  apply (magneticFieldMatrix_differentiable A hA ij).comp
  refine Differentiable.prodMk ?_ ?_
  · change Differentiable ℝ (Time.toRealCLE.symm ∘ fun u => -u / 𝓕.c.val)
    fun_prop
  · fun_prop


-- @@ L206-210 verbatim
/-!

### A.3. Time derivative of electric and magnetic fields of a plane wave

-/


-- @@ L212-221 verbatim
lemma electricField_time_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) :
    ∂ₜ (A.electricField 𝓕.c · x) t = - 𝓕.c.val •
    fderiv ℝ P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  have h : A.electricField 𝓕.c = planeWave P.electricFunction 𝓕.c.val s :=
    Classical.choose_spec P.1
  rw [h, planeWave_time_deriv (P.electricFunction_differentiable hA)]
  simp [planeWave_eq]


-- @@ L223-237 verbatim
lemma magneticFieldMatrix_time_deriv {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time)
    (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t = - 𝓕.c.val •
    fderiv ℝ (fun u => P.magneticFunction u (i, j)) (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 := by
  conv_lhs =>
    enter [1, t]
    rw [P.magneticFieldMatrix_eq_magneticFunction]
  rw [Time.deriv_eq]
  change fderiv ℝ ((fun u => P.magneticFunction u (i, j)) ∘
    fun t => ⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) t 1 = _
  rw [fderiv_comp _ (magneticFunction_differentiable P hA (i, j)).differentiableAt (by fun_prop),
    fderiv_fun_sub (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp [Time.fderiv_val]


-- @@ L239-243 verbatim
/-!

### A.4. Space derivative of electric and magnetic fields of a plane wave

-/


-- @@ L245-255 expanded
lemma electricField_space_deriv {d : ℕ} {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d)
    (i : Fin d) :
    (deriv i) (A.electricField 𝓕.c t ·) x =
      s.unit i • fderiv ℝ P.electricFunction (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 :=
  by
  have h : A.electricField 𝓕.c = planeWave P.electricFunction 𝓕.c.val s := Classical.choose_spec P.1
  rw [h]
  simp only [planeWave_space_deriv (P.electricFunction_differentiable hA)]
  simp [planeWave_eq]


-- @@ L257-275 expanded
lemma magneticFieldMatrix_space_deriv {d : ℕ} {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d)
    (i j : Fin d) (k : Fin d) :
    (deriv k) (A.magneticFieldMatrix 𝓕.c t · (i, j)) x =
      s.unit k •
        fderiv ℝ (fun u => P.magneticFunction u (i, j)) (⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) 1 :=
  by
  conv_lhs =>
    enter [2, t]
    rw [P.magneticFieldMatrix_eq_magneticFunction]
  rw [Space.deriv_eq_fderiv_basis]
  change
    fderiv ℝ ((fun u => P.magneticFunction u (i, j)) ∘ fun x => ⟪x, s.unit⟫_ℝ - 𝓕.c.val * t.val) x
        _ =
      _
  rw [fderiv_comp _ (magneticFunction_differentiable P hA (i, j)).differentiableAt (by fun_prop),
    fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul,
    one_mul, mul_eq_mul_right_iff, fderiv_fun_const, Pi.zero_apply, sub_zero]
  rw [← Space.deriv_eq_fderiv_basis]
  simp only [deriv_inner_left, true_or]


-- @@ L277-280 verbatim
/-!

### A.5. Space derivative in terms of time derivative
-/


-- @@ L282-294 expanded
lemma electricField_space_deriv_eq_time_deriv {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i : Fin d) (k : Fin d) :
    (deriv k) (A.electricField 𝓕.c t · i) x =
      -(s.unit k / 𝓕.c.val) • ∂ₜ (A.electricField 𝓕.c · x i) t :=
  by
  rw [Space.deriv_euclid, IsPlaneWave.electricField_space_deriv P hA t x k, Time.deriv_euclid,
    IsPlaneWave.electricField_time_deriv P hA t x]
  simp only [fderiv_eq_smul_deriv, one_smul, PiLp.smul_apply, smul_eq_mul, neg_mul, mul_neg,
    neg_neg]
  field_simp
  · exact electricField_differentiable_time hA x
  · exact electricField_differentiable_space hA t


-- @@ L296-305 expanded
lemma magneticFieldMatrix_space_deriv_eq_time_deriv {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i j : Fin d) (k : Fin d) :
    (deriv k) (A.magneticFieldMatrix 𝓕.c t · (i, j)) x =
      -(s.unit k / 𝓕.c.val) • ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t :=
  by
  rw [IsPlaneWave.magneticFieldMatrix_space_deriv P hA t x i j k,
    IsPlaneWave.magneticFieldMatrix_time_deriv P hA t x i j]
  simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, neg_mul, mul_neg, neg_neg]
  field_simp


-- @@ L307-311 verbatim
/-!

## B. The magnetic field in terms of the electric field

-/


-- @@ L313-317 verbatim
/-!

### B.1. Time derivative of the magnetic field in terms of electric field

-/

-- @@ L318-318 verbatim
open ContDiff


-- @@ L320-336 verbatim
lemma time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t =
    ∂ₜ (fun t => s.unit j / 𝓕.c * A.electricField 𝓕.c t x i
    - s.unit i / 𝓕.c * A.electricField 𝓕.c t x j) t := by
  have he : ∀ k, DifferentiableAt ℝ (fun t => A.electricField 𝓕.c t x k) t :=
    fun k => (electricField_apply_differentiable_time hA x k).differentiableAt
  rw [time_deriv_magneticFieldMatrix A hA, P.electricField_space_deriv_eq_time_deriv hA,
    P.electricField_space_deriv_eq_time_deriv hA]
  conv_rhs =>
    rw [Time.deriv_eq, fderiv_fun_sub ((he i).const_mul _) ((he j).const_mul _),
      fderiv_const_mul (he i), fderiv_const_mul (he j)]
  simp [← Time.deriv_eq]
  field_simp
  ring


-- @@ L338-342 verbatim
/-!

### B.2. Space derivative of the magnetic field in terms of electric field

-/


-- @@ L344-364 expanded
lemma space_deriv_magneticFieldMatrix_eq_electricField_mul_propogator {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A)
    (t : Time) (x : Space d) (i j k : Fin d) :
    (deriv k) (A.magneticFieldMatrix 𝓕.c t · (i, j)) x =
      (deriv k)
        (fun x =>
          s.unit j / 𝓕.c * A.electricField 𝓕.c t x i - s.unit i / 𝓕.c * A.electricField 𝓕.c t x j)
        x :=
  by
  rw [P.magneticFieldMatrix_space_deriv_eq_time_deriv hA,
    P.time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA,
    Space.deriv_eq_fderiv_basis, fderiv_fun_sub, fderiv_const_mul, fderiv_const_mul]
  simp [← Space.deriv_eq_fderiv_basis]
  rw [Time.deriv_eq, fderiv_fun_sub, fderiv_const_mul, fderiv_const_mul]
  simp [← Time.deriv_eq]
  rw [P.electricField_space_deriv_eq_time_deriv hA, P.electricField_space_deriv_eq_time_deriv hA]
  simp only [smul_eq_mul, neg_mul, mul_neg, sub_neg_eq_add]
  field_simp
  ring
  any_goals apply Differentiable.differentiableAt
  any_goals apply Differentiable.const_mul
  any_goals exact electricField_apply_differentiable_time hA x _
  any_goals exact electricField_apply_differentiable_space hA t _


-- @@ L366-370 verbatim
/-!

### B.3. Magnetic field equal propogator cross electric field up to constant

-/


-- @@ L372-391 verbatim
lemma magneticFieldMatrix_eq_propogator_cross_electricField {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ 2 A) (i j : Fin d) :
    ∃ C, ∀ t x, A.magneticFieldMatrix 𝓕.c t x (i, j) =
    1/ 𝓕.c * (s.unit j * A.electricField 𝓕.c t x i -
      s.unit i * A.electricField 𝓕.c t x j) + C := by
  apply Space.equal_up_to_const_of_deriv_eq
  · exact magneticFieldMatrix_differentiable A hA (i, j)
  · exact (((electricField_apply_differentiable hA).const_mul _).sub
      ((electricField_apply_differentiable hA).const_mul _)).const_mul _
  · intro t x
    rw [P.time_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA t x i j]
    congr
    funext t
    field_simp
  · intro t x k
    rw [P.space_deriv_magneticFieldMatrix_eq_electricField_mul_propogator hA t x i j]
    congr
    funext x
    field_simp


-- @@ L393-397 verbatim
/-!

## C. The electric field in terms of the magnetic field

-/

-- @@ L398-402 verbatim
/-!

### C.1. The time derivative of the electric field in terms of magnetic field

-/


-- @@ L404-455 verbatim
lemma time_deriv_electricField_eq_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (A.electricField 𝓕.c · x i) t =
    ∂ₜ (fun t => 𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) t := by
  have hBd : ∀ k, Differentiable ℝ (fun t => A.magneticFieldMatrix 𝓕.c t x (i, k)) :=
    fun k => magneticFieldMatrix_differentiable_time A (hA.of_le ENat.LEInfty.out) x (i, k)
  rw [Time.deriv_euclid, time_deriv_electricField_of_isExtrema hA 0 _ h t x i]
  simp only [one_div, _root_.mul_inv_rev, LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply,
    PiLp.zero_apply, mul_zero, sub_zero]
  conv_lhs =>
    enter [2, 2, i];
    rw [magneticFieldMatrix_space_deriv_eq_time_deriv P (hA.of_le ENat.LEInfty.out) t x i]
  rw [Time.deriv_eq, fderiv_const_mul]
  simp [← Time.deriv_eq]
  have h1 : ∂ₜ (fun t => ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) t
    = ∑ j, ∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j)) t * s.unit j := by
    rw [Time.deriv_eq, fderiv_fun_sum]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    conv_lhs =>
      enter [2, k]
      rw [fderiv_mul_const (hBd _).differentiableAt]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    congr
    funext i
    ring_nf
    rfl
    · intro k _
      apply DifferentiableAt.mul_const
      exact (hBd k).differentiableAt

  rw [h1, Finset.mul_sum, Finset.mul_sum,← Finset.sum_neg_distrib]
  field_simp
  congr
  funext k
  field_simp
  simp [𝓕.c_sq]
  field_simp
  conv_lhs =>
    enter [1, 2, 1, t]
    rw [magneticFieldMatrix_antisymm]
  rw [Time.deriv_eq, fderiv_fun_neg]
  simp [← Time.deriv_eq]
  · refine DifferentiableAt.fun_sum ?_
    intro k _
    apply DifferentiableAt.mul_const
    exact (hBd k).differentiableAt
  · change ContDiff ℝ ∞ (fun _ => 0)
    fun_prop
  · exact electricField_differentiable_time (hA.of_le (ENat.LEInfty.out)) x


-- @@ L457-461 verbatim
/-!

### C.2. The space derivative of the electric field in terms of magnetic field

-/


-- @@ L463-501 expanded
lemma space_deriv_electricField_eq_magneticFieldMatrix {d : ℕ} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d} {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0) (t : Time) (x : Space d) (i k : Fin d) :
    (deriv k) (A.electricField 𝓕.c t · i) x =
      (deriv k) (fun x => 𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j) x :=
  by
  have hA2 : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  rw [P.electricField_space_deriv_eq_time_deriv hA2 t x i k,
    P.time_deriv_electricField_eq_magneticFieldMatrix hA h t x i, Time.deriv_eq, fderiv_const_mul,
    fderiv_fun_sum]
  simp [Finset.mul_sum, -Finset.sum_neg_distrib]
  rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sum]
  simp [-Finset.sum_neg_distrib]
  congr
  funext j
  rw [fderiv_mul_const, fderiv_const_mul, fderiv_mul_const]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq_fderiv_basis, P.magneticFieldMatrix_space_deriv_eq_time_deriv hA2 t x i j k]
  simp [← Time.deriv_eq]
  field_simp
  any_goals apply Differentiable.differentiableAt
  · exact toFieldStrength_eval_differentiable_space hA2 t
  · apply Differentiable.mul_const
    exact toFieldStrength_eval_differentiable_space hA2 t
  · exact toFieldStrength_eval_differentiable_time hA2 x
  · intro i _
    apply Differentiable.differentiableAt
    apply Differentiable.const_mul
    apply Differentiable.mul_const
    exact toFieldStrength_eval_differentiable_space hA2 t
  · intro i _
    apply Differentiable.differentiableAt
    apply Differentiable.mul_const
    exact toFieldStrength_eval_differentiable_time hA2 x
  · apply Differentiable.fun_sum
    intro i _
    apply Differentiable.mul_const
    exact toFieldStrength_eval_differentiable_time hA2 x


-- @@ L503-507 verbatim
/-!

### C.3. Electric field equal propogator cross magnetic field up to constant

-/


-- @@ L509-525 verbatim
lemma electricField_eq_propogator_cross_magneticFieldMatrix {d : ℕ}
    {𝓕 : FreeSpace} {A : ElectromagneticPotential d}
    {s : Direction d} (P : IsPlaneWave 𝓕 A s) (hA : ContDiff ℝ ∞ A)
    (h : IsExtrema 𝓕 A 0) (i : Fin d) :
    ∃ C, ∀ t x, A.electricField 𝓕.c t x i =
    𝓕.c * ∑ j, A.magneticFieldMatrix 𝓕.c t x (i, j) * s.unit j + C := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le ENat.LEInfty.out
  apply Space.equal_up_to_const_of_deriv_eq
  · exact electricField_apply_differentiable hA2
  · exact (Differentiable.fun_sum fun j _ =>
      (magneticFieldMatrix_differentiable A hA2 (i, j)).mul_const _).const_mul _
  · intro t x
    rw [P.time_deriv_electricField_eq_magneticFieldMatrix hA _ t x i]
    congr
  · intro t x i
    rw [P.space_deriv_electricField_eq_magneticFieldMatrix hA]
    congr


-- @@ L527-527 verbatim
end IsPlaneWave


-- @@ L529-529 verbatim
end ElectromagneticPotential


-- @@ L531-531 verbatim
end Electromagnetism
