/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.ElectricField

-- @@ L9-50 verbatim
/-!

# The Magnetic Field

## i. Overview

In 3-spatial dimensions from the electromagnetic potential we can define the magnetic field
` \vec B` as `(∇ ⨯ (A.vectorPotential t)) x`.
In this module we define this magnetic field from the electromagnetic potential.

In general dimensions we define the magnetic field matrix from the spatial components of the
field strength matrix. This is an antisymmetric matrix.

## ii. Key results

- `ElectromagneticPotential.magneticField` : The magnetic field from the electromagnetic potential
  in 3 spatial dimensions.
- `ElectromagneticPotential.magneticFieldMatrix` : The magnetic field matrix from the
  electromagnetic potential in general spatial dimensions.
- `ElectromagneticPotential.time_deriv_magneticFieldMatrix` : The time derivative of the magnetic
  field matrix in terms of the vector potential. (Aka Faraday's law).

## iii. Table of contents

- A. The magnetic field
  - A.1. Relation between the magnetic field and the field strength matrix
  - A.2. Divergence of the magnetic field
- B. The field strength matrix in terms of the electric and magnetic fields
- C. Magnetic field matrix
  - C.1. Antisymmetry of the magnetic field matrix
  - C.2. Magnetic field in terms of the magnetic field matrix
  - C.3. Magnetic field matrix in terms of vector potentials
  - C.4. Smoothness of the magnetic field matrix
  - C.5. Differentiablity of the magnetic field matrix
  - C.6. Spatial derivative of the magnetic field matrix
  - C.7. Temporal derivative of the magnetic field matrix
  - C.8. `curl` of the magnetic field matrix

## iv. References

* None.
-/


-- @@ L52-52 verbatim
@[expose] public section


-- @@ L54-54 verbatim
namespace Electromagnetism

-- @@ L55-55 verbatim
open Module realLorentzTensor

-- @@ L56-56 verbatim
open TensorSpecies

-- @@ L57-57 verbatim
open Tensor


-- @@ L59-59 verbatim
namespace ElectromagneticPotential


-- @@ L61-61 verbatim
open TensorSpecies

-- @@ L62-62 verbatim
open Tensor

-- @@ L63-63 verbatim
open SpaceTime

-- @@ L64-64 verbatim
open TensorProduct

-- @@ L65-65 verbatim
open minkowskiMatrix

-- @@ L66-66 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L67-67 verbatim
attribute [-simp] Nat.succ_eq_add_one

-- @@ L68-68 verbatim
attribute [-simp] Fin.succAbove_zero


-- @@ L70-70 verbatim
open Space Time


-- @@ L72-76 verbatim
/-!

## A. The magnetic field

-/


-- @@ L78-81 expanded
/-- The magnetic field from the electromagnetic potential. -/
noncomputable def magneticField (c : SpeedOfLight := 1) (A : ElectromagneticPotential) :
    MagneticField := fun t x => (curl (A.vectorPotential c t)) x


-- @@ L83-84 expanded
lemma magneticField_eq {c : SpeedOfLight} (A : ElectromagneticPotential) :
    A.magneticField c = fun t x => (curl (A.vectorPotential c t)) x :=
  rfl


-- @@ L86-90 verbatim
/-!

### A.1. Relation between the magnetic field and the field strength tensor

-/


-- @@ L92-108 verbatim
lemma magneticField_coord_eq_toFieldStrength_eval {i : Fin 3} {c : SpeedOfLight}
    (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) :
    A.magneticField c t x i = - toField {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) |
      [Sum.inr (i+1)] [Sum.inr (i+2)]}ᵀ := by
  rw [toFieldStrength_eval_apply_eq_single]
  simp only [Fin.isValue, inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add, neg_add_rev, neg_neg]
  rw [magneticField]
  simp only [curl, Fin.isValue]
  rw [neg_add_eq_sub]
  congr
  all_goals
  · rw [SpaceTime.deriv_sum_inr c _ hA]
    simp only [Fin.isValue, ContinuousLinearEquiv.apply_symm_apply]
    rw [Space.deriv_eq, Space.deriv_eq, Lorentz.Vector.fderiv_apply]
    rfl
    · fun_prop


-- @@ L110-114 verbatim
/-!

### A.2. Divergence of the magnetic field

-/


-- @@ L116-120 verbatim
lemma magneticField_div_eq_zero (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) : Space.div (A.magneticField c t) = 0 := by
  simp only [magneticField_eq]
  rw [Space.div_of_curl_eq_zero]
  exact vectorPotential_contDiff_space A hA t


-- @@ L122-126 verbatim
/-!

### A.4. The magnetic field on constructors

-/


-- @@ L128-161 expanded
open Matrix in
/-- The magnetic field of the electromagnetic potential created from the electric field
  `E` and the magnetic field `B` is `B`, as long as Gauss's law is satisfied. -/
lemma ofElectromagneticField_magneticField {c : SpeedOfLight} (E : ElectricField)
    (B : MagneticField) (B_contDiff : ∀ t, ContDiff ℝ 1 (B t)) (B_grad : ∀ t, div (B t) = 0) :
    (ofElectromagneticField c E B).magneticField c = B :=
  by
  ext1 t
  ext1 x
  have h1 := eq_neg_curl_of_div_zero (B t) (B_contDiff t) (B_grad t)
  conv_rhs => rw [h1]
  simp only [magneticField, ofElectromagneticField_vectorPotential, WithLp.equiv_apply,
    WithLp.ofLp_smul, map_smul, LinearMap.smul_apply]
  rw [fun_curl_neg]
  simp only [WithLp.equiv_symm_apply, WithLp.toLp_smul, Pi.neg_apply]
  change
    Differentiable ℝ fun x =>
      ∫ (u : ℝ) in 0..1,
        u • WithLp.toLp 2 ((crossProduct (Space.basis.repr x).ofLp) (B t (u • x)).ofLp)
  apply ContDiff.differentiable (n := 1) _ (by simp)
  apply contDiff_parametric_intervalIntegral_of_contDiff
  refine contDiff_euclidean.mpr ?_
  intro i
  let C : (Space) × ℝ → EuclideanSpace ℝ (Fin 3) := fun p =>
    let x := p.1
    let u := p.2
    (fun a b =>
        (WithLp.equiv 2 (Fin 3 → ℝ)).symm
          (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
      (u • basis.repr x) (B t (u • x))
  suffices h : ContDiff ℝ 1 (fun x => C x i)
    by
    convert! h using 1
    simp [C]
    rfl
  fin_cases i
  all_goals
    · simp [C, crossProduct]
      fun_prop


-- @@ L163-167 verbatim
/-!

## B. The components of the field strength tensor in terms of the electric and magnetic fields

-/


-- @@ L169-197 verbatim
lemma toFieldStrength_eval_eq_electric_magnetic {c} (A : ElectromagneticPotential) (t : Time)
    (x : Space) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    toField {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) | [μ] [ν]}ᵀ =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField c t x i / c
    | Sum.inr i, Sum.inl 0 => A.electricField c t x i / c
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField c t x 2
    | 0, 2 => A.magneticField c t x 1
    | 1, 0 => A.magneticField c t x 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField c t x 0
    | 2, 0 => - A.magneticField c t x 1
    | 2, 1 => A.magneticField c t x 0
    | 2, 2 => 0 := by
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => simp [toFieldStrength_eval_diag_eq_zero]
  | Sum.inl 0, Sum.inr i => simp [electricField_eq_toFieldStrength_eval A t x i hA]
  | Sum.inr i, Sum.inl 0 =>
    simp [electricField_eq_toFieldStrength_eval A t x i hA]
    field_simp
    rw [toFieldStrength_eval_antisymm]
  | Sum.inr i, Sum.inr j =>
    fin_cases i <;> fin_cases j <;>
    simp [magneticField_coord_eq_toFieldStrength_eval A t x hA, toFieldStrength_eval_diag_eq_zero]
    repeat rw [toFieldStrength_eval_antisymm]


-- @@ L199-222 verbatim
lemma toFieldStrength_eval_eq_electric_magnetic_of_spaceTime (c : SpeedOfLight)
    (A : ElectromagneticPotential)
    (x : SpaceTime) (hA : Differentiable ℝ A) (μ ν : Fin 1 ⊕ Fin 3) :
    let tx := SpaceTime.toTimeAndSpace c x
    toField {A.toFieldStrength x | [μ] [ν]}ᵀ =
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 => 0
    | Sum.inl 0, Sum.inr i => - A.electricField c tx.1 tx.2 i / c
    | Sum.inr i, Sum.inl 0 => A.electricField c tx.1 tx.2 i / c
    | Sum.inr i, Sum.inr j =>
    match i, j with
    | 0, 0 => 0
    | 0, 1 => - A.magneticField c tx.1 tx.2 2
    | 0, 2 => A.magneticField c tx.1 tx.2 1
    | 1, 0 => A.magneticField c tx.1 tx.2 2
    | 1, 1 => 0
    | 1, 2 => - A.magneticField c tx.1 tx.2 0
    | 2, 0 => - A.magneticField c tx.1 tx.2 1
    | 2, 1 => A.magneticField c tx.1 tx.2 0
    | 2, 2 => 0 := by
  dsimp
  rw [← toFieldStrength_eval_eq_electric_magnetic A]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact hA


-- @@ L224-228 verbatim
/-!

## C. Magnetic field matrix

-/


-- @@ L230-234 verbatim
/-- The matrix corresponding to the magnetic field in general dimensions.
  In `3` space-dimensions this reduces to a vector. -/
noncomputable def magneticFieldMatrix (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → (Fin d × Fin d) → ℝ := timeSlice c <| fun x ij =>
    toField {A.toFieldStrength x | [Sum.inr ij.1] [Sum.inr ij.2]}ᵀ


-- @@ L236-239 verbatim
lemma magneticFieldMatrix_eq {c : SpeedOfLight} (A : ElectromagneticPotential d) :
    A.magneticFieldMatrix c = fun t x ij =>
      toField {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) |
        [Sum.inr ij.1] [Sum.inr ij.2]}ᵀ := rfl


-- @@ L241-246 verbatim
lemma toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i j : Fin d) :
    toField {A.toFieldStrength x | [Sum.inr i] [Sum.inr j]}ᵀ =
    A.magneticFieldMatrix c (x.time c) x.space (i, j) := by
  simp [magneticFieldMatrix_eq]


-- @@ L248-252 verbatim
/-!

### C.1. Antisymmetry of the magnetic field matrix

-/


-- @@ L254-258 verbatim
lemma magneticFieldMatrix_antisymm {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix c t x (i, j) = - A.magneticFieldMatrix c t x (j, i) :=
  toFieldStrength_eval_antisymm A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i) (Sum.inr j)


-- @@ L260-265 verbatim
@[simp]
lemma magneticFieldMatrix_diag_eq_zero {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) :
    A.magneticFieldMatrix c t x (i, i) = 0 :=
  toFieldStrength_eval_diag_eq_zero A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i)


-- @@ L267-271 verbatim
/-!

### C.2. Magnetic field in terms of the magnetic field matrix

-/


-- @@ L273-278 verbatim
lemma magneticField_eq_magneticFieldMatrix {c : SpeedOfLight} (A : ElectromagneticPotential)
    (hA : Differentiable ℝ A) :
    A.magneticField c = fun t x => WithLp.toLp 2 fun i =>
      - A.magneticFieldMatrix c t x ((i+1), (i+2)) := by
  ext t x
  simp [magneticFieldMatrix_eq, magneticField_coord_eq_toFieldStrength_eval A t x hA]


-- @@ L280-293 expanded
lemma magneticField_curl_eq_magneticFieldMatrix {c : SpeedOfLight} (A : ElectromagneticPotential)
    (hA : ContDiff ℝ 2 A) (t : Time) :
    (curl (A.magneticField c t)) x i = ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x :=
  by
  rw [magneticField_eq_magneticFieldMatrix A (hA.differentiable (by simp))]
  simp only [curl, Fin.isValue, deriv_eq_fderiv_basis, fderiv_fun_neg, _root_.neg_apply,
    sub_neg_eq_add, Fin.sum_univ_three]
  fin_cases i <;>
    · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, zero_add,
        magneticFieldMatrix_diag_eq_zero, fderiv_fun_const, Pi.ofNat_apply, _root_.zero_apply,
        add_zero]
      conv_lhs =>
        enter [1, 1, 1, 2, x]
        rw [magneticFieldMatrix_antisymm]
      simp [add_comm]


-- @@ L295-299 verbatim
/-!

### C.3. Magnetic field matrix in terms of vector potentials

-/


-- @@ L301-315 verbatim
lemma magneticFieldMatrix_eq_vectorPotential {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d) (i j : Fin d) :
    A.magneticFieldMatrix c t x (i, j) = Space.deriv j (A.vectorPotential c t · i) x -
    Space.deriv i (A.vectorPotential c t · j) x := by
  simp only [magneticFieldMatrix_eq]
  rw [toFieldStrength_eval_apply_eq_single]
  simp only [inr_i_inr_i, neg_mul, one_mul, sub_neg_eq_add]
  rw [SpaceTime.deriv_sum_inr c _ hA, SpaceTime.deriv_sum_inr c _ hA]
  simp [vectorPotential]
  rw [add_comm]
  congr
  all_goals
  · rw [← Space.deriv_lorentz_vector]
    rfl
    fun_prop


-- @@ L317-321 verbatim
/-!

### C.4. Smoothness of the magnetic field matrix

-/


-- @@ L323-326 verbatim
lemma magneticFieldMatrix_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (ij) :
    ContDiff ℝ n ↿(fun t x => A.magneticFieldMatrix c t x ij) := by
  exact (toFieldStrength_eval_contDiff hA).comp (toTimeAndSpace c).symm.contDiff


-- @@ L328-331 verbatim
lemma magneticFieldMatrix_space_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (t : Time) (ij) :
    ContDiff ℝ n (fun x => A.magneticFieldMatrix c t x ij) := by
  exact (magneticFieldMatrix_contDiff A hA ij).comp (f := fun x => (t, x)) (by fun_prop)


-- @@ L333-336 verbatim
lemma magneticFieldMatrix_time_contDiff {n} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) (ij) :
    ContDiff ℝ n (fun t => A.magneticFieldMatrix c t x ij) := by
  exact (magneticFieldMatrix_contDiff A hA ij).comp (f := fun t => (t, x)) (by fun_prop)


-- @@ L338-342 verbatim
/-!

### C.5. Differentiablity of the magnetic field matrix

-/


-- @@ L344-346 verbatim
lemma magneticFieldMatrix_differentiable {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (ij) : Differentiable ℝ ↿(fun t x => A.magneticFieldMatrix c t x ij) := by
  exact (toFieldStrength_eval_differentiable hA).comp (toTimeAndSpace c).symm.differentiable


-- @@ L348-351 verbatim
lemma magneticFieldMatrix_differentiable_space {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (ij) :
    Differentiable ℝ (fun x => A.magneticFieldMatrix c t x ij) := by
  exact (magneticFieldMatrix_differentiable A hA ij).comp (f := fun x => (t, x)) (by fun_prop)


-- @@ L353-356 verbatim
lemma magneticFieldMatrix_differentiable_time {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (x : Space d) (ij) :
    Differentiable ℝ (fun t => A.magneticFieldMatrix c t x ij) := by
  exact (magneticFieldMatrix_differentiable A hA ij).comp (f := fun t => (t, x)) (by fun_prop)


-- @@ L358-362 verbatim
/-!

### C.6. Spatial derivative of the magnetic field matrix

-/


-- @@ L364-385 expanded
lemma magneticFieldMatrix_space_deriv_eq {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j k : Fin d) :
    (deriv k) (A.magneticFieldMatrix c t · (i, j)) x =
      (deriv i) (A.magneticFieldMatrix c t · (k, j)) x -
        (deriv j) (A.magneticFieldMatrix c t · (k, i)) x :=
  by
  conv_lhs =>
    enter [2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x i j]
  conv_rhs =>
    enter [1, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  conv_rhs =>
    enter [2, 2, x]
    rw [magneticFieldMatrix_eq_vectorPotential A (hA.differentiable (by simp)) t x]
  rw [fun_deriv_sub, fun_deriv_sub, fun_deriv_sub]
  rw [Space.deriv_commute _ (vectorPotential_apply_contDiff_space _ hA _ i),
    Space.deriv_commute _ (vectorPotential_apply_contDiff_space _ hA _ j),
    Space.deriv_commute _ (vectorPotential_apply_contDiff_space _ hA _ k)]
  ring
  all_goals
    · apply Space.deriv_differentiable
      apply vectorPotential_apply_contDiff_space _ hA


-- @@ L387-391 verbatim
/-!

### C.7. Temporal derivative of the magnetic field matrix

-/


-- @@ L393-432 expanded
lemma time_deriv_magneticFieldMatrix {d : ℕ} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (A.magneticFieldMatrix c · x (i, j)) t =
      (deriv i) (A.electricField c t · j) x - (deriv j) (A.electricField c t · i) x :=
  by
  calc
    _
    _ =
        ∂ₜ (fun t => (deriv j) (fun x => A.vectorPotential c t x i) x) t -
          ∂ₜ (fun t => (deriv i) (fun x => A.vectorPotential c t x j) x) t :=
      by
      conv_lhs =>
        enter [1, t]
        rw [magneticFieldMatrix_eq_vectorPotential _ (hA.differentiable (by simp))]
      rw [Time.deriv, fderiv_fun_sub]
      rfl
      all_goals
        · apply Differentiable.differentiableAt
          apply Space.space_deriv_differentiable_time
          apply vectorPotential_comp_contDiff _ hA
    _ =
        (deriv j) (fun x => ∂ₜ (fun t => A.vectorPotential c t x i) t) x -
          (deriv i) (fun x => ∂ₜ (fun t => A.vectorPotential c t x j) t) x :=
      by
      rw [Space.time_deriv_comm_space_deriv _, Space.time_deriv_comm_space_deriv _]
      all_goals · apply vectorPotential_comp_contDiff _ hA
    _ = (deriv i) (A.electricField c t · j) x - (deriv j) (A.electricField c t · i) x :=
      by
      have hφ := scalarPotential_contDiff_space c A hA t
      have hd1 : ∀ k : Fin d, DifferentiableAt ℝ (fun x => -(A.electricField c t x).ofLp k) x :=
        fun k => (electricField_apply_differentiable_space hA t k).neg.differentiableAt
      have hd2 : ∀ k : Fin d, DifferentiableAt ℝ (Space.deriv k (scalarPotential c A t)) x :=
        fun k => (Space.deriv_differentiable hφ k).differentiableAt
      conv_lhs =>
        enter [1, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      conv_lhs =>
        enter [2, 2, x]
        rw [time_deriv_comp_vectorPotential_eq_electricField (hA.differentiable (by simp))]
      rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub (hd1 i) (hd2 i), fderiv_fun_neg]
      conv_lhs =>
        enter [2]
        rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sub (hd1 j) (hd2 j), fderiv_fun_neg]
      simp only [FunLike.coe_sub, Pi.sub_apply, _root_.neg_apply, ← Space.deriv_eq_fderiv_basis]
      rw [Space.deriv_commute _ hφ]
      ring


-- @@ L434-454 expanded
lemma time_deriv_time_deriv_magneticFieldMatrix {d : ℕ} {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ 3 A) (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix c · x (i, j))) t =
      (deriv i) (fun x => ∂ₜ (fun t => A.electricField c t x) t j) x -
        (deriv j) (fun x => ∂ₜ (fun t => A.electricField c t x) t i) x :=
  by
  conv_lhs =>
    enter [1, t]
    rw [time_deriv_magneticFieldMatrix A (hA.of_le (right_eq_inf.mp rfl)) t x i j]
  rw [Time.deriv, fderiv_fun_sub]
  simp [← Time.deriv_eq]
  rw [Space.time_deriv_comm_space_deriv _, Space.time_deriv_comm_space_deriv _]
  congr
  all_goals
    first
    | ( funext x
        rw [Time.deriv_euclid]
        apply electricField_differentiable_time (hA.of_le (right_eq_inf.mp rfl)))
    | apply electricField_apply_contDiff hA
    | ( apply Differentiable.differentiableAt
        apply Space.space_deriv_differentiable_time
        apply electricField_apply_contDiff hA)


-- @@ L456-460 verbatim
/-!

### C.8. `curl` of the magnetic field matrix

-/


-- @@ L462-483 verbatim
lemma curl_magneticFieldMatrix_eq_electricField_toFieldStrength_eval {d : ℕ} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i : Fin d) :
    ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x =
    (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    (∑ (μ : (Fin 1 ⊕ Fin d)), (∂_ μ (fun x => toField {A.toFieldStrength x | [μ] [Sum.inr i]}ᵀ)
    ((toTimeAndSpace c).symm (t, x)))) := by
  trans (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    (- (1/c^2) * ∂ₜ (fun t => A.electricField c t x) t i +
    ∑ j, Space.deriv j (A.magneticFieldMatrix c t · (j, i)) x)
  · ring
  congr 1
  rw [Fintype.sum_sum_type]
  congr
  · simp
    rw [time_deriv_electricField_eq_toFieldStrength_eval hA t x i]
    field_simp
  · funext j
    rw [SpaceTime.deriv_sum_inr c]
    simp
    rfl
    · apply toFieldStrength_eval_differentiable hA


-- @@ L485-485 verbatim
end ElectromagneticPotential


-- @@ L487-487 verbatim
end Electromagnetism
