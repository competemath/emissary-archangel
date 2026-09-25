/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.VectorPotential

-- @@ L9-39 verbatim
/-!

# The Scalar Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the scalar potential, and prove lemmas about it.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the scalar potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.scalarPotential` : The scalar potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Scalar Potential
- B. Relation to constructors
- C. Smoothness of the Scalar Potential
- D. Differentiability of the Scalar Potential

## iv. References

* None.
-/


-- @@ L41-41 verbatim
@[expose] public section

-- @@ L42-42 verbatim
namespace Electromagnetism

-- @@ L43-43 verbatim
open Module realLorentzTensor

-- @@ L44-44 verbatim
open TensorSpecies

-- @@ L45-45 verbatim
open Tensor


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
attribute [-simp] Fintype.sum_sum_type

-- @@ L55-55 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L57-61 verbatim
/-!

## A. Definition of the Scalar Potential

-/


-- @@ L63-66 verbatim
/-- The scalar potential from the electromagnetic potential. -/
noncomputable def scalarPotential {d} (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → ℝ := timeSlice c <|
  fun x => c * A x (Sum.inl 0)


-- @@ L68-72 verbatim
/-!

## B. Relation to constructors

-/


-- @@ L74-79 verbatim
@[simp]
lemma ofScalarPotential_scalarPotential {d} (c : SpeedOfLight)
    (φ : Time → Space d → ℝ) : (ofScalarPotential c φ).scalarPotential c = φ := by
  simp only [scalarPotential, ofScalarPotential, Fin.isValue]
  field_simp
  simp


-- @@ L81-84 verbatim
@[simp]
lemma ofStaticScalarPotential_scalarPotential {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : (ofStaticScalarPotential c φ).scalarPotential c = fun _ => φ := by
  simp [ofStaticScalarPotential]


-- @@ L86-91 verbatim
@[simp]
lemma ofVectorPotential_scalarPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofVectorPotential c A).scalarPotential = 0 := by
  simp only [scalarPotential, SpeedOfLight.val_one, ofVectorPotential, Fin.isValue, mul_zero]
  rfl


-- @@ L93-97 verbatim
@[simp]
lemma ofStaticVectorPotential_scalarPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticVectorPotential c A).scalarPotential = 0 := by
  simp [ofStaticVectorPotential]


-- @@ L99-105 verbatim
@[simp]
lemma ofPotentials_scalarPotential {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofPotentials c φ A).scalarPotential c = φ := by
  simp only [scalarPotential, ofPotentials, Fin.isValue]
  field_simp
  simp


-- @@ L107-111 verbatim
@[simp]
lemma ofStaticPotentials_scalarPotential {d} (c : SpeedOfLight) (φ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticPotentials c φ A).scalarPotential c = fun _ => φ := by
  simp [ofStaticPotentials_eq_ofPotentials]


-- @@ L113-119 verbatim
open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_scalarPotential (c : SpeedOfLight)
    (E : Time → Space → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space → EuclideanSpace ℝ (Fin 3)) :
    (ofElectromagneticField c E B).scalarPotential c = fun t x =>
    - ∫ u in (0 : ℝ)..1, ⟪E t (u • x), basis.repr x⟫_ℝ ∂(volume) := by
  simp [ofElectromagneticField]


-- @@ L121-134 verbatim
open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_scalarPotential_eq_add_vectorPotential (c : SpeedOfLight)
    (E : Time → Space → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space → EuclideanSpace ℝ (Fin 3)) (hb : ContDiff ℝ 1 ↿B) :
    (ofElectromagneticField c E B).scalarPotential c = fun t x =>
    - ∫ u in (0 : ℝ)..1, ⟪E t (u • x) +
    ∂ₜ ((ofElectromagneticField c E B).vectorPotential c ·
      (u • x)) t, basis.repr x⟫_ℝ ∂(volume) := by
  simp [ofElectromagneticField_scalarPotential, inner_add_left]
  ext t x
  simp only [neg_inj]
  congr
  ext u
  simp [time_deriv_vectorPotential_inner_radial_eq_zero_ofElectromagneticField (B := B) hb]


-- @@ L136-142 verbatim
/-!

## C. Smoothness of the Scalar Potential

We prove various lemmas about the smoothness of the scalar potential.

-/


-- @@ L144-153 verbatim
lemma scalarPotential_contDiff {n} {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.scalarPotential c) := by
  simp [scalarPotential]
  apply timeSlice_contDiff
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hA
  apply ContDiff.mul
  · fun_prop
  exact h1 (Sum.inl 0)


-- @@ L155-162 verbatim
@[fun_prop]
lemma scalarPotential_contDiff_space {n} {d} (c : SpeedOfLight)
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.scalarPotential c t) := by
  change ContDiff ℝ n (↿(A.scalarPotential c) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact scalarPotential_contDiff c A hA
  · fun_prop


-- @@ L164-164 verbatim
open ContDiff


-- @@ L166-171 verbatim
@[fun_prop]
lemma scalarPotential_contDiff_space_of_smooth {n : ℕ} {d} (c : SpeedOfLight)
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (t : Time) : ContDiff ℝ n (A.scalarPotential c t) := by
  apply scalarPotential_contDiff_space
  exact hA.of_le (ENat.LEInfty.out)


-- @@ L173-178 verbatim
lemma scalarPotential_contDiff_time {n} {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.scalarPotential c · x) := by
  change ContDiff ℝ n (↿(A.scalarPotential c) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact scalarPotential_contDiff c A hA
  · fun_prop


-- @@ L180-186 verbatim
/-!

## d. Differentiability of the Scalar Potential

We prove various lemmas about the differentiability of the scalar potential.

-/


-- @@ L188-197 verbatim
lemma scalarPotential_differentiable {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.scalarPotential c) := by
  simp [scalarPotential]
  apply timeSlice_differentiable
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hA
  apply Differentiable.mul
  · fun_prop
  exact h1 (Sum.inl 0)


-- @@ L199-204 verbatim
lemma scalarPotential_differentiable_space {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (t : Time) : Differentiable ℝ (A.scalarPotential c t) := by
  change Differentiable ℝ (↿(A.scalarPotential c) ∘ fun x => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact scalarPotential_differentiable c A hA
  · fun_prop


-- @@ L206-211 verbatim
lemma scalarPotential_differentiable_time {d} (c : SpeedOfLight) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.scalarPotential c · x) := by
  change Differentiable ℝ (↿(A.scalarPotential c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact scalarPotential_differentiable c A hA
  · fun_prop


-- @@ L213-213 verbatim
end ElectromagneticPotential


-- @@ L215-215 verbatim
end Electromagnetism
