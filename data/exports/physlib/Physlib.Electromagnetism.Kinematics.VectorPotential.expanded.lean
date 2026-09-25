/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.EMPotential
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

-- @@ L10-39 verbatim
/-!

# The vector Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the vector potential, and prove lemmas about it.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the vector potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Vector Potential
- B. Smoothness of the vector potential
- C. Differentiablity of the vector potential

## iv. References

* None.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
namespace Electromagnetism

-- @@ L44-44 verbatim
open Module realLorentzTensor

-- @@ L45-45 verbatim
open TensorSpecies

-- @@ L46-46 verbatim
open Tensor


-- @@ L48-48 verbatim
namespace ElectromagneticPotential


-- @@ L50-50 verbatim
open TensorSpecies

-- @@ L51-51 verbatim
open Tensor

-- @@ L52-52 verbatim
open SpaceTime

-- @@ L53-53 verbatim
open TensorProduct

-- @@ L54-54 verbatim
open minkowskiMatrix

-- @@ L55-55 verbatim
attribute [-simp] Fintype.sum_sum_type

-- @@ L56-56 verbatim
attribute [-simp] Nat.succ_eq_add_one


-- @@ L58-62 verbatim
/-!

## A. Definition of the Vector Potential

-/


-- @@ L64-67 verbatim
/-- The vector potential from the electromagnetic potential. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) := timeSlice c <|
  fun x => WithLp.toLp 2 fun i => A x (Sum.inr i)


-- @@ L69-73 verbatim
/-!

## B. Relation to constructors

-/


-- @@ L75-79 verbatim
@[simp]
lemma ofScalarPotential_vectorPotential {d} (c : SpeedOfLight)
    (φ : Time → Space d → ℝ) : (ofScalarPotential c φ).vectorPotential c = 0 := by
  simp only [vectorPotential, ofScalarPotential]
  rfl


-- @@ L81-84 verbatim
@[simp]
lemma ofStaticScalarPotential_vectorPotential {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : (ofStaticScalarPotential c φ).vectorPotential c = 0 := by
  simp [ofStaticScalarPotential]


-- @@ L86-91 verbatim
@[simp]
lemma ofVectorPotential_vectorPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofVectorPotential c A).vectorPotential c = A := by
  ext i
  simp [vectorPotential, ofVectorPotential]


-- @@ L93-97 verbatim
@[simp]
lemma ofStaticVectorPotential_vectorPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticVectorPotential c A).vectorPotential c = fun _ => A := by
  simp [ofStaticVectorPotential]


-- @@ L99-104 verbatim
@[simp]
lemma ofPotentials_vectorPotential {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofPotentials c φ A).vectorPotential c = A := by
  ext i
  simp [vectorPotential, ofPotentials]


-- @@ L106-110 verbatim
@[simp]
lemma ofStaticPotentials_vectorPotential {d} (c : SpeedOfLight) (φ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticPotentials c φ A).vectorPotential c = fun _ => A := by
  simp [ofStaticPotentials_eq_ofPotentials]


-- @@ L112-116 verbatim
/-!

## B.1. ofElectromagneticField

-/


-- @@ L118-124 expanded
open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) :
    (ofElectromagneticField c E B).vectorPotential c = fun t x =>
      -∫ u in 0..(1 : ℝ),
          (fun a b =>
              (WithLp.equiv 2 (Fin 3 → ℝ)).symm
                (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
            (u • Space.basis.repr x) (B t (u • x)) ∂volume :=
  by simp [ofElectromagneticField]


-- @@ L126-141 expanded
open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential_apply {t x} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (i : Fin 3) (hB : Continuous ↿B) :
    (ofElectromagneticField c E B).vectorPotential c t x i =
      -∫ u in 0..(1 : ℝ),
          ((fun a b =>
                (WithLp.equiv 2 (Fin 3 → ℝ)).symm
                  (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
              (u • Space.basis.repr x) (B t (u • x)))
            i ∂volume :=
  by
  simp [ofElectromagneticField_vectorPotential]
  rw [intervalIntegral.integral_of_le (by simp), intervalIntegral.integral_of_le (by simp)]
  rw [MeasureTheory.eval_integral_piLp]
  simp only [PiLp.smul_apply, smul_eq_mul]
  intro i
  apply MeasureTheory.IntegrableOn.integrable
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le]
  apply Continuous.intervalIntegrable
  fun_prop
  simp


-- @@ L143-166 verbatim
open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential_apply_eq_expand {t x} {c : SpeedOfLight}
    {E : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)} (hB : Continuous ↿B) (i : Fin 3) :
    (ofElectromagneticField c E B).vectorPotential c t x i =
    x (i + 2) * ∫ u in 0..(1 : ℝ), u * B t (u • x) (i + 1) ∂volume -
    x (i + 1) * ∫ u in 0..(1 : ℝ), u * B t (u • x) (i + 2) ∂volume := by
  fin_cases i
  all_goals
  · rw [ofElectromagneticField_vectorPotential_apply _ _ _ _ hB]
    simp [crossProduct]
    ring_nf
    rw [intervalIntegral.integral_sub, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    ring_nf
    congr
    · ext u
      ring
    · ext u
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop


-- @@ L168-194 expanded
open MeasureTheory Matrix Space InnerProductSpace Time in
@[fun_prop]
lemma contDiff_vectorPotential_ofElectromagneticField {n : ℕ} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hB : ContDiff ℝ n ↿B) : ContDiff ℝ n ↿((ofElectromagneticField c E B).vectorPotential c) :=
  by
  let A : Time → Space → EuclideanSpace ℝ (Fin 3) := fun t x =>
    -∫ u in 0..(1 : ℝ),
        (fun a b =>
            (WithLp.equiv 2 (Fin 3 → ℝ)).symm
              (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
          (u • basis.repr x) (B t (u • x)) ∂(volume)
  have h1 : ContDiff ℝ n ↿A := by
    simp only [WithLp.equiv_apply, A]
    apply ContDiff.neg
    apply contDiff_parametric_intervalIntegral_of_contDiff
    refine contDiff_euclidean.mpr ?_
    intro i
    let C : (Time × Space) × ℝ → EuclideanSpace ℝ (Fin 3) := fun p =>
      let (t, x) := p.1
      let u := p.2
      (fun a b =>
          (WithLp.equiv 2 (Fin 3 → ℝ)).symm
            (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
        (u • basis.repr x) (B t (u • x))
    change ContDiff ℝ n (fun x => C x i)
    fin_cases i
    all_goals
      · simp [C, crossProduct]
        fun_prop
  suffices h : ContDiff ℝ n ↿A by
    convert h
    simp [ofElectromagneticField_vectorPotential, A]
  fun_prop


-- @@ L196-196 verbatim
open InnerProductSpace

-- @@ L197-206 verbatim
lemma vectorPotential_inner_radial_eq_zero_ofElectromagneticField
    {c : SpeedOfLight} {E B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {t : Time} {x : Space 3} {a : ℝ} (hB : Continuous ↿B) :
    ⟪(ofElectromagneticField c E B).vectorPotential c t (a • x), Space.basis.repr x⟫_ℝ = 0 := by
  rw [real_inner_comm]
  rw [PiLp.inner_apply]
  have h1 (a b : ℝ) : ⟪a, b⟫_ℝ = b * a:= by rfl
  simp only [Space.basis_repr_apply, ofElectromagneticField_vectorPotential_apply_eq_expand hB,
    Fin.isValue, Space.smul_apply, h1, Fin.sum_univ_three, zero_add, Fin.reduceAdd]
  ring


-- @@ L208-208 verbatim
open Time

-- @@ L209-227 verbatim
@[simp]
lemma time_deriv_vectorPotential_inner_radial_eq_zero_ofElectromagneticField
    {c : SpeedOfLight} {E B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {t : Time} {x : Space 3} {a : ℝ} (hB : ContDiff ℝ 1 ↿B) :
    ⟪∂ₜ ((ofElectromagneticField c E B).vectorPotential c · (a • x)) t,
      Space.basis.repr x⟫_ℝ = 0 := by
  trans ∂ₜ (fun t => ⟪(ofElectromagneticField c E B).vectorPotential c t (a • x),
    Space.basis.repr x⟫_ℝ) t
  · rw [Time.deriv, Time.deriv]
    rw [fderiv_inner_apply]
    simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, inner_zero_right,
      zero_add]
    apply Differentiable.differentiableAt
    fun_prop
    fun_prop
  conv_lhs =>
    enter [1, t]
    rw [vectorPotential_inner_radial_eq_zero_ofElectromagneticField (by fun_prop)]
  simp


-- @@ L229-236 verbatim
/-!

## B. Smoothness of the vector potential

We prove various lemmas about the smoothness of the vector potential from
the smoothness of the electromagnetic potential.

-/


-- @@ L238-247 verbatim
@[fun_prop]
lemma vectorPotential_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_contDiff
  refine contDiff_euclidean.mpr ?_
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)


-- @@ L249-249 verbatim
open ContDiff

-- @@ L250-255 verbatim
@[fun_prop]
lemma vectorPotential_contDiff_of_smooth {n : ℕ} {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ n ↿(A.vectorPotential c) := by
  apply vectorPotential_contDiff
  exact hA.of_le (ENat.LEInfty.out)


-- @@ L257-262 verbatim
lemma vectorPotential_apply_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA


-- @@ L264-269 verbatim
lemma vectorPotential_comp_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA


-- @@ L271-276 verbatim
lemma vectorPotential_contDiff_space {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.vectorPotential c t) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop


-- @@ L278-285 verbatim
lemma vectorPotential_apply_contDiff_space {n} {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) (i : Fin d) :
    ContDiff ℝ n (fun x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿(A.vectorPotential c) ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff_space A hA t


-- @@ L287-292 verbatim
lemma vectorPotential_contDiff_time {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.vectorPotential c · x) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop


-- @@ L294-301 verbatim
/-!

## C. Differentiablity of the vector potential

We prove various lemmas about the differentiablity of the vector potential from
the differentiablity of the electromagnetic potential.

-/


-- @@ L303-311 verbatim
lemma vectorPotential_differentiable {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_differentiable
  refine differentiable_euclidean.mpr ?_
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)


-- @@ L313-318 verbatim
lemma vectorPotential_differentiable_time {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.vectorPotential c · x) := by
  change Differentiable ℝ (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact vectorPotential_differentiable A hA
  · fun_prop


-- @@ L320-320 verbatim
end ElectromagneticPotential


-- @@ L322-322 verbatim
end Electromagnetism
