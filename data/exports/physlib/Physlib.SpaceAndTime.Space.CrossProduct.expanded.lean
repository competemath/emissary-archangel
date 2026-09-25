/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Physlib.SpaceAndTime.Time.Derivatives

-- @@ L10-37 verbatim
/-!

# The cross product on Euclidean vectors in three dimensions

## i. Overview

In this module we define the cross product on `EuclideanSpace ℝ (Fin 3)`,
and prove various properties about it related to time derivatives and inner products.

## ii. Key results

- `⨯ₑ₃` : The cross product on `EuclideanSpace ℝ (Fin 3)`.
- `time_deriv_cross_commute` : Time derivatives move out of cross products.
- `inner_cross_self` : Inner product of a vector with the cross product of another vector
  and itself is zero.
- `inner_self_cross` : Inner product of a vector with the cross product of itself
  and another vector is zero.

## iii. Table of contents

- A. The notation for the cross product
- B. Time derivatives move out of cross products
- C. Inner product of vectors with cross products involving themselves

## iv. References

* None.
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace Space

-- @@ L42-42 verbatim
open Time Matrix


-- @@ L44-48 verbatim
/-!

## A. The notation for the cross product

-/


-- @@ L50-54 verbatim
set_option quotPrecheck false in
/-- Cross product in `EuclideanSpace ℝ (Fin 3)`. Uses `⨯` which is typed using `\X` or
`\vectorproduct` or `\crossproduct`. -/
infixl:70 " ⨯ₑ₃ " => fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b)


-- @@ L56-60 verbatim
/-!

## B. Time derivatives move out of cross products

-/


-- @@ L62-99 expanded
/-- Cross product and fderiv commute. -/
lemma fderiv_cross_commute {t : Time} {s : EuclideanSpace ℝ (Fin 3)}
    {f : Time → EuclideanSpace ℝ (Fin 3)} (hf : Differentiable ℝ f) :
    (fun a b =>
          (WithLp.equiv 2 (Fin 3 → ℝ)).symm
            (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
        s ((fderiv ℝ (fun t' => f t') t) 1) =
      fderiv ℝ
        (fun t' =>
          (fun a b =>
              (WithLp.equiv 2 (Fin 3 → ℝ)).symm
                (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
            s (f t'))
        t 1 :=
  by
  have h (i j : Fin 3) :
    s i * (fderiv ℝ (fun u => f u) t) 1 j - s j * (fderiv ℝ (fun u => f u) t) 1 i =
      (fderiv ℝ (fun t => s i * f t j - s j * f t i) t) 1 :=
    by
    rw [fderiv_fun_sub, fderiv_const_mul, fderiv_const_mul]
    · simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Time.fderiv_euclid, Time.fderiv_euclid]
      · intro i
        repeat fun_prop
      · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
  rw [crossProduct]
  ext i
  fin_cases i <;>
    · simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
        LinearMap.mk₂_apply, Fin.reduceFinMk, WithLp.equiv_symm_apply, PiLp.toLp_apply, cons_val]
      rw [h]
      simp only [Fin.isValue]
      rw [← Time.fderiv_euclid]
      simp [Fin.isValue, cons_val_zero]
      apply Time.differentiable_euclid
      intro i
      fin_cases i
      · simp [Fin.zero_eta, Fin.isValue]
        fun_prop
      · simp [Fin.isValue]
        fun_prop
      · simp [Fin.isValue]
        fun_prop


-- @@ L101-107 expanded
/-- Cross product and time derivative commute. -/
lemma time_deriv_cross_commute {s : EuclideanSpace ℝ (Fin 3)} {f : Time → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) :
    (fun a b =>
          (WithLp.equiv 2 (Fin 3 → ℝ)).symm
            (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
        s (∂ₜ (fun t => f t) t) =
      ∂ₜ
        (fun t =>
          (fun a b =>
              (WithLp.equiv 2 (Fin 3 → ℝ)).symm
                (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
            s (f t))
        t :=
  by
  repeat rw [Time.deriv]
  rw [fderiv_cross_commute]
  fun_prop


-- @@ L109-113 verbatim
/-!

## C. Inner product of vectors with cross products involving themselves

-/


-- @@ L115-121 expanded
lemma inner_cross_self (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v
        ((fun a b =>
            (WithLp.equiv 2 (Fin 3 → ℝ)).symm
              (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
          w v) =
      0 :=
  by
  cases v using WithLp.rec with
  | _ v =>
    cases w using WithLp.rec with
    | _ w =>
      simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
      change (crossProduct w) v ⬝ᵥ v = _
      rw [dotProduct_comm, dot_cross_self]


-- @@ L123-129 expanded
lemma inner_self_cross (v w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v
        ((fun a b =>
            (WithLp.equiv 2 (Fin 3 → ℝ)).symm
              (WithLp.equiv 2 (Fin 3 → ℝ) a ⨯₃ WithLp.equiv 2 (Fin 3 → ℝ) b))
          v w) =
      0 :=
  by
  cases v using WithLp.rec with
  | _ v =>
    cases w using WithLp.rec with
    | _ w =>
      simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply, PiLp.inner_apply]
      change (crossProduct v) w ⬝ᵥ v = _
      rw [dotProduct_comm, dot_self_cross]


-- @@ L131-131 verbatim
end Space
