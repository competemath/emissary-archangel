/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Fin.Lift
public import Mathlib.RingTheory.Polynomial.Basic

-- @@ L10-10 verbatim
/-! # Polynomial Coefficient Interfaces -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
section PolynomialInterface


-- @@ L17-17 verbatim
open Polynomial


-- @@ L19-23 verbatim
variable {F : Type*} [Semiring F] {deg : ℕ} {coeffs : Fin deg → F}

lemma natDegree_lt_of_lbounded_zero_coeff {p : F[X]} [NeZero deg]
    (h : ∀ i, deg ≤ i → p.coeff i = 0) : p.natDegree < deg := by
  aesop (add 
-- @@ L23-23 verbatim
unsafe [(by by_contra), (by specialize h p.natDegree)])


-- @@ L25-26 verbatim
def coeffsOfPolynomial (p : F[X]) : Fin deg → F :=
  fun ⟨x, _⟩ ↦ p.coeff x


-- @@ L28-28 verbatim
variable [DecidableEq F]


-- @@ L30-35 verbatim
def polynomialOfCoeffs (coeffs : Fin deg → F) : F[X] :=
  ⟨
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0},
    fun i ↦ if h : i < deg then coeffs ⟨i, h⟩ else 0,
    fun a ↦ by aesop (add safe (by existsi ⟨a, w⟩))
  ⟩


-- @@ L37-42 verbatim
@[simp]
lemma natDegree_polynomialOfCoeffs_deg_lt_deg
    [NeZero deg] {coeffs : Fin deg → F} :
  (polynomialOfCoeffs coeffs).natDegree < deg := by
  aesop (add simp polynomialOfCoeffs)
        (add safe apply natDegree_lt_of_lbounded_zero_coeff)


-- @@ L44-47 verbatim
@[simp]
lemma degree_polynomialOfCoeffs_deg_lt_deg :
    (polynomialOfCoeffs coeffs).degree < deg := by
  aesop (add simp [polynomialOfCoeffs, degree_lt_iff_coeff_zero])


-- @@ L49-52 verbatim
@[simp]
lemma polynomialOfCoeffs_mem_degreeLT [NeZero deg] :
    polynomialOfCoeffs coeffs ∈ degreeLT F deg := by
  aesop (add simp Polynomial.mem_degreeLT)


-- @@ L54-61 verbatim
@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs :
    Fin.liftF' (polynomialOfCoeffs coeffs).coeff = coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])

lemma coeff_polynomialOfCoeffs_eq_coeffs' :
    (polynomialOfCoeffs coeffs).coeff = fun x ↦ if h : x < deg then coeffs ⟨x, h⟩ else 0 := by
  aesop (add simp polynomialOfCoeffs)


-- @@ L63-66 verbatim
@[simp]
lemma coeff_polynomialOfCoeffs_eq_coeffs'' :
    (polynomialOfCoeffs coeffs).coeff = Fin.liftF coeffs := by
  aesop (add simp [Fin.liftF', polynomialOfCoeffs])


-- @@ L68-86 verbatim
@[simp]
lemma polynomialOfCoeffs_eq_zero :
    polynomialOfCoeffs coeffs = 0 ↔ ∀ (x : ℕ) (h : x < deg), coeffs ⟨x, h⟩ = 0 := by
  constructor <;> intro h
  · intro x hx
    have : (polynomialOfCoeffs coeffs).coeff x = (0 : F[X]).coeff x := by rw [h]
    simp only [polynomialOfCoeffs, ne_eq, coeff_ofFinsupp, Finsupp.coe_mk, coeff_zero,
      dite_eq_right_iff] at this
    exact this hx
  · ext m
    rw [coeff_polynomialOfCoeffs_eq_coeffs']
    simp [h]

lemma polynomialOfCoeffs_coeffsOfPolynomial {p : F[X]}
    (h : p.natDegree + 1 = deg) : polynomialOfCoeffs (coeffsOfPolynomial (deg := deg) p) = p := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe apply coeff_eq_zero_of_natDegree_lt)
        (add safe (by omega))


-- @@ L88-93 verbatim
@[simp]
lemma coeffsOfPolynomial_polynomialOfCoeffs :
    coeffsOfPolynomial (polynomialOfCoeffs coeffs) = coeffs := by
  ext x; symm
  aesop (add simp [polynomialOfCoeffs, coeffsOfPolynomial, coeff_polynomialOfCoeffs_eq_coeffs'])
        (add safe (by omega))


-- @@ L95-97 verbatim
@[simp]
lemma support_polynomialOfCoeffs : (polynomialOfCoeffs coeffs).support =
    Finset.map ⟨Fin.val, Fin.val_injective⟩ {i | coeffs i ≠ 0} := rfl


-- @@ L99-102 verbatim
@[simp]
lemma eval_polynomialsOfCoeffs [NeZero deg] {α : F} :
    (polynomialOfCoeffs coeffs).eval α = ∑ x ∈ {i | coeffs i ≠ 0}, coeffs x * α ^ x.1 := by
  simp [eval_eq_sum, sum_def, Fin.liftF]


-- @@ L104-106 verbatim
@[simp]
lemma isRoot_polynomialsOfCoeffs {x : F} :
    IsRoot (polynomialOfCoeffs coeffs) x ↔ eval x (polynomialOfCoeffs coeffs) = 0 := by rfl


-- @@ L108-108 verbatim
end PolynomialInterface
