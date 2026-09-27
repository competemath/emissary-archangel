/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.Derivative


-- @@ L10-12 verbatim
/-!
# LeanPool.LeanPolyABC.Lib.Wronskian
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open scoped Polynomial


-- @@ L20-20 verbatim
open Polynomial


-- @@ L22-22 verbatim
namespace LeanPolyABC


-- @@ L24-24 verbatim
variable {R : Type _} [CommRing R]


-- @@ L26-28 verbatim
/-- Wronskian: W(a, b) = ab' - a'b. -/
def wronskian (a b : R[X]) : R[X] :=
  a * derivative b - derivative a * b


-- @@ L30-32 verbatim
@[simp]
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  simp_rw [wronskian]; simp only [MulZeroClass.zero_mul, derivative_zero, sub_self]


-- @@ L34-36 verbatim
@[simp]
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := by
  simp_rw [wronskian]; simp only [derivative_zero, MulZeroClass.mul_zero, sub_self]


-- @@ L38-39 verbatim
theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring


-- @@ L41-42 verbatim
theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring


-- @@ L44-46 verbatim
theorem wronskian_add_right (a b c : R[X]) :
    wronskian a (b + c) = wronskian a b + wronskian a c := by
  simp_rw [wronskian, derivative_add]; ring


-- @@ L48-48 verbatim
theorem wronskian_self (a : R[X]) : wronskian a a = 0 := by rw [wronskian, mul_comm, sub_self]


-- @@ L50-51 verbatim
theorem wronskian_anticomm (a b : R[X]) : wronskian a b = -wronskian b a := by
  rw [wronskian, wronskian]; ring


-- @@ L53-56 verbatim
theorem wronskian_eq_of_sum_zero {a b c : R[X]} (h : a + b + c = 0) :
    wronskian a b = wronskian b c := by
  rw [← neg_eq_iff_add_eq_zero] at h
  rw [← h, wronskian_neg_right, wronskian_add_right, wronskian_self, add_zero, ← wronskian_anticomm]


-- @@ L58-59 verbatim
private theorem degree_ne_bot {a : R[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ := by
  intro h; rw [Polynomial.degree_eq_bot] at h; exact ha h


-- @@ L61-61 verbatim
namespace wronskian


-- @@ L63-79 verbatim
theorem degree_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      refine max_lt_iff.mpr ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (degree_mul_le a (derivative b)) ?_
        rw [WithBot.add_lt_add_iff_left (degree_ne_bot ha)]
        exact Polynomial.degree_derivative_lt hb
      · refine lt_of_le_of_lt (degree_mul_le (derivative a) b) ?_
        rw [WithBot.add_lt_add_iff_right (degree_ne_bot hb)]
        exact Polynomial.degree_derivative_lt ha

-- Note: the following is false!
-- Counterexample: b = a = 1 →
-- (wronskian a b).natDegree = a.natDegree = b.natDegree = 0

-- @@ L80-87 verbatim
theorem natDegree_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  have h := wronskian.degree_lt_add ha hb
  rw [Polynomial.degree_eq_natDegree hw, Polynomial.degree_eq_natDegree ha,
    Polynomial.degree_eq_natDegree hb] at h
  exact_mod_cast h


-- @@ L89-89 verbatim
end wronskian


-- @@ L91-91 verbatim
end LeanPolyABC
