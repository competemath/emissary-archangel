import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-14 verbatim
/-!
# Additive group law for the polynomial exponential of a derivation

For any polynomial algebra map whose coefficients are the factorially divided
iterates of a derivation, this file proves the iterative coefficient law. The
construction of the polynomial map from local nilpotence is kept separate.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace StableCoordinate.LNDExponentialLaw


-- @@ L20-20 verbatim
open Polynomial


-- @@ L22-22 verbatim
variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]


-- @@ L24-31 verbatim
omit [CharZero k] in
lemma iterate_smul (D : Derivation k A A) (n : ℕ) (r : k) (a : A) :
    ((D : A → A)^[n]) (r • a) = r • ((D : A → A)^[n]) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    exact D.toLinearMap.map_smul r _


-- @@ L33-41 verbatim
lemma inv_factorial_mul_inv_factorial (n m : ℕ) :
    (n.factorial : k)⁻¹ * (m.factorial : k)⁻¹ =
      ((n + m).choose n : k) * ((n + m).factorial : k)⁻¹ := by
  have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hm : (m.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hnm : ((n + m).factorial : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + m))
  rw [Nat.cast_add_choose]
  field_simp


-- @@ L43-54 verbatim
/-- The coefficient law of the additive group, derived from divided iterates. -/
theorem coefficient_iterative
    (D : Derivation k A A) (E : A →ₐ[k] A[X])
    (hE : ∀ a n, (E a).coeff n = (n.factorial : k)⁻¹ • ((D : A → A)^[n]) a)
    (a : A) (n m : ℕ) :
    (E ((E a).coeff m)).coeff n =
      (n + m).choose n • (E a).coeff (n + m) := by
  simp only [hE, iterate_smul, smul_smul]
  rw [← Function.iterate_add_apply]
  rw [inv_factorial_mul_inv_factorial]
  rw [mul_smul]
  exact Nat.cast_smul_eq_nsmul k _ _


-- @@ L56-62 verbatim
omit [CharZero k] in
/-- Normalization at the identity of the additive group. -/
theorem coefficient_zero
    (D : Derivation k A A) (E : A →ₐ[k] A[X])
    (hE : ∀ a n, (E a).coeff n = (n.factorial : k)⁻¹ • ((D : A → A)^[n]) a)
    (a : A) : (E a).coeff 0 = a := by
  simp [hE]


-- @@ L64-70 verbatim
omit [CharZero k] in
/-- Extracting the linear coefficient recovers the infinitesimal derivation. -/
theorem coefficient_one
    (D : Derivation k A A) (E : A →ₐ[k] A[X])
    (hE : ∀ a n, (E a).coeff n = (n.factorial : k)⁻¹ • ((D : A → A)^[n]) a)
    (a : A) : (E a).coeff 1 = D a := by
  simp [hE]


-- @@ L72-77 verbatim
omit [CharZero k] in
lemma iterate_zero (D : Derivation k A A) (n : ℕ) :
    ((D : A → A)^[n]) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_zero]


-- @@ L79-83 verbatim
omit [CharZero k] in
lemma iterate_eq_zero_of_pos (D : Derivation k A A) {a : A}
    (ha : D a = 0) {n : ℕ} (hn : 0 < n) : ((D : A → A)^[n]) a = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [Function.iterate_succ_apply, ha, iterate_zero]


-- @@ L85-101 verbatim
omit [CharZero k] in
/-- Invariants of the infinitesimal derivation are exactly fixed elements of its exponential. -/
theorem fixed_iff
    (D : Derivation k A A) (E : A →ₐ[k] A[X])
    (hE : ∀ a n, (E a).coeff n = (n.factorial : k)⁻¹ • ((D : A → A)^[n]) a)
    (a : A) : E a = C a ↔ D a = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun q : A[X] => q.coeff 1) h
    simpa only [coefficient_one D E hE, coeff_C, one_ne_zero, ite_false] using h1
  · intro h
    ext n
    cases n with
    | zero => simp only [coefficient_zero D E hE, coeff_C, ite_true]
    | succ n =>
      rw [hE, iterate_eq_zero_of_pos D h (Nat.succ_pos n), smul_zero]
      simp


-- @@ L103-109 verbatim
omit [CharZero k] in
/-- Evaluation at parameter zero is the identity. -/
theorem eval_zero
    (D : Derivation k A A) (E : A →ₐ[k] A[X])
    (hE : ∀ a n, (E a).coeff n = (n.factorial : k)⁻¹ • ((D : A → A)^[n]) a)
    (a : A) : (E a).eval 0 = a := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using coefficient_zero D E hE a


-- @@ L111-111 verbatim
end StableCoordinate.LNDExponentialLaw


-- @@ L113-113 verbatim
end


-- @@ L115-115 verbatim
end OAI
