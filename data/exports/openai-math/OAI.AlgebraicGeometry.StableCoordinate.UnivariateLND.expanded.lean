import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-15 verbatim
/-!
# Locally nilpotent derivations in one polynomial variable

This file supplies the one-variable derivation step in the proof of
Proposition `prop:rigidity`, §5 of the source manuscript. Over an integral domain of
characteristic zero, a locally nilpotent derivation of `K[X]` maps `X` to
a constant. Local nilpotence is stated explicitly as the vanishing of a
sufficiently high iterate on every polynomial.
-/


-- @@ L17-17 verbatim
namespace StableCoordinate

-- @@ L18-18 verbatim
namespace UnivariateLND


-- @@ L20-20 verbatim
open Polynomial


-- @@ L22-22 verbatim
variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]


-- @@ L24-29 verbatim
omit [IsDomain K] [CharZero K] in
/-- A derivation of a univariate polynomial algebra is multiplication of
the ordinary derivative by its value on the indeterminate. -/
theorem apply_eq_derivative_mul (D : Derivation K K[X] K[X]) (p : K[X]) :
    D p = p.derivative * D X := by
  simpa using D.map_aeval p (X : K[X])


-- @@ L31-41 verbatim
/-- If the value on `X` has positive degree, a derivation preserves
positive degree. This excludes nilpotence on `X`. -/
theorem natDegree_apply_pos (D : Derivation K K[X] K[X])
    (hD : 0 < (D X).natDegree) {p : K[X]} (hp : 0 < p.natDegree) :
    0 < (D p).natDegree := by
  have hp' : p.derivative ≠ 0 := derivative_ne_zero.mpr (Nat.ne_of_gt hp)
  have hD' : D X ≠ 0 := by
    intro h
    simp [h] at hD
  rw [apply_eq_derivative_mul, natDegree_mul hp' hD', natDegree_derivative]
  omega


-- @@ L43-52 verbatim
/-- Every iterate on `X` retains positive degree if the value on `X`
has positive degree. -/
theorem natDegree_iterate_X_pos (D : Derivation K K[X] K[X])
    (hD : 0 < (D X).natDegree) (n : ℕ) :
    0 < (((D : K[X] → K[X])^[n]) X).natDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact natDegree_apply_pos D hD ih


-- @@ L54-63 verbatim
/-- Vanishing of one iterate on the indeterminate already forces a
univariate derivation's value on the indeterminate to have degree zero. -/
theorem natDegree_apply_X_eq_zero_of_iterate_eq_zero
    (D : Derivation K K[X] K[X])
    (hD : ∃ n : ℕ, ((D : K[X] → K[X])^[n]) X = 0) :
    (D X).natDegree = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := hD
  have hp := natDegree_iterate_X_pos D (Nat.pos_of_ne_zero h) n
  simp [hn] at hp


-- @@ L65-72 verbatim
/-- The needed rigidity fact: every locally nilpotent derivation of a
one-variable polynomial algebra over a characteristic-zero domain sends
the variable to a constant in the coefficient field. -/
theorem apply_X_eq_C_of_locallyNilpotent (D : Derivation K K[X] K[X])
    (hD : ∀ p : K[X], ∃ n : ℕ, ((D : K[X] → K[X])^[n]) p = 0) :
    D X = C ((D X).coeff 0) := by
  exact eq_C_of_natDegree_eq_zero
    (natDegree_apply_X_eq_zero_of_iterate_eq_zero D (hD X))


-- @@ L74-78 verbatim
/-- Existential form matching the source's statement `D(X) ∈ K`. -/
theorem exists_apply_X_eq_C_of_locallyNilpotent (D : Derivation K K[X] K[X])
    (hD : ∀ p : K[X], ∃ n : ℕ, ((D : K[X] → K[X])^[n]) p = 0) :
    ∃ c : K, D X = C c :=
  ⟨(D X).coeff 0, apply_X_eq_C_of_locallyNilpotent D hD⟩


-- @@ L80-80 verbatim
end UnivariateLND

-- @@ L81-81 verbatim
end StableCoordinate


-- @@ L83-83 verbatim
end OAI
