import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-13 verbatim
/-!
# Explicit polynomial exponential shift

This file proves the exponential substitution used in Section 2 of the source,
without presupposing any locally nilpotent derivation infrastructure.  The six
variables are ordered `p, s, u, F, J, w`.  All formulas work over any commutative
ring: no characteristic-zero or field hypothesis is required for this step.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.ExponentialShift


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
variable (k : Type*) [CommRing k]


-- @@ L21-21 verbatim
abbrev P := MvPolynomial (Fin 6) k


-- @@ L23-23 verbatim
noncomputable def p : P k := X 0

-- @@ L24-24 verbatim
noncomputable def s : P k := X 1

-- @@ L25-25 verbatim
noncomputable def u : P k := X 2

-- @@ L26-26 verbatim
noncomputable def F : P k := X 3

-- @@ L27-27 verbatim
noncomputable def J : P k := X 4

-- @@ L28-28 verbatim
noncomputable def w : P k := X 5


-- @@ L30-30 verbatim
noncomputable def x : P k := s k ^ 2 - u k ^ 2 + p k * F k

-- @@ L31-32 verbatim
noncomputable def H : P k := x k ^ 2 * F k - (1 + 2 * s k * x k) * J k -
  p k * J k ^ 2 - u k


-- @@ L34-34 verbatim
noncomputable def t (c : k) : P k := C c * w k

-- @@ L35-35 verbatim
noncomputable def d (c : k) : P k := 2 * u k * t k c - p k * t k c ^ 2


-- @@ L37-43 verbatim
noncomputable def substitution (c : k) : Fin 6 → P k :=
  ![p k,
    s k + p k * x k * d k c,
    u k - p k * t k c,
    F k - (2 * s k * x k + 1) * d k c - p k * x k ^ 2 * d k c ^ 2,
    J k - x k ^ 2 * d k c,
    w k]


-- @@ L45-46 verbatim
noncomputable def shift (c : k) : P k →ₐ[k] P k :=
  aeval (substitution k c)


-- @@ L48-49 verbatim
@[simp] theorem shift_p (c : k) : shift k c (p k) = p k := by
  simp [shift, p, substitution]

-- @@ L50-51 verbatim
@[simp] theorem shift_s (c : k) : shift k c (s k) = s k + p k * x k * d k c := by
  simp [shift, s, substitution]

-- @@ L52-53 verbatim
@[simp] theorem shift_u (c : k) : shift k c (u k) = u k - p k * t k c := by
  simp [shift, u, substitution]

-- @@ L54-56 verbatim
@[simp] theorem shift_F (c : k) : shift k c (F k) =
    F k - (2 * s k * x k + 1) * d k c - p k * x k ^ 2 * d k c ^ 2 := by
  simp [shift, F, substitution]

-- @@ L57-58 verbatim
@[simp] theorem shift_J (c : k) : shift k c (J k) = J k - x k ^ 2 * d k c := by
  simp [shift, J, substitution]

-- @@ L59-60 verbatim
@[simp] theorem shift_w (c : k) : shift k c (w k) = w k := by
  simp [shift, w, substitution]

-- @@ L61-62 verbatim
@[simp] theorem shift_t (c b : k) : shift k c (t k b) = t k b := by
  simp [t, shift, w, substitution]

-- @@ L63-64 verbatim
@[simp] theorem t_neg (c : k) : t k (-c) = -t k c := by
  simp [t]


-- @@ L66-73 verbatim
private theorem quadratic_invariant {A : Type*} [CommRing A]
    (p s u F t : A) :
    let x := s ^ 2 - u ^ 2 + p * F
    let d := 2 * u * t - p * t ^ 2
    (s + p * x * d) ^ 2 - (u - p * t) ^ 2 +
      p * (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) = x := by
  dsimp
  ring


-- @@ L75-77 verbatim
@[simp] theorem shift_x (c : k) : shift k c (x k) = x k := by
  simp only [x, map_add, map_sub, map_pow, map_mul, shift_s, shift_u, shift_p, shift_F]
  exact quadratic_invariant (p k) (s k) (u k) (F k) (t k c)


-- @@ L79-81 verbatim
@[simp] theorem shift_d_neg (c : k) : shift k c (d k (-c)) = -d k c := by
  simp only [d, map_sub, map_mul, map_ofNat, map_pow, shift_u, shift_t, shift_p, t_neg, map_neg]
  ring


-- @@ L83-86 verbatim
private theorem inverse_F {A : Type*} [CommRing A] (p s F x d : A) :
    (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) -
      (2 * (s + p * x * d) * x + 1) * -d - p * x ^ 2 * (-d) ^ 2 = F := by
  ring


-- @@ L88-109 verbatim
@[simp] theorem shift_comp_neg (c : k) :
    (shift k c).comp (shift k (-c)) = AlgHom.id k (P k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change shift k c (shift k (-c) (p k)) = p k
    simp
  · change shift k c (shift k (-c) (s k)) = s k
    simp only [shift_s, map_add, map_mul, shift_p, shift_x, shift_d_neg]
    ring
  · change shift k c (shift k (-c) (u k)) = u k
    simp only [shift_u, map_sub, map_mul, shift_p, shift_t, t_neg, map_neg]
    ring
  · change shift k c (shift k (-c) (F k)) = F k
    simp only [shift_F, map_sub, map_add, map_mul, map_ofNat, map_one, map_pow,
      shift_s, shift_x, shift_d_neg, shift_p]
    exact inverse_F (p k) (s k) (F k) (x k) (d k c)
  · change shift k c (shift k (-c) (J k)) = J k
    simp only [shift_J, map_sub, map_mul, map_pow, shift_x, shift_d_neg]
    ring
  · change shift k c (shift k (-c) (w k)) = w k
    simp


-- @@ L111-114 verbatim
/-- The explicit exponential substitution, with inverse obtained by negating its parameter. -/
noncomputable def shiftEquiv (c : k) : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (shift k c) (shift k (-c)) (shift_comp_neg k c)
    (by simpa only [neg_neg] using shift_comp_neg k (-c))


-- @@ L116-117 verbatim
@[simp] theorem shiftEquiv_apply (c : k) (a : P k) :
    shiftEquiv k c a = shift k c a := rfl


-- @@ L119-125 verbatim
private theorem equation_shift {A : Type*} [CommRing A]
    (p s u F J x t d : A) :
    x ^ 2 * (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) -
      (1 + 2 * (s + p * x * d) * x) * (J - x ^ 2 * d) -
      p * (J - x ^ 2 * d) ^ 2 - (u - p * t) =
      (x ^ 2 * F - (1 + 2 * s * x) * J - p * J ^ 2 - u) + p * t := by
  ring


-- @@ L127-131 verbatim
/-- The crucial equation transport: the automorphism adds `p * c * w` to `H`. -/
theorem shift_H (c : k) : shift k c (H k) = H k + p k * t k c := by
  simp only [H, map_sub, map_mul, map_add, map_pow, map_one, map_ofNat,
    shift_x, shift_F, shift_s, shift_J, shift_p, shift_u]
  exact equation_shift (p k) (s k) (u k) (F k) (J k) (x k) (t k c) (d k c)


-- @@ L133-139 verbatim
/-- Section 2's `exp(w Δ)` is an actual algebra automorphism fixing `p` and
sending `H` to `H + p*w`. -/
theorem exponential_shift_exists :
    ∃ e : P k ≃ₐ[k] P k, e (p k) = p k ∧ e (H k) = H k + p k * w k := by
  refine ⟨shiftEquiv k 1, ?_, ?_⟩
  · simp
  · simpa [t] using shift_H k 1


-- @@ L141-141 verbatim
end StableCoordinate.ExponentialShift


-- @@ L143-143 verbatim
end OAI
