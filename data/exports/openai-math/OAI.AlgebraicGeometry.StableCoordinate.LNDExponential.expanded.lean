import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Choose.Cast


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# Polynomial exponentials of locally nilpotent derivations

The exponential of a locally nilpotent derivation in characteristic zero is
an actual polynomial algebra homomorphism, not a formal power series.  This
is the forward algebraic interface for the additive-action step in Section 4.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
namespace StableCoordinate.LNDExponential


-- @@ L19-19 verbatim
open Function Polynomial Finset


-- @@ L21-21 verbatim
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]


-- @@ L23-25 verbatim
/-- The factorially divided `n`th iterate of a derivation. -/
def dividedIterate (D : Derivation k A A) (a : A) (n : ℕ) : A :=
  ((n.factorial : k)⁻¹) • (D : A → A)^[n] a


-- @@ L27-35 verbatim
lemma dividedIterate_finiteSupport (D : Derivation k A A)
    (hD : IsLocallyNilpotent D) (a : A) :
    (Function.support (dividedIterate D a)).Finite := by
  obtain ⟨N, hN⟩ := hD a
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra h
  have hz := derivation_iterate_eq_zero_of_le D hN (Nat.le_of_not_gt h)
  exact hn (by simp [dividedIterate, hz])


-- @@ L37-40 verbatim
/-- A finite-support construction of `exp(T D)(a)`. -/
def polynomial (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) : A[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (dividedIterate D a) (dividedIterate_finiteSupport D hD a)))


-- @@ L42-45 verbatim
@[simp]
lemma coeff_polynomial (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (a : A) (n : ℕ) :
    (polynomial D hD a).coeff n = ((n.factorial : k)⁻¹) • (D : A → A)^[n] a := rfl


-- @@ L47-51 verbatim
lemma iterate_add (D : Derivation k A A) (n : ℕ) (a b : A) :
    (D : A → A)^[n] (a + b) = (D : A → A)^[n] a + (D : A → A)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]


-- @@ L53-57 verbatim
lemma iterate_smul (D : Derivation k A A) (n : ℕ) (c : k) (a : A) :
    (D : A → A)^[n] (c • a) = c • (D : A → A)^[n] a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, Derivation.map_smul]


-- @@ L59-62 verbatim
lemma polynomial_add (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a b : A) :
    polynomial D hD (a + b) = polynomial D hD a + polynomial D hD b := by
  ext n
  simp [smul_add]


-- @@ L64-67 verbatim
lemma polynomial_smul (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (c : k) (a : A) : polynomial D hD (c • a) = c • polynomial D hD a := by
  ext n
  rw [coeff_polynomial, Polynomial.coeff_smul, coeff_polynomial, iterate_smul, smul_comm]


-- @@ L69-77 verbatim
lemma polynomial_one (D : Derivation k A A) (hD : IsLocallyNilpotent D) :
    polynomial D hD 1 = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have hzero : (D : A → A)^[n + 1] 1 = 0 :=
      derivation_iterate_eq_zero_of_le D (m := 1) (by simp) (by omega)
    simp [hzero, Polynomial.coeff_one]


-- @@ L79-79 verbatim
variable [CharZero k]


-- @@ L81-88 verbatim
lemma inverse_factorial_mul_choose (i j : ℕ) :
    ((i + j).factorial : k)⁻¹ * ((i + j).choose i : k) =
      (i.factorial : k)⁻¹ * (j.factorial : k)⁻¹ := by
  rw [Nat.cast_add_choose]
  have hi : (i.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hij : ((i+j).factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp


-- @@ L90-102 verbatim
lemma dividedIterate_mul (D : Derivation k A A) (n : ℕ) (a b : A) :
    ((n.factorial : k)⁻¹) • (D : A → A)^[n] (a * b) =
    ∑ ij ∈ antidiagonal n,
      (((ij.1.factorial : k)⁻¹) • (D : A → A)^[ij.1] a) *
      (((ij.2.factorial : k)⁻¹) • (D : A → A)^[ij.2] b) := by
  rw [derivation_iterate_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  have hn : i + j = n := Finset.mem_antidiagonal.mp hij
  subst n
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inverse_factorial_mul_choose]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm ((i.factorial : k)⁻¹)]


-- @@ L104-107 verbatim
lemma polynomial_mul (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a b : A) :
    polynomial D hD (a * b) = polynomial D hD a * polynomial D hD b := by
  ext n
  simpa only [coeff_polynomial, Polynomial.coeff_mul] using dividedIterate_mul D n a b


-- @@ L109-120 verbatim
/-- The polynomial exponential is a coefficient-field algebra homomorphism. -/
def exponential (D : Derivation k A A) (hD : IsLocallyNilpotent D) : A →ₐ[k] A[X] where
  toFun := polynomial D hD
  map_one' := polynomial_one D hD
  map_mul' := polynomial_mul D hD
  map_zero' := by
    ext n
    simp [Function.iterate_fixed (map_zero D)]
  map_add' := polynomial_add D hD
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, polynomial_smul, polynomial_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm


-- @@ L122-126 verbatim
@[simp]
lemma coeff_exponential (D : Derivation k A A) (hD : IsLocallyNilpotent D)
    (a : A) (n : ℕ) :
    (exponential D hD a).coeff n = ((n.factorial : k)⁻¹) • (D : A → A)^[n] a :=
  coeff_polynomial D hD a n


-- @@ L128-130 verbatim
@[simp]
lemma coeff_exponential_zero (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (exponential D hD a).coeff 0 = a := by simp


-- @@ L132-134 verbatim
@[simp]
lemma coeff_exponential_one (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    (exponential D hD a).coeff 1 = D a := by simp


-- @@ L136-136 verbatim
end StableCoordinate.LNDExponential


-- @@ L138-138 verbatim
end


-- @@ L140-140 verbatim
end OAI
