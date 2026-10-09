import OAI.Algebra.AffineCancellation.ModificationGrading
import OAI.Algebra.AffineCancellation.PolynomialDerivation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace ComplexCancellation.AffineModification

-- @@ L9-9 verbatim
open MvPolynomial

-- @@ L10-10 verbatim
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

-- @@ L11-11 verbatim
variable (v : R) (hv : v ≠ 0)

-- @@ L12-17 verbatim
lemma coefficient_injective : Function.Injective (algebraMap R (T R v)) := by
  apply Function.Injective.of_comp (f := embedding R v)
  intro r s he
  change embedding R v (algebraMap R (T R v) r)=embedding R v (algebraMap R (T R v) s) at he
  rw [AlgHom.commutes,AlgHom.commutes] at he
  exact ((RatFunc.C_injective).comp (IsFractionRing.injective R (F R))) he

-- @@ L18-23 verbatim
lemma τ_nonzero : τ R v ≠ 0 := by
  intro h
  have he := congrArg (embedding R v) h
  have he' : (RatFunc.X : K R)=0 := by
    simpa [τ,eval,values] using he
  exact RatFunc.X_ne_zero he'

-- @@ L24-29 verbatim
include hv in
lemma V_nonzero : V R v ≠ 0 := by
  intro h
  have he := equation R v
  rw [h,mul_zero] at he
  exact hv ((coefficient_injective v) (he.symm.trans (map_zero _).symm))


-- @@ L31-31 verbatim
def coefficientHom : R →ₐ[k] T R v := IsScalarTower.toAlgHom k R (T R v)

-- @@ L32-34 verbatim
omit [CharZero k] in
lemma coefficientHom_injective : Function.Injective (coefficientHom (k := k) v) :=
  coefficient_injective v


-- @@ L36-37 verbatim
def eulerPoly (H : Derivation k R R) : Derivation k (P R) (P R) :=
  PolynomialDerivation.mv H ![0,2*X 1]

-- @@ L38-44 verbatim
omit [CharZero k] [IsDomain R] in
lemma eulerPoly_relation (H : Derivation k R R) (hH : H v=2*v) :
    eulerPoly H (rel R v)=2*rel R v := by
  simp only [rel,eulerPoly,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
    PolynomialDerivation.mv_X,PolynomialDerivation.mv_C,hH,map_mul,map_ofNat,
    Matrix.cons_val_zero,Matrix.cons_val_one,smul_eq_mul]
  ring


-- @@ L46-50 verbatim
def euler (H : Derivation k R R) (hH : H v=2*v) : Derivation k (T R v) (T R v) :=
  QuotientDerivation.derivation _ (eulerPoly H)
    (QuotientDerivation.span_singleton_stable _ (by
      rw [eulerPoly_relation v H hH]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))

-- @@ L51-53 verbatim
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_π (H : Derivation k R R) (hH : H v=2*v) (p : P R) :
    euler v H hH (π R v p)=π R v (eulerPoly H p) := rfl

-- @@ L54-59 verbatim
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_coefficient (H : Derivation k R R) (hH : H v=2*v) (r : R) :
    euler v H hH (coefficientHom (k := k) v r)=coefficientHom (k := k) v (H r) := by
  change euler v H hH (π R v (C r))=π R v (C (H r))
  rw [euler_π]
  simp [eulerPoly]

-- @@ L60-62 verbatim
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_τ (H : Derivation k R R) (hH : H v=2*v) : euler v H hH (τ R v)=0 := by
  simp [τ,eulerPoly]

-- @@ L63-65 verbatim
omit [CharZero k] [IsDomain R] in
@[simp] lemma euler_V (H : Derivation k R R) (hH : H v=2*v) : euler v H hH (V R v)=2*V R v := by
  simp only [V,euler_π,eulerPoly,PolynomialDerivation.mv_X,Matrix.cons_val_one,Matrix.cons_val_zero,map_mul,map_ofNat]

-- @@ L66-76 verbatim
omit [CharZero k] [IsDomain R] in
lemma euler_monomial (H : Derivation k R R) (hH : H v=2*v) (i h : ℕ) :
    euler v H hH (τ R v^i*V R v^h)=(2*h:ℕ)*(τ R v^i*V R v^h) := by
  simp only [Derivation.leibniz,Derivation.leibniz_pow,euler_τ,euler_V,
    smul_eq_mul,mul_zero,add_zero,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  by_cases hh : h=0
  · subst h; simp
  · have he : V R v^(h-1)*V R v=V R v^h := by rw [← pow_succ]; congr 1; omega
    calc
      _ = (2*(h : T R v))*(τ R v^i*(V R v^(h-1)*V R v)) := by ring
      _ = _ := by rw [he]


-- @@ L78-94 verbatim
omit [CharZero k] [IsDomain R] in
lemma derivation_zero_of_generators (D : Derivation k (T R v) (T R v))
    (hc : ∀ r, D (coefficientHom (k := k) v r)=0)
    (hτ : D (τ R v)=0) (hV : D (V R v)=0) : D=0 := by
  apply Derivation.ext
  intro r
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective R (Ideal.span {rel R v}) r
  change D (π R v r)=0
  induction r using MvPolynomial.induction_on with
  | C r => exact hc r
  | add r s hr hs => simp only [map_add,hr,hs,add_zero]
  | mul_X r i hr =>
    have hi : D (π R v (X i))=0 := by
      fin_cases i
      · exact hτ
      · exact hV
    simp only [map_mul,Derivation.leibniz,hr,hi,smul_zero,add_zero]

-- @@ L95-95 verbatim
end ComplexCancellation.AffineModification


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
end OAI
