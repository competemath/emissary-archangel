import OAI.Algebra.AffineCancellation.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.LaurentDerivation

-- @@ L8-8 verbatim
open LaurentPolynomial

-- @@ L9-9 verbatim
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

-- @@ L10-12 verbatim
def linear (D : Derivation k R R) : LaurentPolynomial R →ₗ[k] LaurentPolynomial R :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap D.toLinearMap ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

-- @@ L13-18 verbatim
@[simp] lemma linear_single (D : Derivation k R R) (n : ℤ) (r : R) :
    linear D (C r*T n)=C (D r)*T n := by
  rw [← single_eq_C_mul_T,← single_eq_C_mul_T]
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapRange D (map_zero D) (Finsupp.single n r)=Finsupp.single n (D r)
  exact Finsupp.mapRange_single

-- @@ L19-30 verbatim
lemma linear_mul (D : Derivation k R R) (r s : LaurentPolynomial R) :
    linear D (r*s)=r*linear D s+s*linear D r := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [add_mul,map_add,hr,hs]; ring
  | C_mul_T n a =>
    induction s using LaurentPolynomial.induction_on' with
    | add r s hr hs => simp only [mul_add,map_add,hr,hs]; ring
    | C_mul_T m b =>
      have he : C a*T n*(C b*T m)=C (a*b)*T (n+m) := by rw [map_mul,T_add]; ring
      rw [he,linear_single,linear_single,linear_single,Derivation.leibniz,
        map_add,smul_eq_mul,smul_eq_mul,map_mul,map_mul,T_add]
      ring


-- @@ L32-33 verbatim
def extension (D : Derivation k R R) : Derivation k (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' (linear D) (by intro r s; exact linear_mul D r s)

-- @@ L34-35 verbatim
@[simp] lemma extension_monomial (D : Derivation k R R) (n : ℤ) (r : R) :
    extension D (C r*T n)=C (D r)*T n := linear_single D n r

-- @@ L36-37 verbatim
@[simp] lemma extension_C (D : Derivation k R R) (r : R) : extension D (C r)=C (D r) := by
  simpa using extension_monomial D 0 r

-- @@ L38-39 verbatim
@[simp] lemma extension_T (D : Derivation k R R) (n : ℤ) : extension D (T n)=0 := by
  simpa using extension_monomial D n 1

-- @@ L40-45 verbatim
lemma iterate_monomial (D : Derivation k R R) (n : ℤ) (r : R) (i : ℕ) :
    (extension D : LaurentPolynomial R → LaurentPolynomial R)^[i] (C r*T n)=
      C ((D : R → R)^[i] r)*T n := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih,extension_monomial,Function.iterate_succ_apply']

-- @@ L46-66 verbatim
lemma locallyNilpotent (D : Derivation k R R)
    (hD : ∀ r : R, ∃ n, (D : R → R)^[n] r=0) :
    ∀ p : LaurentPolynomial R, ∃ n,
      (extension D : LaurentPolynomial R → LaurentPolynomial R)^[n] p=0 := by
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    refine ⟨n+m,?_⟩
    have hp' : (extension D : LaurentPolynomial R → LaurentPolynomial R)^[n+m] p=0 := by
      rw [Nat.add_comm,Function.iterate_add_apply,hn]
      simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using ((extension D).toLinearMap ^ m).map_zero
    have hq' : (extension D : LaurentPolynomial R → LaurentPolynomial R)^[n+m] q=0 := by
      rw [Function.iterate_add_apply,hm]
      simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using ((extension D).toLinearMap ^ n).map_zero
    have he := ((extension D).toLinearMap ^ (n+m)).map_add p q
    simpa only [Module.End.pow_apply, Derivation.coeFn_coe,hp',hq',add_zero] using he
  | C_mul_T n r =>
    obtain ⟨m,hm⟩ := hD r
    exact ⟨m,by rw [iterate_monomial,hm,map_zero,zero_mul]⟩

-- @@ L67-67 verbatim
end ComplexCancellation.LaurentDerivation


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
