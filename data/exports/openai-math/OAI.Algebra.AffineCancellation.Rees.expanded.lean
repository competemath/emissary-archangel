import OAI.Algebra.AffineCancellation.Cylinder
import OAI.Algebra.AffineCancellation.Dimension


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace ComplexCancellation.Rees

-- @@ L9-9 verbatim
open MvPolynomial

-- @@ L10-10 verbatim
abbrev Poly := MvPolynomial (Fin 6) ℂ

-- @@ L11-11 verbatim
def xp : Poly := X 2^2+X 3^3+X 1^2*X 4

-- @@ L12-12 verbatim
def relation : Poly := xp^2*X 4-(1+2*X 2*xp)*X 5-X 1^2*X 5^2-X 0^3*X 1*X 3

-- @@ L13-13 verbatim
abbrev B := Poly ⧸ Ideal.span {relation}

-- @@ L14-14 verbatim
def π : Poly →ₐ[ℂ] B := Ideal.Quotient.mkₐ ℂ _

-- @@ L15-15 verbatim
def q : B := π (X 0)

-- @@ L16-16 verbatim
lemma relation_zero : π relation=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

-- @@ L17-21 verbatim
lemma q_regular : IsLeftRegular q := by
  apply Cylinder.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 6 => if i=5 then (1:ℂ) else 0)) h
  norm_num [relation,xp,Fin.ext_iff] at he

-- @@ L22-22 verbatim
abbrev L := LaurentPolynomial A

-- @@ L23-23 verbatim
def c : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L

-- @@ L24-24 verbatim
def aπ : P →ₐ[ℂ] A := Ideal.Quotient.mkₐ ℂ _

-- @@ L25-25 verbatim
def a (i : Fin 5) : L := c (aπ (X i))

-- @@ L26-27 verbatim
def values : Fin 6 → L := ![LaurentPolynomial.T 1,a 0*LaurentPolynomial.T (-1),
  a 1,a 2,a 3*LaurentPolynomial.T 2,a 4*LaurentPolynomial.T 2]

-- @@ L28-28 verbatim
def eval : Poly →ₐ[ℂ] L := aeval values

-- @@ L29-35 verbatim
lemma eval_xp : eval xp = c (aπ ComplexCancellation.x) := by
  simp only [xp,eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
    ComplexCancellation.x,ComplexCancellation.s,ComplexCancellation.p,ComplexCancellation.u,
    ComplexCancellation.F,map_add,map_mul,map_pow,a]
  have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
    rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
  linear_combination c (aπ (X 0))^2*c (aπ (X 3))*ht

-- @@ L36-52 verbatim
lemma eval_relation : eval relation = 0 := by
  have h : c (aπ H) = 0 := by
    rw [show aπ H=0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),map_zero]
  have hh : eval relation = c (aπ H)*LaurentPolynomial.T 2 := by
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,eval_xp]
    simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [H,ComplexCancellation.F,ComplexCancellation.J,ComplexCancellation.p,
      ComplexCancellation.s,ComplexCancellation.u,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,a]
    have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    have ht' : (LaurentPolynomial.T 1:L)^3*LaurentPolynomial.T (-1)=LaurentPolynomial.T 2 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    linear_combination
      -(c (aπ (X 0)))^2*c (aπ (X 4))^2*LaurentPolynomial.T 2*ht -
      c (aπ (X 0))*c (aπ (X 2))*ht'

  rw [hh,h,zero_mul]

-- @@ L53-56 verbatim
def embedding : B →ₐ[ℂ] L := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])

-- @@ L57-57 verbatim
@[simp] lemma embedding_π (r : Poly) : embedding (π r)=eval r := Ideal.Quotient.lift_mk _ _ _


-- @@ L59-59 verbatim
abbrev Bq := Localization.Away q

-- @@ L60-60 verbatim
def loc : B →ₐ[ℂ] Bq := IsScalarTower.toAlgHom ℂ B Bq

-- @@ L61-61 verbatim
def Q : Bqˣ := (IsLocalization.Away.algebraMap_isUnit q).unit

-- @@ L62-62 verbatim
lemma Q_val : (Q : Bq)=loc q := IsUnit.unit_spec _

-- @@ L63-66 verbatim
lemma loc_injective : Function.Injective loc := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers q) Bq
  rintro r ⟨n,rfl⟩
  exact isLeftRegular_iff_isRegular.mp (q_regular.pow n)

-- @@ L67-68 verbatim
def backValues : Fin 5 → Bq := ![(Q:Bq)*loc (π (X 1)),loc (π (X 2)),
  loc (π (X 3)),(↑(Q⁻¹):Bq)^2*loc (π (X 4)),(↑(Q⁻¹):Bq)^2*loc (π (X 5))]

-- @@ L69-69 verbatim
def backEval : P →ₐ[ℂ] Bq := aeval backValues

-- @@ L70-76 verbatim
lemma backEval_x : backEval ComplexCancellation.x = loc (π xp) := by
  simp only [ComplexCancellation.x,ComplexCancellation.p,ComplexCancellation.s,
    ComplexCancellation.u,ComplexCancellation.F,backEval,map_add,map_mul,map_pow,aeval_X,
    backValues,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,xp]
  simp only [mul_pow]
  have h : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
  linear_combination loc (π (X 1))^2*loc (π (X 4))*h

-- @@ L77-92 verbatim
lemma backEval_H : backEval H=0 := by
  have h : loc (π relation)=0 := by rw [relation_zero,map_zero]
  have he : (Q:Bq)^2*backEval H=loc (π relation) := by
    simp only [H,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,backEval_x]
    simp only [ComplexCancellation.p,ComplexCancellation.s,ComplexCancellation.u,
      ComplexCancellation.F,ComplexCancellation.J,backEval,aeval_X,backValues,
      Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat]
    rw [show loc (π (X 0))=(Q:Bq) from Q_val.symm]
    have h2 : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    have h4 : (Q:Bq)^4*(↑(Q⁻¹):Bq)^4=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    linear_combination
      (loc (π xp)^2*loc (π (X 4))-(1+2*loc (π (X 2))*loc (π xp))*loc (π (X 5)))*h2-
      loc (π (X 1))^2*loc (π (X 5))^2*h4
  apply (Q.isUnit.pow 2).mul_right_inj.mp
  rw [mul_zero,he,h]

-- @@ L93-96 verbatim
def backCoefficients : A →ₐ[ℂ] Bq := Ideal.Quotient.liftₐ _ backEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,backEval_H,zero_mul])

-- @@ L97-98 verbatim
@[simp] lemma backCoefficients_aπ (r : P) : backCoefficients (aπ r)=backEval r :=
  Ideal.Quotient.lift_mk _ _ _

-- @@ L99-104 verbatim
def backward : L →ₐ[ℂ] Bq where
  __ := LaurentPolynomial.eval₂ backCoefficients.toRingHom Q
  commutes' r := by
    change LaurentPolynomial.eval₂ backCoefficients.toRingHom Q (LaurentPolynomial.C (algebraMap ℂ A r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact backCoefficients.commutes r

-- @@ L105-115 verbatim
lemma backward_embedding : backward.comp embedding=loc := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward (eval (X i))=loc (π (X i))
  fin_cases i <;> simp [eval,values,Matrix.cons_val,backward,a,c,backEval,backValues,
    backCoefficients_aπ,IsScalarTower.toAlgHom]
  · exact Q_val
  · rw [mul_right_comm,Units.mul_inv,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]

-- @@ L116-119 verbatim
lemma embedding_injective : Function.Injective embedding := by
  apply Function.Injective.of_comp (f := backward)
  rw [← AlgHom.coe_comp,backward_embedding]
  exact loc_injective

-- @@ L120-120 verbatim
instance : IsDomain B := Function.Injective.isDomain embedding embedding_injective

-- @@ L121-121 verbatim
instance : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B

-- @@ L122-122 verbatim
end ComplexCancellation.Rees


-- @@ L124-124 verbatim
end


-- @@ L126-126 verbatim
end OAI
