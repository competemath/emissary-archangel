import OAI.Algebra.AffineCancellation.Clearing
import OAI.Algebra.AffineCancellation.DeterminantRigidity


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace ComplexCancellation.Quadric

-- @@ L9-9 verbatim
open MvPolynomial

-- @@ L10-10 verbatim
abbrev Poly := MvPolynomial (Fin 4) ℂ

-- @@ L11-11 verbatim
abbrev Base := MvPolynomial (Fin 3) ℂ

-- @@ L12-12 verbatim
abbrev K := FractionRing Base

-- @@ L13-13 verbatim
def relation : Poly := X 0*X 1-X 2*(X 2+1)

-- @@ L14-14 verbatim
abbrev R := Poly ⧸ Ideal.span {relation}

-- @@ L15-15 verbatim
def π : Poly →ₐ[ℂ] R := Ideal.Quotient.mkₐ ℂ _

-- @@ L16-16 verbatim
def x : R := π (X 0)

-- @@ L17-17 verbatim
def y : R := π (X 1)

-- @@ L18-18 verbatim
def z : R := π (X 2)

-- @@ L19-19 verbatim
def u : R := π (X 3)

-- @@ L20-20 verbatim
def s : R := y-x*(x-u^3)

-- @@ L21-21 verbatim
def f : R := x-s^2-u^3

-- @@ L22-22 verbatim
def g : R := z-s*x


-- @@ L24-24 verbatim
def baseEmbedding : Base →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Base K

-- @@ L25-25 verbatim
lemma baseEmbedding_injective : Function.Injective baseEmbedding := IsFractionRing.injective Base K

-- @@ L26-27 verbatim
lemma x_field_nonzero : baseEmbedding (X 0) ≠ 0 := by
  simpa only [map_zero] using baseEmbedding_injective.ne (X_ne_zero (0 : Fin 3))

-- @@ L28-30 verbatim
def values : Fin 4 → K := ![baseEmbedding (X 0),
  baseEmbedding (X 1)*(baseEmbedding (X 1)+1)/baseEmbedding (X 0),
  baseEmbedding (X 1),baseEmbedding (X 2)]

-- @@ L31-31 verbatim
def eval : Poly →ₐ[ℂ] K := aeval values

-- @@ L32-36 verbatim
lemma eval_relation : eval relation = 0 := by
  simp only [relation,eval,map_sub,map_mul,map_add,map_one,aeval_X,values,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [x_field_nonzero]
  ring


-- @@ L38-41 verbatim
def embedding : R →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])

-- @@ L42-42 verbatim
@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r := Ideal.Quotient.lift_mk _ _ _

-- @@ L43-46 verbatim
lemma equation : x*y=z*(z+1) := by
  apply sub_eq_zero.mp
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation,map_sub,map_mul,map_add,map_one,x,y,z] using h

-- @@ L47-51 verbatim
lemma x_regular : IsLeftRegular x := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 4 => if i=2 then (1:ℂ) else 0)) h
  norm_num [relation,Fin.ext_iff] at he


-- @@ L53-53 verbatim
def baseMap : Base →ₐ[ℂ] R := aeval ![x,z,u]

-- @@ L54-54 verbatim
lemma baseMap_X_zero : baseMap (X 0) = x := by simp [baseMap]

-- @@ L55-58 verbatim
lemma embedding_baseMap : embedding.comp baseMap = baseEmbedding := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap,x,z,u,eval,values]

-- @@ L59-68 verbatim
lemma clears : Clearing.subalgebra baseMap (X 0) = ⊤ := by
  apply Clearing.top_of_generators π (Ideal.Quotient.mkₐ_surjective ℂ _) _ _
  intro i
  fin_cases i
  · exact ⟨0,X 0,by simp [baseMap,x]⟩
  · refine ⟨1,X 1*(X 1+1),?_⟩
    simp only [pow_one,baseMap,map_mul,map_add,map_one,aeval_X]
    exact equation
  · exact ⟨0,X 1,by simp [baseMap,z]⟩
  · exact ⟨0,X 2,by simp [baseMap,u]⟩

-- @@ L69-73 verbatim
lemma embedding_injective : Function.Injective embedding := by
  apply Clearing.injective_of_clearing embedding baseMap (X 0)
  · rw [embedding_baseMap]; exact baseEmbedding_injective
  · rw [baseMap_X_zero]; exact x_regular
  · exact clears

-- @@ L74-74 verbatim
instance : IsDomain R := Function.Injective.isDomain embedding embedding_injective

-- @@ L75-78 verbatim
lemma baseMap_injective : Function.Injective baseMap := by
  apply Function.Injective.of_comp (f := embedding)
  rw [← AlgHom.coe_comp,embedding_baseMap]
  exact baseEmbedding_injective

-- @@ L79-81 verbatim
lemma x_ne_zero : x ≠ 0 := by
  rw [← baseMap_X_zero]
  simpa only [map_zero] using baseMap_injective.ne (X_ne_zero (0 : Fin 3))


-- @@ L83-83 verbatim
end ComplexCancellation.Quadric


-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
end OAI
