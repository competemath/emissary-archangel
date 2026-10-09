import OAI.Algebra.AffineCancellation.Quadric


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.Degeneration

-- @@ L8-8 verbatim
open MvPolynomial

-- @@ L9-9 verbatim
abbrev P := MvPolynomial (Fin 5) ℂ

-- @@ L10-10 verbatim
def xp : P := X 1^2+X 2^3+X 0^2*X 3

-- @@ L11-11 verbatim
def yp : P := X 1+xp*(xp-X 2^3)

-- @@ L12-12 verbatim
def zp : P := X 1*xp+X 0^2*X 4

-- @@ L13-13 verbatim
def relation : P := xp^2*X 3-(1+2*X 1*xp)*X 4-X 0^2*X 4^2

-- @@ L14-16 verbatim
lemma identity : xp*yp-zp*(zp+1)=X 0^2*relation := by
  simp only [yp,zp,relation,xp]
  ring

-- @@ L17-17 verbatim
abbrev G := P ⧸ Ideal.span {relation}

-- @@ L18-18 verbatim
def π : P →ₐ[ℂ] G := Ideal.Quotient.mkₐ ℂ _

-- @@ L19-19 verbatim
def p : G := π (X 0)

-- @@ L20-20 verbatim
def s : G := π (X 1)

-- @@ L21-21 verbatim
def u : G := π (X 2)

-- @@ L22-22 verbatim
def F : G := π (X 3)

-- @@ L23-23 verbatim
def J : G := π (X 4)

-- @@ L24-24 verbatim
def x : G := π xp

-- @@ L25-25 verbatim
def y : G := π yp

-- @@ L26-26 verbatim
def z : G := π zp

-- @@ L27-27 verbatim
lemma relation_zero : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

-- @@ L28-31 verbatim
lemma equation : x*y=z*(z+1) := by
  apply sub_eq_zero.mp
  have h := congrArg π identity
  simpa only [map_sub,map_mul,map_add,map_one,map_pow,relation_zero,mul_zero,x,y,z] using h


-- @@ L33-33 verbatim
def coeffEval : Quadric.Poly →ₐ[ℂ] G := aeval ![x,y,z,u]

-- @@ L34-35 verbatim
lemma coeffEval_relation : coeffEval Quadric.relation = 0 := by
  simpa [coeffEval,Quadric.relation,Matrix.cons_val] using sub_eq_zero.mpr equation

-- @@ L36-39 verbatim
def coefficientMap : Quadric.R →ₐ[ℂ] G := Ideal.Quotient.liftₐ _ coeffEval (by
  intro r hr
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,coeffEval_relation,zero_mul])

-- @@ L40-41 verbatim
@[simp] lemma coefficientMap_π (r : Quadric.Poly) : coefficientMap (Quadric.π r) = coeffEval r :=
  Ideal.Quotient.lift_mk _ _ _

-- @@ L42-42 verbatim
@[simp] lemma coefficientMap_x : coefficientMap Quadric.x=x := by simp [Quadric.x,coeffEval]

-- @@ L43-43 verbatim
@[simp] lemma coefficientMap_y : coefficientMap Quadric.y=y := by simp [Quadric.y,coeffEval]

-- @@ L44-44 verbatim
@[simp] lemma coefficientMap_z : coefficientMap Quadric.z=z := by simp [Quadric.z,coeffEval,Matrix.cons_val]

-- @@ L45-45 verbatim
@[simp] lemma coefficientMap_u : coefficientMap Quadric.u=u := by simp [Quadric.u,coeffEval,Matrix.cons_val]

-- @@ L46-49 verbatim
@[simp] lemma coefficientMap_s : coefficientMap Quadric.s=s := by
  simp only [Quadric.s,map_sub,map_mul,map_pow,coefficientMap_x,coefficientMap_y,coefficientMap_u]
  simp only [x,y,s,u,yp,map_add,map_mul,map_sub,map_pow]
  ring

-- @@ L50-53 verbatim
lemma coefficientMap_f : coefficientMap Quadric.f=p^2*F := by
  simp only [Quadric.f,map_sub,map_pow,coefficientMap_x,coefficientMap_s,coefficientMap_u]
  simp only [x,xp,map_add,map_mul,map_pow,s,u,p,F]
  ring

-- @@ L54-57 verbatim
lemma coefficientMap_g : coefficientMap Quadric.g=p^2*J := by
  simp only [Quadric.g,map_sub,map_mul,coefficientMap_z,coefficientMap_s,coefficientMap_x]
  simp only [z,zp,map_add,map_mul,map_pow,s,p,J,x]
  ring


-- @@ L59-59 verbatim
abbrev K₀ := FractionRing Quadric.R

-- @@ L60-60 verbatim
abbrev K := RatFunc K₀

-- @@ L61-61 verbatim
def ι : Quadric.R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Quadric.R K

-- @@ L62-63 verbatim
lemma ι_injective : Function.Injective ι :=
  (RatFunc.C_injective).comp (IsFractionRing.injective Quadric.R K₀)

-- @@ L64-64 verbatim
lemma τ_ne_zero : (RatFunc.X : K) ≠ 0 := RatFunc.X_ne_zero

-- @@ L65-66 verbatim
def values : Fin 5 → K := ![RatFunc.X,ι Quadric.s,ι Quadric.u,
  ι Quadric.f/RatFunc.X^2,ι Quadric.g/RatFunc.X^2]

-- @@ L67-67 verbatim
def eval : P →ₐ[ℂ] K := aeval values

-- @@ L68-73 verbatim
lemma eval_xp : eval xp=ι Quadric.x := by
  simp only [xp,eval,map_add,map_mul,map_pow,aeval_X,values,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [τ_ne_zero]
  simp only [Quadric.f,map_sub,map_pow]
  ring

-- @@ L74-78 verbatim
lemma eval_yp : eval yp=ι Quadric.y := by
  simp only [yp,map_add,map_mul,map_sub,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  simp only [Quadric.s,map_sub,map_mul,map_pow]
  ring

-- @@ L79-84 verbatim
lemma eval_zp : eval zp=ι Quadric.z := by
  simp only [zp,map_add,map_mul,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [τ_ne_zero]
  simp only [Quadric.g,map_sub,map_mul]
  ring

-- @@ L85-92 verbatim
lemma eval_relation : eval relation=0 := by
  have h := congrArg eval identity
  simp only [map_sub,map_mul,map_add,map_one,map_pow,eval_xp,eval_yp,eval_zp] at h
  have he : ι Quadric.x*ι Quadric.y-ι Quadric.z*(ι Quadric.z+1)=0 := by
    simpa only [map_mul,map_add,map_one] using congrArg ι Quadric.equation |> sub_eq_zero.mpr
  rw [he] at h
  have hp : eval (X 0) ≠ 0 := by simpa [eval,values] using τ_ne_zero
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hp)


-- @@ L94-97 verbatim
def embedding : G →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])

-- @@ L98-98 verbatim
@[simp] lemma embedding_π (r : P) : embedding (π r)=eval r := Ideal.Quotient.lift_mk _ _ _

-- @@ L99-112 verbatim
lemma embedding_coefficientMap : embedding.comp coefficientMap=ι := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change embedding (coefficientMap Quadric.x)=ι Quadric.x
    rw [coefficientMap_x,x,embedding_π,eval_xp]
  · change embedding (coefficientMap Quadric.y)=ι Quadric.y
    rw [coefficientMap_y,y,embedding_π,eval_yp]
  · change embedding (coefficientMap Quadric.z)=ι Quadric.z
    rw [coefficientMap_z,z,embedding_π,eval_zp]
  · change embedding (coefficientMap Quadric.u)=ι Quadric.u
    rw [coefficientMap_u,u,embedding_π]
    simp [eval,values,Matrix.cons_val]

-- @@ L113-116 verbatim
lemma coefficientMap_injective : Function.Injective coefficientMap := by
  apply Function.Injective.of_comp (f := embedding)
  rw [← AlgHom.coe_comp,embedding_coefficientMap]
  exact ι_injective

-- @@ L117-121 verbatim
lemma p_regular : IsLeftRegular p := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 5 => if i=4 then (1:ℂ) else 0)) h
  norm_num [relation,xp,Fin.ext_iff] at he


-- @@ L123-124 verbatim
def baseMap : Polynomial Quadric.R →ₐ[ℂ] G :=
  Polynomial.eval₂AlgHom coefficientMap p (fun _ => Commute.all _ _)

-- @@ L125-125 verbatim
lemma baseMap_X : baseMap Polynomial.X=p := by simp [baseMap]

-- @@ L126-126 verbatim
lemma baseMap_C (r : Quadric.R) : baseMap (Polynomial.C r)=coefficientMap r := by simp [baseMap]

-- @@ L127-129 verbatim
def baseEmbedding : Polynomial Quadric.R →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Polynomial K₀) K).comp
    (Polynomial.mapAlgHom (IsScalarTower.toAlgHom ℂ Quadric.R K₀))

-- @@ L130-132 verbatim
lemma baseEmbedding_injective : Function.Injective baseEmbedding :=
  (RatFunc.algebraMap_injective K₀).comp
    (Polynomial.map_injective _ (IsFractionRing.injective Quadric.R K₀))

-- @@ L133-145 verbatim
lemma embedding_baseMap : embedding.comp baseMap=baseEmbedding := by
  apply Polynomial.algHom_ext'
  · ext r
    change embedding (baseMap (Polynomial.C r))=baseEmbedding (Polynomial.C r)
    rw [baseMap_C]
    have h := DFunLike.congr_fun embedding_coefficientMap r
    simpa [baseEmbedding,ι,IsScalarTower.algebraMap_apply Quadric.R K₀ K,
      RatFunc.algebraMap_eq_C] using h
  · change embedding (baseMap Polynomial.X)=baseEmbedding Polynomial.X
    rw [baseMap_X]
    change eval (X 0)=algebraMap (Polynomial K₀) K (Polynomial.map (algebraMap Quadric.R K₀) Polynomial.X)
    rw [Polynomial.map_X,RatFunc.algebraMap_X]
    simp [eval,values]

-- @@ L146-154 verbatim
lemma clears : Clearing.subalgebra (S := Polynomial Quadric.R) baseMap Polynomial.X=⊤ := by
  apply Clearing.top_of_generators π (Ideal.Quotient.mkₐ_surjective ℂ _) _ _
  intro i
  fin_cases i
  · exact ⟨0,Polynomial.X,by simp [baseMap_X,p]⟩
  · exact ⟨0,Polynomial.C Quadric.s,by simp [baseMap_C,s]⟩
  · exact ⟨0,Polynomial.C Quadric.u,by simp [baseMap_C,u]⟩
  · exact ⟨2,Polynomial.C Quadric.f,by rw [baseMap_X,baseMap_C,coefficientMap_f]; rfl⟩
  · exact ⟨2,Polynomial.C Quadric.g,by rw [baseMap_X,baseMap_C,coefficientMap_g]; rfl⟩

-- @@ L155-159 verbatim
lemma embedding_injective : Function.Injective embedding := by
  apply Clearing.injective_of_clearing (S := Polynomial Quadric.R) embedding baseMap Polynomial.X
  · rw [embedding_baseMap]; exact baseEmbedding_injective
  · rw [baseMap_X]; exact p_regular
  · exact clears

-- @@ L160-160 verbatim
instance : IsDomain G := Function.Injective.isDomain embedding embedding_injective


-- @@ L162-162 verbatim
end ComplexCancellation.Degeneration


-- @@ L164-164 verbatim
end


-- @@ L166-166 verbatim
end OAI
