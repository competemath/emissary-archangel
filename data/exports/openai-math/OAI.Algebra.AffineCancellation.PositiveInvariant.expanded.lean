import OAI.Algebra.AffineCancellation.ReesGrading


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation.LND

-- @@ L8-8 verbatim
variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

-- @@ L9-13 verbatim
def conjugate (e : R ≃ₐ[k] S) (D : Derivation k S S) : Derivation k R R :=
  Derivation.mk' (e.symm.toLinearMap ∘ₗ D.toLinearMap ∘ₗ e.toLinearMap) (by
    intro r s
    change e.symm (D (e (r*s))) = r*e.symm (D (e s))+s*e.symm (D (e r))
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,AlgEquiv.symm_apply_apply])

-- @@ L14-15 verbatim
lemma conjugate_apply (e : R ≃ₐ[k] S) (D : Derivation k S S) (r : R) :
    conjugate e D r=e.symm (D (e r)) := rfl

-- @@ L16-20 verbatim
lemma conjugate_iterate (e : R ≃ₐ[k] S) (D : Derivation k S S) (r : R) (n : ℕ) :
    (conjugate e D : R → R)^[n] r=e.symm ((D : S → S)^[n] (e r)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,conjugate_apply,AlgEquiv.apply_symm_apply,Function.iterate_succ_apply']

-- @@ L21-25 verbatim
lemma conjugate_ln (e : R ≃ₐ[k] S) (D : Derivation k S S) (hD : LocallyNilpotent D) :
    LocallyNilpotent (conjugate e D) := by
  intro r
  obtain ⟨n,hn⟩ := hD (e r)
  exact ⟨n,by rw [conjugate_iterate,hn,map_zero]⟩

-- @@ L26-34 verbatim
lemma pderiv_ln {ι : Type*} (i : ι) : LocallyNilpotent (MvPolynomial.pderiv (R := k) i) := by
  classical
  apply mvPolynomial_locallyNilpotent
  intro j
  refine ⟨2,?_⟩
  simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,MvPolynomial.pderiv_X]
  by_cases hij : j=i
  · subst j; simp
  · simp [hij]

-- @@ L35-35 verbatim
end ComplexCancellation.LND


-- @@ L37-37 verbatim
namespace ComplexCancellation.Rees

-- @@ L38-38 verbatim
open MvPolynomial LaurentPolynomial

-- @@ L39-52 verbatim
lemma F_ne_zero : Degeneration.F ≠ 0 := by
  let f : Degeneration.P →ₐ[ℂ] ℂ := aeval (fun i => if i=3 then 1 else 0)
  have hf : f Degeneration.relation=0 := by
    norm_num [f,Degeneration.relation,Degeneration.xp,Fin.ext_iff]
  let g : Degeneration.G →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ _ f (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,hf,zero_mul])
  have hg : g Degeneration.F=1 := by
    change f (X 3)=1
    norm_num [f]
  intro hz
  rw [hz,map_zero] at hg
  exact zero_ne_one hg


-- @@ L54-66 verbatim
lemma coefficient_not_mem : c (aπ (X 3)) ∉ embedding.range := by
  rintro ⟨b,hb⟩
  change embedding b=c (aπ (X 3)) at hb
  have he : π (X 4)=q^2*b := by
    apply embedding_injective
    rw [map_mul,map_pow,embedding_q,T_pow,hb,embedding_π]
    simp only [eval,aeval_X,values,Matrix.cons_val]
    change c (aπ (X 3))*T 2=T 2*c (aπ (X 3))
    exact mul_comm (c (aπ (X 3))) (T 2 : L)
  have hr := congrArg red he
  simp only [map_mul,map_pow,red_q,zero_pow (by decide : 2 ≠ 0),zero_mul] at hr
  have hF : red (π (X 4))=Degeneration.F := by simp [redEval,redValues,Matrix.cons_val]
  exact F_ne_zero (hF.symm.trans hr)

-- @@ L67-82 verbatim
lemma positive_clear (r : A) (hr : c r ∉ embedding.range) :
    ∃ (i : ℤ) (s : B), 0 < i ∧ red s ≠ 0 ∧ embedding s=T i*c r := by
  have hcr : c r ≠ 0 := by
    intro hz
    apply hr
    rw [hz]
    exact embedding.range.zero_mem
  obtain ⟨i,s,hs,he⟩ := clear_order (c r) hcr
  refine ⟨i,s,?_,hs,he⟩
  by_contra hn
  have hi : 0 ≤ -i := by omega
  apply hr
  use q^(-i).toNat*s
  change embedding (q^(-i).toNat*s)=c r
  rw [map_mul,map_pow,embedding_q,T_pow,Int.toNat_of_nonneg hi,mul_one,he,← mul_assoc,← T_add]
  simp

-- @@ L83-97 verbatim
lemma polynomial_bad_coordinate (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ i : Fin 4, c (e.symm (X i)) ∉ embedding.range := by
  by_contra hn
  push Not at hn
  apply coefficient_not_mem
  rw [← e.symm_apply_apply (aπ (X 3))]
  generalize e (aπ (X 3))=r
  induction r using MvPolynomial.induction_on with
  | C z =>
    have he : c (e.symm (MvPolynomial.C z))=algebraMap ℂ L z := by
      rw [MvPolynomial.C_eq_algebraMap,AlgEquiv.commutes,c.commutes]
    rw [he]
    exact embedding.range.algebraMap_mem z
  | add r s hr hs => rw [map_add,map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul,map_mul]; exact mul_mem hr (hn i)

-- @@ L98-110 verbatim
lemma bad_invariant (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ (r : A) (D : Derivation ℂ A A), c r ∉ embedding.range ∧ LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D r=0 := by
  classical
  obtain ⟨i,hi⟩ := polynomial_bad_coordinate e
  obtain ⟨j,hj⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
  let D := LND.conjugate e (MvPolynomial.pderiv j)
  refine ⟨e.symm (X i),D,hi,LND.conjugate_ln e _ (LND.pderiv_ln j),?_,?_⟩
  · intro hz
    have he := DFunLike.congr_fun hz (e.symm (X j))
    have ho : D (e.symm (X j))=1 := by simp [D,LND.conjugate_apply]
    rw [ho,Derivation.zero_apply] at he
    exact one_ne_zero he
  · simp [D,LND.conjugate_apply,MvPolynomial.pderiv_X,hj]

-- @@ L111-118 verbatim
lemma positive_invariant_of_polynomial (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ (i : ℤ) (r : Degeneration.G) (D : Derivation ℂ Degeneration.G Degeneration.G),
      0 < i ∧ r ≠ 0 ∧ r ∈ Degeneration.pieces i ∧ LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D r=0 := by
  obtain ⟨r,D,hr,hD,hDn,hDr⟩ := bad_invariant e
  obtain ⟨i,s,hi,hs,he⟩ := positive_clear r hr
  obtain ⟨E,hE,hEn,hEq,hEs⟩ := scaled_restriction D hD hDn r hDr i s he
  obtain ⟨D',hD',hDn',hDr'⟩ := primitive_reduction E hE hEn hEq s hEs
  exact ⟨i,red s,D',hi,hs,red_monomial_mem s r i he,hD',hDn',hDr'⟩

-- @@ L119-119 verbatim
end ComplexCancellation.Rees


-- @@ L121-121 verbatim
end


-- @@ L123-123 verbatim
end OAI
