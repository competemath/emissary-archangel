import OAI.Geometry.HarmonicGrowth.LieGeneration


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Matrix

-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open scoped Topology

-- @@ L9-9 verbatim
open Filter

-- @@ L10-10 verbatim
open Matrix

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Matrix MvPolynomial

-- @@ L13-13 verbatim
open Matrix

-- @@ L14-14 verbatim
open scoped BigOperators


-- @@ L16-16 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L17-17 verbatim
open MvPolynomial Finsupp

-- @@ L18-18 verbatim
variable {σ : Type*} [Fintype σ]


-- @@ L20-21 verbatim
/-- The bilinear Fischer form, over the actual complex polynomial algebra. -/
def factorialWeight (d : σ →₀ ℕ) : ℂ := ∏ i : σ,(d i).factorial


-- @@ L23-25 verbatim
def fischer : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ (fun d => factorialWeight d • lcoeff ℂ d)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap


-- @@ L27-33 verbatim
lemma fischer_monomial (d : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fischer (monomial d c) Q = c*factorialWeight d*Q.coeff d := by
  change (Finsupp.linearCombination ℂ (fun e : σ →₀ ℕ =>
    factorialWeight e • lcoeff ℂ e) (single d c)) Q = _
  rw [Finsupp.linearCombination_single]
  change c*(factorialWeight d*Q.coeff d) = _
  ring


-- @@ L35-38 verbatim
lemma fischer_apply (P Q : MvPolynomial σ ℂ) :
    fischer P Q = ∑ d ∈ P.support,P.coeff d*factorialWeight d*Q.coeff d := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum,LinearMap.sum_apply,fischer_monomial]


-- @@ L40-51 verbatim
lemma fischer_symm (P Q : MvPolynomial σ ℂ) : fischer P Q = fischer Q P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    induction Q using MvPolynomial.induction_on' with
    | monomial e b =>
      simp only [fischer_monomial,coeff_monomial]
      by_cases h : d=e
      · subst e; simp only [ite_true]; ring
      · simp [h,Ne.symm h]
    | add Q R hq hr => simp only [map_add,LinearMap.add_apply,hq,hr]
  | add P R hp hr => simp only [map_add,LinearMap.add_apply,hp,hr]


-- @@ L53-66 verbatim
lemma factorialWeight_add_single (d : σ →₀ ℕ) (i : σ) :
    factorialWeight (d+single i 1) = ((d i:ℂ)+1)*factorialWeight d := by
  classical
  unfold factorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j : σ => ((d j).factorial:ℂ)) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, (((d+single i 1 : σ →₀ ℕ) j).factorial:ℂ)) =
      ∏ j ∈ Finset.univ.erase i, ((d j).factorial:ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Ne.symm (Finset.mem_erase.1 hj).1]
  rw [he]
  simp only [Finsupp.add_apply,single_eq_same,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring


-- @@ L68-76 verbatim
lemma fischer_mul_X (P Q : MvPolynomial σ ℂ) (i : σ) :
    fischer (P*X i) Q = fischer P (pderiv i Q) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [← pow_one (X i),← monomial_add_single,fischer_monomial,fischer_monomial,
      coeff_pderiv,factorialWeight_add_single]
    ring
  | add P R hp hr => simp only [add_mul,map_add,LinearMap.add_apply,hp,hr]


-- @@ L78-78 verbatim
def conjugate : MvPolynomial σ ℂ →+* MvPolynomial σ ℂ := MvPolynomial.map (starRingEnd ℂ)


-- @@ L80-82 verbatim
omit [Fintype σ] in
lemma coeff_conjugate (P : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (conjugate P).coeff d = star (P.coeff d) := by exact coeff_map (starRingEnd ℂ) P d


-- @@ L84-87 verbatim
omit [Fintype σ] in
lemma conjugate_involutive (P : MvPolynomial σ ℂ) : conjugate (conjugate P) = P := by
  ext d
  simp [coeff_conjugate]


-- @@ L89-91 verbatim
omit [Fintype σ] in
lemma conjugate_pderiv (P : MvPolynomial σ ℂ) (i : σ) :
    conjugate (pderiv i P) = pderiv i (conjugate P) := pderiv_map.symm


-- @@ L93-96 verbatim
lemma factorialWeight_re (d : σ →₀ ℕ) :
    (factorialWeight d).re = ∏ i : σ,((d i).factorial:ℝ) := by
  unfold factorialWeight
  rw [← Nat.cast_prod,Complex.natCast_re,Nat.cast_prod]


-- @@ L98-100 verbatim
lemma factorialWeight_im (d : σ →₀ ℕ) : (factorialWeight d).im = 0 := by
  unfold factorialWeight
  rw [← Nat.cast_prod,Complex.natCast_im]


-- @@ L102-104 verbatim
lemma factorialWeight_re_pos (d : σ →₀ ℕ) : 0 < (factorialWeight d).re := by
  rw [factorialWeight_re]
  exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (d i)


-- @@ L106-114 verbatim
lemma fischer_conjugate_re (P : MvPolynomial σ ℂ) :
    (fischer P (conjugate P)).re =
      ∑ d ∈ P.support,(factorialWeight d).re*Complex.normSq (P.coeff d) := by
  rw [fischer_apply]
  simp only [Complex.re_sum,coeff_conjugate]
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_right_comm,Complex.star_def,Complex.mul_conj]
  simp [Complex.mul_re,mul_comm]


-- @@ L116-126 verbatim
lemma fischer_definite {P : MvPolynomial σ ℂ} (h : fischer P (conjugate P) = 0) : P = 0 := by
  have he := congrArg Complex.re h
  rw [fischer_conjugate_re,Complex.zero_re] at he
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun d (_ : d ∈ P.support) =>
    mul_nonneg (factorialWeight_re_pos d).le (Complex.normSq_nonneg _))).1 he
  ext d
  rw [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  by_cases hd : d ∈ P.support
  · exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (hh d hd)).resolve_left
      (factorialWeight_re_pos d).ne')
  · exact MvPolynomial.notMem_support_iff.1 hd


-- @@ L128-128 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L130-130 verbatim
end


-- @@ L132-132 verbatim
noncomputable section

-- @@ L133-133 verbatim
open Matrix

-- @@ L134-134 verbatim
open scoped BigOperators

-- @@ L135-135 verbatim
open scoped Topology

-- @@ L136-136 verbatim
open Filter

-- @@ L137-137 verbatim
open Matrix

-- @@ L138-138 verbatim
open scoped BigOperators

-- @@ L139-139 verbatim
open Matrix MvPolynomial

-- @@ L140-140 verbatim
open Matrix

-- @@ L141-141 verbatim
open scoped BigOperators


-- @@ L143-143 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L144-144 verbatim
open MvPolynomial Finsupp

-- @@ L145-145 verbatim
open scoped BigOperators

-- @@ L146-146 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L148-148 verbatim
abbrev SplitPolynomial (ι : Type*) := MvPolynomial (ι ⊕ ι) ℂ


-- @@ L150-152 verbatim
/-- The isotropic quadratic in independent z and bar-z variables. -/
def quadric (ι : Type*) [Fintype ι] : SplitPolynomial ι :=
  ∑ i : ι,X (Sum.inl i)*X (Sum.inr i)


-- @@ L154-155 verbatim
def mixedLaplacian : SplitPolynomial ι →ₗ[ℂ] SplitPolynomial ι :=
  ∑ i : ι,(pderiv (Sum.inl i)).toLinearMap.comp (pderiv (Sum.inr i)).toLinearMap


-- @@ L157-159 verbatim
lemma mixedLaplacian_apply (P : SplitPolynomial ι) :
    mixedLaplacian P = ∑ i : ι,pderiv (Sum.inl i) (pderiv (Sum.inr i) P) := by
  simp [mixedLaplacian]


-- @@ L161-167 verbatim
lemma fischer_quadric (P Q : SplitPolynomial ι) :
    fischer (quadric ι*P) Q = fischer P (mixedLaplacian Q) := by
  simp only [quadric,Finset.sum_mul,map_sum,LinearMap.sum_apply,mixedLaplacian_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show X (Sum.inl i)*X (Sum.inr i)*P = (P*X (Sum.inl i))*X (Sum.inr i) by ring,
    fischer_mul_X,fischer_mul_X]


-- @@ L169-170 verbatim
lemma conjugate_quadric : conjugate (quadric ι) = quadric ι := by
  simp [quadric,conjugate,MvPolynomial.map_X]


-- @@ L172-174 verbatim
lemma conjugate_mixedLaplacian (P : SplitPolynomial ι) :
    conjugate (mixedLaplacian P) = mixedLaplacian (conjugate P) := by
  simp only [mixedLaplacian_apply,map_sum,conjugate_pderiv]


-- @@ L176-184 verbatim
/-- A harmonic multiple of the isotropic quadratic is zero. Positivity is
proved in the actual coefficient algebra by the Hermitian Fischer form. -/
theorem harmonic_quadric_multiple {P : SplitPolynomial ι}
    (hP : mixedLaplacian P = 0) (hdiv : quadric ι ∣ P) : P = 0 := by
  obtain ⟨Q,hQ⟩ := hdiv
  apply fischer_definite
  have hc : conjugate P = quadric ι * conjugate Q := by
    rw [hQ, map_mul, conjugate_quadric]
  rw [fischer_symm, hc, fischer_quadric, hP, map_zero]


-- @@ L186-202 verbatim
lemma quadric_irreducible [Nontrivial ι] : Irreducible (quadric ι) := by
  classical
  let c : ι →₀ ℂ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
  have hc (i : ι) : c i = 1 := by simp [c]
  have he : MvPolynomial.sumSMulXSMulY c = quadric ι := by
    unfold MvPolynomial.sumSMulXSMulY quadric
    rw [Finsupp.linearCombination_apply,Finsupp.sum_fintype]
    · simp only [hc,one_smul]
    · intro i; exact zero_smul _ _
  rw [← he]
  apply MvPolynomial.irreducible_sumSMulXSMulY
  · have hs : c.support = Finset.univ := by ext i; simp [Finsupp.mem_support_iff,hc]
    rw [hs]
    exact Finset.univ_nontrivial
  · intro r hr
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact isUnit_of_dvd_one (hc i ▸ hr i)


-- @@ L204-218 verbatim
/-- The orbit-spanning divisibility step from the manuscript, now obtained
from the pinned Nullstellensatz and a proved irreducible actual quadric. -/
theorem quadric_dvd_of_vanishing [Nontrivial ι] (P : SplitPolynomial ι)
    (hP : ∀ a : (ι ⊕ ι) → ℂ,MvPolynomial.eval a (quadric ι) = 0 →
      MvPolynomial.eval a P = 0) : quadric ι ∣ P := by
  let I : Ideal (SplitPolynomial ι) := Ideal.span {quadric ι}
  have hp : Prime (quadric ι) := irreducible_iff_prime.1 quadric_irreducible
  have : I.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hm : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    intro a ha
    apply hP a
    have hz := ha (quadric ι) (Ideal.subset_span (Set.mem_singleton _))
    simpa using hz
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hm
  exact Ideal.mem_span_singleton.1 hm


-- @@ L220-220 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L222-222 verbatim
end


-- @@ L224-224 verbatim
noncomputable section

-- @@ L225-225 verbatim
open Matrix

-- @@ L226-226 verbatim
open scoped BigOperators

-- @@ L227-227 verbatim
open scoped Topology

-- @@ L228-228 verbatim
open Filter

-- @@ L229-229 verbatim
open Matrix

-- @@ L230-230 verbatim
open scoped BigOperators

-- @@ L231-231 verbatim
open Matrix MvPolynomial

-- @@ L232-232 verbatim
open Matrix

-- @@ L233-233 verbatim
open scoped BigOperators


-- @@ L235-235 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L236-236 verbatim
open MvPolynomial Finsupp

-- @@ L237-237 verbatim
open scoped BigOperators

-- @@ L238-238 verbatim
variable {σ : Type*} [Fintype σ]


-- @@ L240-240 verbatim
def linearForm (a : σ → ℂ) : MvPolynomial σ ℂ := ∑ i : σ,a i • X i


-- @@ L242-250 verbatim
lemma factorialWeight_mul_multinomial (d : σ →₀ ℕ) :
    factorialWeight d * (d.multinomial:ℂ) = (d.sum (fun _ v => v)).factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have hd : (∑ i : σ,d i) = d.sum (fun _ v => v) := by
    rw [Finsupp.sum_fintype]; intro; rfl
  have h := Nat.multinomial_spec Finset.univ d
  rw [hd] at h
  unfold factorialWeight
  exact_mod_cast h


-- @@ L252-265 verbatim
lemma fischer_linearForm_pow {P : MvPolynomial σ ℂ} {l : ℕ}
    (hP : P.IsHomogeneous l) (a : σ → ℂ) :
    fischer P (linearForm a ^ l) = (l.factorial:ℂ)*MvPolynomial.eval a P := by
  classical
  rw [fischer_apply,MvPolynomial.eval_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : d.sum (fun _ v => v) = l := (hP.degree_eq_sum_deg_support hd).symm
  rw [linearForm,coeff_linearCombination_X_pow_of_fintype,ite_eq_left he]
  rw [show P.coeff d * factorialWeight d * ((d.multinomial:ℂ)*d.prod (fun r m => a r^m)) =
    P.coeff d * (factorialWeight d*(d.multinomial:ℂ))*d.prod (fun r m => a r^m) by ring,
    factorialWeight_mul_multinomial,he]
  change P.coeff d * (l.factorial:ℂ) * (∏ i ∈ d.support,a i^d i) = _
  ring


-- @@ L267-267 verbatim
variable {ι : Type*} [Fintype ι] [Nontrivial ι]


-- @@ L269-280 verbatim
/-- No nonzero homogeneous harmonic polynomial can annihilate every isotropic
power. This is the actual polynomial producer in the orbit-span argument. -/
theorem harmonic_eq_zero_of_isotropic_pairing {P : SplitPolynomial ι} {l : ℕ}
    (hP : P.IsHomogeneous l) (hΔ : mixedLaplacian P = 0)
    (hpair : ∀ a : (ι ⊕ ι) → ℂ,MvPolynomial.eval a (quadric ι) = 0 →
      fischer P (linearForm a ^ l) = 0) : P = 0 := by
  apply harmonic_quadric_multiple hΔ
  apply quadric_dvd_of_vanishing
  intro a ha
  have h := hpair a ha
  rw [fischer_linearForm_pow hP] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast Nat.factorial_ne_zero l)


-- @@ L282-282 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L284-284 verbatim
end


-- @@ L286-286 verbatim
noncomputable section

-- @@ L287-287 verbatim
open Matrix

-- @@ L288-288 verbatim
open scoped BigOperators

-- @@ L289-289 verbatim
open scoped Topology

-- @@ L290-290 verbatim
open Filter

-- @@ L291-291 verbatim
open Matrix

-- @@ L292-292 verbatim
open scoped BigOperators

-- @@ L293-293 verbatim
open Matrix MvPolynomial

-- @@ L294-294 verbatim
open Matrix

-- @@ L295-295 verbatim
open scoped BigOperators


-- @@ L297-297 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L298-298 verbatim
open MvPolynomial Finsupp Module

-- @@ L299-299 verbatim
open scoped BigOperators

-- @@ L300-300 verbatim
variable {σ : Type*} [Fintype σ]


-- @@ L302-305 verbatim
lemma linearForm_homogeneous (a : σ → ℂ) : (linearForm a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [smul_eq_C_mul] using (isHomogeneous_X ℂ i).C_mul (a i)


-- @@ L307-309 verbatim
lemma pderiv_linearForm (a : σ → ℂ) (i : σ) : pderiv i (linearForm a) = C (a i) := by
  classical
  simp [linearForm,pderiv_X,smul_eq_C_mul,Pi.single_apply]


-- @@ L311-311 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L313-328 verbatim
lemma mixedLaplacian_linearForm_pow (a : (ι ⊕ ι) → ℂ) (l : ℕ) :
    mixedLaplacian (linearForm a ^ (l+2)) =
      C (((l+2:ℕ):ℂ)*((l+1:ℕ):ℂ)*MvPolynomial.eval a (quadric ι)) * linearForm a ^ l := by
  classical
  rw [mixedLaplacian_apply]
  have he (i : ι) : pderiv (Sum.inl i) (pderiv (Sum.inr i) (linearForm a^(l+2))) =
      C (((l+2:ℕ):ℂ)*((l+1:ℕ):ℂ)) *
        (C (a (Sum.inl i)*a (Sum.inr i))*linearForm a^l) := by
    simp only [pderiv_pow,pderiv_linearForm,show l+2-1=l+1 by omega,
      show l+1-1=l by omega,pderiv_mul,pderiv_C,mul_zero,add_zero,
      map_natCast,Derivation.map_natCast,zero_mul,zero_add,map_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,← Finset.sum_mul,← map_sum]
  simp only [quadric,map_sum,map_mul,eval_X]
  ring


-- @@ L330-337 verbatim
lemma isotropicPower_harmonic (a : (ι ⊕ ι) → ℂ)
    (ha : MvPolynomial.eval a (quadric ι) = 0) (l : ℕ) :
    mixedLaplacian (linearForm a ^ l) = 0 := by
  rcases l with _ | l
  · simp [mixedLaplacian_apply]
  rcases l with _ | l
  · simp [mixedLaplacian_apply,pderiv_linearForm]
  · rw [show l+1+1=l+2 by omega,mixedLaplacian_linearForm_pow,ha,mul_zero,map_zero,zero_mul]


-- @@ L339-342 verbatim
/-- The actual degree-l complex harmonic polynomial space in independent complex
coordinates. It is not postulated as an irreducible representation. -/
def harmonicSpace (ι : Type*) [Fintype ι] (l : ℕ) : Submodule ℂ (SplitPolynomial ι) :=
  homogeneousSubmodule (ι ⊕ ι) ℂ l ⊓ LinearMap.ker mixedLaplacian


-- @@ L344-345 verbatim
lemma mem_harmonicSpace {P : SplitPolynomial ι} {l : ℕ} :
    P ∈ harmonicSpace ι l ↔ P.IsHomogeneous l ∧ mixedLaplacian P = 0 := Iff.rfl


-- @@ L347-350 verbatim
instance harmonicSpace_finite (l : ℕ) : FiniteDimensional ℂ (harmonicSpace ι l) := by
  have : FiniteDimensional ℂ (homogeneousSubmodule (ι ⊕ ι) ℂ l) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (ι ⊕ ι) ℂ l)
  exact Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)


-- @@ L352-356 verbatim
lemma conjugate_mem_harmonicSpace {P : SplitPolynomial ι} {l : ℕ}
    (hP : P ∈ harmonicSpace ι l) : conjugate P ∈ harmonicSpace ι l := by
  refine ⟨hP.1.map _,?_⟩
  change mixedLaplacian (conjugate P) = 0
  rw [← conjugate_mixedLaplacian,hP.2,map_zero]


-- @@ L358-359 verbatim
def spaceFischer (l : ℕ) : harmonicSpace ι l →ₗ[ℂ] Module.Dual ℂ (harmonicSpace ι l) :=
  (harmonicSpace ι l).subtype.dualMap.comp (fischer.comp (harmonicSpace ι l).subtype)


-- @@ L361-370 verbatim
lemma spaceFischer_surjective (l : ℕ) : Function.Surjective (spaceFischer (ι := ι) l) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℂ) (V := harmonicSpace ι l)).symm).1
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  apply Subtype.ext
  apply fischer_definite
  exact congrArg (fun f : Module.Dual ℂ (harmonicSpace ι l) =>
    f ⟨conjugate P,conjugate_mem_harmonicSpace P.property⟩) hP


-- @@ L372-377 verbatim
def isotropicPower (l : ℕ) (a : {a : (ι ⊕ ι) → ℂ | MvPolynomial.eval a (quadric ι) = 0}) :
    harmonicSpace ι l :=
  ⟨linearForm a.1 ^ l,by
    change (linearForm a.1 ^ l).IsHomogeneous l
    simpa only [one_mul] using (linearForm_homogeneous a.1).pow l,
    isotropicPower_harmonic a.1 a.2 l⟩


-- @@ L379-393 verbatim
/-- The full isotropic-power span is proved by actual coefficient duality and
the prime quadric ideal, without importing a representation-theoretic axiom. -/
theorem isotropicPowers_span [Nontrivial ι] (l : ℕ) :
    Submodule.span ℂ (Set.range (isotropicPower (ι := ι) l)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.1
  apply (Submodule.eq_bot_iff _).2
  intro f hf
  obtain ⟨P,rfl⟩ := spaceFischer_surjective l f
  have hz : (P : SplitPolynomial ι) = 0 := by
    apply harmonic_eq_zero_of_isotropic_pairing P.property.1 P.property.2
    intro a ha
    exact (Submodule.mem_dualAnnihilator _).1 hf (isotropicPower l ⟨a,ha⟩)
      (Submodule.subset_span (Set.mem_range_self _))
  have hp : P=0 := Subtype.ext hz
  rw [hp,map_zero]


-- @@ L395-395 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L397-397 verbatim
end


-- @@ L399-399 verbatim
noncomputable section

-- @@ L400-400 verbatim
open Matrix

-- @@ L401-401 verbatim
open scoped BigOperators

-- @@ L402-402 verbatim
open scoped Topology

-- @@ L403-403 verbatim
open Filter

-- @@ L404-404 verbatim
open Matrix

-- @@ L405-405 verbatim
open scoped BigOperators

-- @@ L406-406 verbatim
open Matrix MvPolynomial

-- @@ L407-407 verbatim
open Matrix

-- @@ L408-408 verbatim
open scoped BigOperators


-- @@ L410-410 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L411-411 verbatim
open MvPolynomial Module

-- @@ L412-412 verbatim
variable {ι : Type*} [Fintype ι] [Nontrivial ι]


-- @@ L414-439 verbatim
/-- Algebraic replacement for the manuscript's real-analytic density step.
On the actual isotropic-power orbit, the product of two nonzero linear
functionals cannot vanish identically. The proof uses the prime quadric. -/
theorem power_product_zero (l : ℕ) (f g : Module.Dual ℂ (harmonicSpace ι l))
    (hf : f ≠ 0)
    (h : ∀ a,f (isotropicPower l a)*g (isotropicPower l a) = 0) : g = 0 := by
  obtain ⟨P,rfl⟩ := spaceFischer_surjective l f
  obtain ⟨Q,rfl⟩ := spaceFischer_surjective l g
  have hdiv : quadric ι ∣ (P : SplitPolynomial ι)*(Q : SplitPolynomial ι) := by
    apply quadric_dvd_of_vanishing
    intro a ha
    have he := h ⟨a,ha⟩
    change fischer (P : SplitPolynomial ι) (linearForm a^l)*
      fischer (Q : SplitPolynomial ι) (linearForm a^l) = 0 at he
    rw [fischer_linearForm_pow P.property.1,fischer_linearForm_pow Q.property.1] at he
    rw [map_mul]
    have hc : (l.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
    apply (mul_eq_zero.1 he).elim
    · intro hp; exact mul_eq_zero_of_left ((mul_eq_zero.1 hp).resolve_left hc) _
    · intro hq; exact mul_eq_zero_of_right _ ((mul_eq_zero.1 hq).resolve_left hc)
  have hprime : Prime (quadric ι) := irreducible_iff_prime.1 quadric_irreducible
  rcases hprime.dvd_or_dvd hdiv with hp | hq
  · have hz : P=0 := Subtype.ext (harmonic_quadric_multiple P.property.2 hp)
    exact (hf (by rw [hz,map_zero])).elim
  · have hz : Q=0 := Subtype.ext (harmonic_quadric_multiple Q.property.2 hq)
    rw [hz,map_zero]


-- @@ L441-441 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L443-443 verbatim
end


-- @@ L445-445 verbatim
noncomputable section

-- @@ L446-446 verbatim
open Matrix

-- @@ L447-447 verbatim
open scoped BigOperators

-- @@ L448-448 verbatim
open scoped Topology

-- @@ L449-449 verbatim
open Filter

-- @@ L450-450 verbatim
open Matrix

-- @@ L451-451 verbatim
open scoped BigOperators

-- @@ L452-452 verbatim
open Matrix MvPolynomial

-- @@ L453-453 verbatim
open Matrix

-- @@ L454-454 verbatim
open scoped BigOperators


-- @@ L456-456 verbatim
namespace HarmonicCounterexample.Control

-- @@ L457-457 verbatim
open Module

-- @@ L458-458 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L459-459 verbatim
variable {𝕜 W : Type*} [Field 𝕜] [AddCommGroup W] [Module 𝕜 W]


-- @@ L461-463 verbatim
/-- Genuine rank-one endomorphisms for a bilinear form. -/
def outer (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (u v : W) : Module.End 𝕜 W :=
  (B v).smulRight u


-- @@ L465-465 verbatim
lemma outer_apply (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (u v x : W) : outer B u v x = B v x • u := rfl


-- @@ L467-473 verbatim
def wedgeLeft (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (u : W) : W →ₗ[𝕜] Module.End 𝕜 W where
  toFun v := outer B u v-outer B v u
  map_add' v w := by ext x; simp [outer_apply,add_smul,smul_add]; abel
  map_smul' c v := by
    ext x
    simp only [outer_apply,LinearMap.sub_apply,LinearMap.smul_apply,map_smul,smul_eq_mul,smul_sub,RingHom.id_apply]
    module


-- @@ L475-476 verbatim
lemma wedgeLeft_apply (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (u v : W) :
    wedgeLeft B u v = outer B u v-outer B v u := rfl


-- @@ L478-479 verbatim
lemma wedgeLeft_flip (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (u v : W) :
    wedgeLeft B u v = -wedgeLeft B v u := by simp [wedgeLeft_apply]


-- @@ L481-488 verbatim
lemma bracket_outer (B : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
    (hB : ∀ x y,B x y = B y x) (u v : W) :
    ⁅outer B u u,outer B v v⁆ = B u v • wedgeLeft B u v := by
  ext x
  simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,outer_apply,
    map_smul,smul_smul,LinearMap.smul_apply,wedgeLeft_apply,smul_sub]
  rw [hB v u]
  module


-- @@ L490-490 verbatim
end HarmonicCounterexample.Control


-- @@ L492-492 verbatim
end


-- @@ L494-494 verbatim
noncomputable section

-- @@ L495-495 verbatim
open Matrix

-- @@ L496-496 verbatim
open scoped BigOperators

-- @@ L497-497 verbatim
open scoped Topology

-- @@ L498-498 verbatim
open Filter

-- @@ L499-499 verbatim
open Matrix

-- @@ L500-500 verbatim
open scoped BigOperators

-- @@ L501-501 verbatim
open Matrix MvPolynomial

-- @@ L502-502 verbatim
open Matrix

-- @@ L503-503 verbatim
open scoped BigOperators


-- @@ L505-505 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L506-506 verbatim
open Module HarmonicCounterexample.Control

-- @@ L507-507 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L508-508 verbatim
variable {ι : Type*} [Fintype ι] [Nontrivial ι] {l : ℕ}


-- @@ L510-550 verbatim
/-- From all orbit rank-one operators to every skew operator, with neither an
unproved density principle nor an assumed Lie saturation step. -/
theorem wedges_mem_of_isotropic_rankones
    (L : LieSubalgebra ℂ (Module.End ℂ (harmonicSpace ι l)))
    (B : harmonicSpace ι l →ₗ[ℂ] Module.Dual ℂ (harmonicSpace ι l))
    (hB : ∀ x y,B x y = B y x) (hinj : Function.Injective B)
    (hL : ∀ a,outer B (isotropicPower l a) (isotropicPower l a) ∈ L) :
    ∀ u v,wedgeLeft B u v ∈ L := by
  have hu (a) (v : harmonicSpace ι l) : wedgeLeft B (isotropicPower l a) v ∈ L := by
    let u := isotropicPower l a
    by_cases hu0 : u = 0
    · rw [show isotropicPower l a = 0 from hu0,wedgeLeft_flip,map_zero]
      exact L.neg_mem L.zero_mem
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff L.toSubmodule _).1
    intro f hf
    have hz : f.comp (wedgeLeft B u) = 0 := by
      apply power_product_zero l (B u) _ (fun he => hu0 (hinj (he.trans (map_zero B).symm)))
      intro b
      have hm := L.lie_mem (hL a) (hL b)
      rw [bracket_outer B hB] at hm
      have he := (Submodule.mem_dualAnnihilator f).1 hf _ hm
      simpa only [map_smul,smul_eq_mul,LinearMap.comp_apply,u] using he
    exact congrArg (fun g : Module.Dual ℂ (harmonicSpace ι l) => g v) hz
  intro u v
  have hspan : u ∈ Submodule.span ℂ (Set.range (isotropicPower (ι := ι) l)) := by
    rw [isotropicPowers_span]; trivial
  induction hspan using Submodule.span_induction with
  | mem w hw => obtain ⟨a,rfl⟩ := hw; exact hu a v
  | zero => rw [wedgeLeft_flip,map_zero]; exact L.neg_mem L.zero_mem
  | add u w _ _ hu hw =>
    rw [wedgeLeft_flip,map_add]
    apply L.neg_mem
    apply L.add_mem
    · rw [wedgeLeft_flip]; exact L.neg_mem hu
    · rw [wedgeLeft_flip]; exact L.neg_mem hw
  | smul c w _ hw =>
    rw [wedgeLeft_flip,map_smul]
    apply L.neg_mem
    apply L.smul_mem
    rw [wedgeLeft_flip]
    exact L.neg_mem hw


-- @@ L552-552 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L554-554 verbatim
end


-- @@ L556-556 verbatim
noncomputable section

-- @@ L557-557 verbatim
open Matrix

-- @@ L558-558 verbatim
open scoped BigOperators

-- @@ L559-559 verbatim
open scoped Topology

-- @@ L560-560 verbatim
open Filter

-- @@ L561-561 verbatim
open Matrix

-- @@ L562-562 verbatim
open scoped BigOperators

-- @@ L563-563 verbatim
open Matrix MvPolynomial

-- @@ L564-564 verbatim
open Matrix

-- @@ L565-565 verbatim
open scoped BigOperators


-- @@ L567-567 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L568-568 verbatim
open MvPolynomial

-- @@ L569-569 verbatim
open scoped BigOperators

-- @@ L570-570 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L572-573 verbatim
def swapPolynomial : SplitPolynomial ι ≃ₐ[ℂ] SplitPolynomial ι :=
  renameEquiv ℂ (Equiv.sumComm ι ι)


-- @@ L575-578 verbatim
omit [Fintype ι] in
lemma swapPolynomial_involutive (P : SplitPolynomial ι) :
    swapPolynomial (swapPolynomial P) = P := by
  exact (swapPolynomial (ι := ι)).apply_symm_apply P


-- @@ L580-581 verbatim
omit [Fintype ι] in
lemma swapPolynomial_X (i : ι ⊕ ι) : swapPolynomial (X i) = X (Sum.swap i) := rename_X _ _


-- @@ L583-586 verbatim
omit [Fintype ι] in
lemma swapPolynomial_pderiv (P : SplitPolynomial ι) (i : ι ⊕ ι) :
    swapPolynomial (pderiv i P) = pderiv (Sum.swap i) (swapPolynomial P) :=
  (pderiv_rename (Equiv.sumComm ι ι).injective i P).symm


-- @@ L588-600 verbatim
omit [Fintype ι] in
lemma pderiv_commute (P : SplitPolynomial ι) (i j : ι ⊕ ι) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P k hp =>
    simp only [pderiv_mul,map_add,hp]
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j; rfl
    · subst i; simp [Ne.symm hj]
    · subst j; simp [Ne.symm hi]
    · simp [Ne.symm hi,Ne.symm hj]


-- @@ L602-607 verbatim
lemma swapPolynomial_mixedLaplacian (P : SplitPolynomial ι) :
    swapPolynomial (mixedLaplacian P) = mixedLaplacian (swapPolynomial P) := by
  simp only [mixedLaplacian_apply,map_sum,swapPolynomial_pderiv,Sum.swap_inl,Sum.swap_inr]
  apply Finset.sum_congr rfl
  intro i _
  exact pderiv_commute _ _ _


-- @@ L609-611 verbatim
lemma fischer_C (c : ℂ) (P : SplitPolynomial ι) : fischer (C c) P = c*P.coeff 0 := by
  rw [show C c = monomial 0 c from rfl,fischer_monomial]
  simp [factorialWeight]


-- @@ L613-624 verbatim
lemma fischer_swapPolynomial (P Q : SplitPolynomial ι) :
    fischer (swapPolynomial P) Q = fischer P (swapPolynomial Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    change fischer (rename Sum.swap (C c)) Q = _
    rw [rename_C,fischer_C,fischer_C]
    congr 1
    exact (constantCoeff_rename Sum.swap Q).symm
  | add P R hp hr => simp only [map_add,LinearMap.add_apply,hp,hr]
  | mul_X P i hp =>
    rw [map_mul,swapPolynomial_X,fischer_mul_X,hp,fischer_mul_X,
      swapPolynomial_pderiv,Sum.swap_swap]


-- @@ L626-630 verbatim
lemma swapPolynomial_mem_harmonicSpace {P : SplitPolynomial ι} {l : ℕ}
    (hP : P ∈ harmonicSpace ι l) : swapPolynomial P ∈ harmonicSpace ι l := by
  refine ⟨hP.1.rename_isHomogeneous, ?_⟩
  change mixedLaplacian (swapPolynomial P) = 0
  rw [← swapPolynomial_mixedLaplacian,hP.2,map_zero]


-- @@ L632-638 verbatim
def spaceSwap (l : ℕ) : harmonicSpace ι l ≃ₗ[ℂ] harmonicSpace ι l where
  toFun P := ⟨swapPolynomial P,swapPolynomial_mem_harmonicSpace P.property⟩
  invFun P := ⟨swapPolynomial P,swapPolynomial_mem_harmonicSpace P.property⟩
  left_inv P := Subtype.ext (swapPolynomial_involutive (P : SplitPolynomial ι))
  right_inv P := Subtype.ext (swapPolynomial_involutive (P : SplitPolynomial ι))
  map_add' P Q := Subtype.ext (map_add swapPolynomial (P : SplitPolynomial ι) (Q : SplitPolynomial ι))
  map_smul' c P := Subtype.ext (map_smul swapPolynomial c (P : SplitPolynomial ι))


-- @@ L640-644 verbatim
/-- The invariant complex bilinear Fischer form in split coordinates, swapping
z and bar-z in the second argument. This is the correct null-vector pairing,
not the positive coefficient pairing without this swap. -/
def roundPairing (l : ℕ) : harmonicSpace ι l →ₗ[ℂ] Module.Dual ℂ (harmonicSpace ι l) :=
  (spaceFischer l).comp (spaceSwap l).toLinearMap


-- @@ L646-647 verbatim
lemma roundPairing_apply (l : ℕ) (P Q : harmonicSpace ι l) :
    roundPairing l P Q = fischer (swapPolynomial (P : SplitPolynomial ι)) (Q : SplitPolynomial ι) := rfl


-- @@ L649-651 verbatim
lemma roundPairing_symm (l : ℕ) (P Q : harmonicSpace ι l) :
    roundPairing l P Q = roundPairing l Q P := by
  rw [roundPairing_apply,roundPairing_apply,fischer_swapPolynomial,fischer_symm]


-- @@ L653-657 verbatim
lemma roundPairing_injective (l : ℕ) : Function.Injective (roundPairing (ι := ι) l) := by
  have hf : Function.Injective (spaceFischer (ι := ι) l) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := harmonicSpace ι l)).symm).2 (spaceFischer_surjective l)
  exact hf.comp (spaceSwap l).injective


-- @@ L659-667 verbatim
lemma eval_swap_linearForm (a : (ι ⊕ ι) → ℂ) :
    MvPolynomial.eval a (swapPolynomial (linearForm a)) =
      2*MvPolynomial.eval a (quadric ι) := by
  change MvPolynomial.eval a (rename Sum.swap (linearForm a)) = _
  simp only [linearForm,quadric,map_sum,map_add,smul_eq_C_mul,map_mul,rename_C,
    rename_X,eval_X,eval_C,Fintype.sum_sum_type,Sum.swap_inl,Sum.swap_inr]
  rw [show (∑ i : ι,a (Sum.inr i)*a (Sum.inl i)) =
      ∑ i : ι,a (Sum.inl i)*a (Sum.inr i) from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
  ring


-- @@ L669-677 verbatim
lemma roundPairing_isotropicPower (l : ℕ) (hl : 0 < l)
    (a : {a : (ι ⊕ ι) → ℂ | MvPolynomial.eval a (quadric ι) = 0}) :
    roundPairing l (isotropicPower l a) (isotropicPower l a) = 0 := by
  rw [roundPairing_apply]
  change fischer (swapPolynomial (linearForm a.1 ^ l)) (linearForm a.1 ^ l) = 0
  have hh := (swapPolynomial_mem_harmonicSpace (isotropicPower l a).property).1
  dsimp only [isotropicPower] at hh
  rw [fischer_linearForm_pow hh,map_pow,map_pow,eval_swap_linearForm,a.property,
    mul_zero,zero_pow hl.ne',mul_zero]



-- @@ L680-680 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L682-682 verbatim
end


-- @@ L684-684 verbatim
noncomputable section

-- @@ L685-685 verbatim
open Matrix

-- @@ L686-686 verbatim
open scoped BigOperators

-- @@ L687-687 verbatim
open scoped Topology

-- @@ L688-688 verbatim
open Filter

-- @@ L689-689 verbatim
open Matrix

-- @@ L690-690 verbatim
open scoped BigOperators

-- @@ L691-691 verbatim
open Matrix MvPolynomial

-- @@ L692-692 verbatim
open Matrix

-- @@ L693-693 verbatim
open scoped BigOperators


-- @@ L695-695 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L696-696 verbatim
open MvPolynomial Finsupp

-- @@ L697-697 verbatim
open scoped BigOperators

-- @@ L698-698 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L700-701 verbatim
lemma linearForm_single (i : ι) : linearForm (Pi.single i (1:ℂ)) = X i := by
  simp [linearForm,Pi.single_apply]


-- @@ L703-710 verbatim
omit [DecidableEq ι] in
lemma factorialWeight_single (i : ι) (l : ℕ) : factorialWeight (Finsupp.single i l) = (l.factorial:ℂ) := by
  unfold factorialWeight
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp


-- @@ L712-718 verbatim
lemma homogeneous_eval_single {l : ℕ} {P : MvPolynomial ι ℂ}
    (hP : P.IsHomogeneous l) (i : ι) :
    MvPolynomial.eval (Pi.single i 1) P = P.coeff (Finsupp.single i l) := by
  have h := fischer_linearForm_pow hP (Pi.single i 1)
  rw [linearForm_single,X_pow_eq_monomial,fischer_symm,fischer_monomial,
    one_mul,factorialWeight_single] at h
  exact (mul_left_cancel₀ (show (l.factorial:ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero l) h).symm


-- @@ L720-720 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L722-722 verbatim
end


-- @@ L724-724 verbatim
noncomputable section

-- @@ L725-725 verbatim
open Matrix

-- @@ L726-726 verbatim
open scoped BigOperators

-- @@ L727-727 verbatim
open scoped Topology

-- @@ L728-728 verbatim
open Filter

-- @@ L729-729 verbatim
open Matrix

-- @@ L730-730 verbatim
open scoped BigOperators

-- @@ L731-731 verbatim
open Matrix MvPolynomial

-- @@ L732-732 verbatim
open Matrix

-- @@ L733-733 verbatim
open scoped BigOperators


-- @@ L735-735 verbatim
namespace HarmonicCounterexample.Control

-- @@ L736-736 verbatim
open MvPolynomial Matrix HarmonicCounterexample.ComplexAngular

-- @@ L737-737 verbatim
open scoped BigOperators

-- @@ L738-738 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L740-747 verbatim
omit [DecidableEq ι] in
lemma eval_linearChange (M : Matrix ι ι ℂ) (a : ι → ℂ) (P : MvPolynomial ι ℂ) :
    MvPolynomial.eval a (linearChange M P) = MvPolynomial.eval (M *ᵥ a) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [linearChange]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    simp only [map_mul,hp,linearChange_X,map_sum,smul_eq_C_mul,map_mul,eval_C,eval_X,Matrix.mulVec,dotProduct]


-- @@ L749-756 verbatim
lemma coeff_pure_linearChange (l : ℕ) (M : Matrix ι ι ℂ)
    (P : homogeneousSubmodule ι ℂ l) (i : ι) :
    (linearChange M P.1).coeff (Finsupp.single i l) = MvPolynomial.eval (fun j => M j i) P.1 := by
  rw [← homogeneous_eval_single (linearChange_homogeneous P.2 M) i,eval_linearChange]
  have he : M *ᵥ Pi.single i 1 = fun j => M j i := by
    funext j
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [he]


-- @@ L758-776 verbatim
lemma matrixUnit_homogeneous_apply (l : ℕ) (μ ν : MonomialIndex ι l)
    (P : homogeneousSubmodule ι ℂ l) :
    (((LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm (single μ ν (1:ℂ))) P).1 =
      P.1.coeff ν.1 • monomial μ.1 1 := by
  let B := homogeneousBasis (𝕜 := ℂ) (ι := ι) l
  have he : (LinearMap.toMatrixAlgEquiv B).symm (single μ ν (1:ℂ)) =
      ((B.coord ν).smulRight (B μ)) := by
    apply (LinearMap.toMatrixAlgEquiv B).injective
    rw [AlgEquiv.apply_symm_apply]
    ext a b
    change single μ ν (1:ℂ) a b = (LinearMap.toMatrix B B ((B.coord ν).smulRight (B μ))) a b
    simp [LinearMap.toMatrix_apply,LinearMap.smulRight_apply,Module.Basis.coord_apply,
      Module.Basis.repr_self,Matrix.single_apply,Finsupp.single_apply]
    split_ifs <;> simp_all
  rw [he]
  change ((B.repr P ν) • B μ).1 = _
  rw [show (B.repr P ν) = P.1.coeff ν.1 from homogeneousBasis_repr l P ν]
  change P.1.coeff ν.1 • (B μ).1 = _
  rw [homogeneousBasis_val]


-- @@ L778-778 verbatim
end HarmonicCounterexample.Control


-- @@ L780-780 verbatim
end


-- @@ L782-782 verbatim
noncomputable section

-- @@ L783-783 verbatim
open Matrix

-- @@ L784-784 verbatim
open scoped BigOperators

-- @@ L785-785 verbatim
open scoped Topology

-- @@ L786-786 verbatim
open Filter

-- @@ L787-787 verbatim
open Matrix

-- @@ L788-788 verbatim
open scoped BigOperators

-- @@ L789-789 verbatim
open Matrix MvPolynomial

-- @@ L790-790 verbatim
open Matrix

-- @@ L791-791 verbatim
open scoped BigOperators


-- @@ L793-793 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L794-794 verbatim
open MvPolynomial

-- @@ L795-795 verbatim
open scoped BigOperators

-- @@ L796-796 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L798-799 verbatim
lemma linearForm_power_homogeneous (a : ι → ℂ) (l : ℕ) : (linearForm a^l).IsHomogeneous l := by
  simpa only [one_mul] using (linearForm_homogeneous a).pow l


-- @@ L801-814 verbatim
omit [Fintype ι] in
lemma homogeneous_eval_smul {l : ℕ} {P : MvPolynomial ι ℂ} (hP : P.IsHomogeneous l)
    (c : ℂ) (x : ι → ℂ) : MvPolynomial.eval (c • x) P = c^l*MvPolynomial.eval x P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => arg 2; rw [P.as_sum]
  simp only [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : Finsupp.degree d = l := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.1 hd)
  simp only [eval_monomial,Finsupp.prod,Pi.smul_apply,smul_eq_mul,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← Finsupp.degree_apply,hdeg]
  ring


-- @@ L816-816 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L818-818 verbatim
end


-- @@ L820-820 verbatim
noncomputable section

-- @@ L821-821 verbatim
open Matrix

-- @@ L822-822 verbatim
open scoped BigOperators

-- @@ L823-823 verbatim
open scoped Topology

-- @@ L824-824 verbatim
open Filter

-- @@ L825-825 verbatim
open Matrix

-- @@ L826-826 verbatim
open scoped BigOperators

-- @@ L827-827 verbatim
open Matrix MvPolynomial

-- @@ L828-828 verbatim
open Matrix

-- @@ L829-829 verbatim
open scoped BigOperators


-- @@ L831-831 verbatim
namespace HarmonicCounterexample.Control

-- @@ L832-832 verbatim
open Matrix MvPolynomial HarmonicCounterexample.ComplexAngular

-- @@ L833-833 verbatim
open HarmonicCounterexample.Berger.ComplexStructure

-- @@ L834-834 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L835-835 verbatim
variable {s : ℕ}


-- @@ L837-849 verbatim
/-- Actual polynomial evaluation rank-one operator. -/
def homogeneousPowerRankOne (l : ℕ) (a : (Fin s ⊕ Fin s) → ℂ) :
    Module.End ℂ (homogeneousSubmodule (Fin s ⊕ Fin s) ℂ l) where
  toFun P := ⟨MvPolynomial.eval (a ∘ Sum.swap) P.1 • linearForm a^l,
    (homogeneousSubmodule _ ℂ l).smul_mem _ (linearForm_power_homogeneous a l)⟩
  map_add' P Q := by apply Subtype.ext; simp only [Submodule.coe_add,map_add,add_smul]
  map_smul' c P := by
    apply Subtype.ext
    change MvPolynomial.eval (a ∘ Sum.swap) (c • P.1) • linearForm a^l =
      c • (MvPolynomial.eval (a ∘ Sum.swap) P.1 • linearForm a^l)
    have he : MvPolynomial.eval (a ∘ Sum.swap) (c • P.1) =
        c*MvPolynomial.eval (a ∘ Sum.swap) P.1 := by simp only [smul_eq_C_mul,map_mul,eval_C]
    rw [he,mul_smul]


-- @@ L851-854 verbatim
lemma homogeneousPowerRankOne_apply_val (l : ℕ) (a : (Fin s ⊕ Fin s) → ℂ)
    (P : homogeneousSubmodule (Fin s ⊕ Fin s) ℂ l) :
    (homogeneousPowerRankOne l a P).1 =
      MvPolynomial.eval (a ∘ Sum.swap) P.1 • linearForm a^l := rfl


-- @@ L856-857 verbatim
def powerRankOneMatrix (l : ℕ) (a : (Fin s ⊕ Fin s) → ℂ) :=
  LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousPowerRankOne l a)


-- @@ L859-881 verbatim
lemma angular_conjugate_endpoint (l : ℕ)
    (R : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ) :
    angularChange l R*single (pureMonomial true l) (pureMonomial false l) (1:ℂ)*angularChange l Rᵀ =
      powerRankOneMatrix l (splitFieldMatrix R (.inl 0)) := by
  apply (LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm.injective
  simp only [map_mul,angularChange,homogeneousChangeMatrix,powerRankOneMatrix,
    AlgEquiv.symm_apply_apply]
  ext P : 1
  apply Subtype.ext
  change linearChange (splitFieldMatrix R)
    ((((LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm
      (single (pureMonomial true l) (pureMonomial false l) (1:ℂ)))
      (homogeneousChange l (splitFieldMatrix Rᵀ) P)).1) = _
  rw [matrixUnit_homogeneous_apply]
  rw [homogeneousChange_apply_val,homogeneousPowerRankOne_apply_val]
  dsimp only [pureMonomial,signedIndex]
  simp only [ite_true,Bool.false_eq_true,ite_false]
  rw [map_smul,coeff_pure_linearChange,← X_pow_eq_monomial,map_pow,linearChange_X]
  congr 2
  congr 1
  funext a
  simpa only [Sum.swap_swap,Sum.swap_inl,Function.comp_apply] using
    splitFieldMatrix_transpose R (.inl 0) (Sum.swap a)


-- @@ L883-899 verbatim
lemma powerRankOne_smul (l : ℕ) (a : (Fin s ⊕ Fin s) → ℂ) (c : ℂ) :
    powerRankOneMatrix l (c • a) = (c^l*c^l) • powerRankOneMatrix l a := by
  unfold powerRankOneMatrix
  rw [← map_smul]
  congr 1
  ext P : 1
  apply Subtype.ext
  change MvPolynomial.eval ((c • a) ∘ Sum.swap) P.1 • linearForm (c • a)^l =
    (c^l*c^l) • (MvPolynomial.eval (a ∘ Sum.swap) P.1 • linearForm a^l)
  have he : MvPolynomial.eval ((c • a) ∘ Sum.swap) P.1 =
      c^l*MvPolynomial.eval (a ∘ Sum.swap) P.1 := by
    exact homogeneous_eval_smul P.2 c (a ∘ Sum.swap)
  have hl : linearForm (c • a) = c • linearForm a := by
    simp only [linearForm,Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]
  rw [he,hl,smul_pow,smul_smul,smul_smul]
  congr 1
  ring


-- @@ L901-904 verbatim
lemma powerRankOne_zero (l : ℕ) (hl : 0 < l) :
    powerRankOneMatrix (s := s) l 0 = 0 := by
  have he := powerRankOne_smul l (0 : (Fin s ⊕ Fin s) → ℂ) 0
  simpa only [zero_smul,zero_pow hl.ne',zero_mul] using he


-- @@ L906-919 verbatim
/-- All null-cone polynomial evaluation rank-one operators belong to the ACTUAL
angular Lie algebra in n=16, for every degree l>=2. -/
theorem angularLie_all_rankones (l : ℕ) (hl : 2 ≤ l)
    (a : (Fin 8 ⊕ Fin 8) → ℂ) (ha : ∑ j : Fin 8,a (.inl j)*a (.inr j) = 0) :
    powerRankOneMatrix l a ∈ angularLie l := by
  by_cases hn : a = 0
  · rw [hn,powerRankOne_zero l (by omega)]
    exact (angularLie l).zero_mem
  obtain ⟨r,R,hr,hR,haR⟩ := split_null_row_orbit 0 a ha hn
  have hm := angularLie_orthogonal_conjugate l R hR _ (angularLie_endpoint l hl)
  rw [angular_conjugate_endpoint] at hm
  have he : a = (r:ℂ) • splitFieldMatrix R (.inl 0) := funext haR
  rw [he,powerRankOne_smul]
  exact (angularLie l).smul_mem _ hm


-- @@ L921-921 verbatim
end HarmonicCounterexample.Control


-- @@ L923-923 verbatim
end


-- @@ L925-925 verbatim
noncomputable section

-- @@ L926-926 verbatim
open Matrix

-- @@ L927-927 verbatim
open scoped BigOperators

-- @@ L928-928 verbatim
open scoped Topology

-- @@ L929-929 verbatim
open Filter

-- @@ L930-930 verbatim
open Matrix

-- @@ L931-931 verbatim
open scoped BigOperators

-- @@ L932-932 verbatim
open Matrix MvPolynomial

-- @@ L933-933 verbatim
open Matrix

-- @@ L934-934 verbatim
open scoped BigOperators


-- @@ L936-936 verbatim
namespace HarmonicCounterexample.Control

-- @@ L937-937 verbatim
open MvPolynomial Matrix

-- @@ L938-938 verbatim
open scoped BigOperators

-- @@ L939-939 verbatim
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]


-- @@ L941-950 verbatim
omit [Fintype ι] in
lemma pderiv_commutes (P : MvPolynomial ι 𝕜) (i j : ι) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  have h : ⁅pderiv (R := 𝕜) i,pderiv (R := 𝕜) j⁆ = (0 : Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜)) := by
    apply MvPolynomial.derivation_ext
    intro a
    simp only [Derivation.commutator_apply,pderiv_X,Pi.single_apply]
    split_ifs <;> simp
  have he := congrArg (fun D : Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜) => D P) h
  simpa only [Derivation.commutator_apply,Derivation.zero_apply,sub_eq_zero] using he


-- @@ L952-962 verbatim
lemma pderiv_linearField (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) (i : ι) :
    pderiv i (linearField M P) = linearField M (pderiv i P) + ∑ j : ι,M j i • pderiv j P := by
  have h : ⁅pderiv (R := 𝕜) i,linearField M⁆ = ∑ j : ι,M j i • pderiv j := by
    apply MvPolynomial.derivation_ext
    intro a
    by_cases hai : a = i <;>
      simp [Derivation.commutator_apply,linearField_X,pderiv_X,Pi.single_apply,hai,
      Derivation.smul_apply,Derivation.map_smul]
  have he := congrArg (fun D : Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜) => D P) h
  simp only [Derivation.commutator_apply,derivation_sum_apply,Derivation.smul_apply] at he
  exact sub_eq_iff_eq_add'.1 he


-- @@ L964-970 verbatim
lemma pderiv_twice_linearField (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) (i j : ι) :
    pderiv i (pderiv j (linearField M P)) =
      linearField M (pderiv i (pderiv j P)) +
        (∑ k : ι,M k i • pderiv k (pderiv j P)) +
        (∑ k : ι,M k j • pderiv i (pderiv k P)) := by
  rw [pderiv_linearField,map_add,pderiv_linearField]
  simp only [map_sum,Derivation.map_smul]


-- @@ L972-991 verbatim
/-- Skew coefficients cancel against a genuinely symmetric Hessian. -/
lemma skew_hessian_sum (M : Matrix ι ι 𝕜) (hM : ∀ i j,M i j = -M j i)
    (P : MvPolynomial ι 𝕜) [NoZeroSMulDivisors 𝕜 (MvPolynomial ι 𝕜)]
    [CharZero 𝕜] : ∑ i : ι,∑ j : ι,M i j • pderiv i (pderiv j P) = 0 := by
  let S := ∑ i : ι,∑ j : ι,M i j • pderiv i (pderiv j P)
  have h : S = -S := by
    calc
      S = ∑ i : ι,∑ j : ι,M j i • pderiv j (pderiv i P) := Finset.sum_comm
      _ = ∑ i : ι,∑ j : ι,-(M i j • pderiv i (pderiv j P)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        calc
          M j i • pderiv j (pderiv i P) = (-M i j) • pderiv i (pderiv j P) := by
            rw [hM j i,pderiv_commutes P j i]
          _ = _ := neg_smul _ _
      _ = -S := by simp only [Finset.sum_neg_distrib,S]
  have he : (2:𝕜) • S = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
  exact (smul_eq_zero.1 he).resolve_left (by norm_num)


-- @@ L993-993 verbatim
end HarmonicCounterexample.Control


-- @@ L995-995 verbatim
end


-- @@ L997-997 verbatim
noncomputable section

-- @@ L998-998 verbatim
open Matrix

-- @@ L999-999 verbatim
open scoped BigOperators

-- @@ L1000-1000 verbatim
open scoped Topology

-- @@ L1001-1001 verbatim
open Filter

-- @@ L1002-1002 verbatim
open Matrix

-- @@ L1003-1003 verbatim
open scoped BigOperators

-- @@ L1004-1004 verbatim
open Matrix MvPolynomial

-- @@ L1005-1005 verbatim
open Matrix

-- @@ L1006-1006 verbatim
open scoped BigOperators


-- @@ L1008-1008 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L1009-1009 verbatim
open MvPolynomial Matrix HarmonicCounterexample.Control

-- @@ L1010-1010 verbatim
open scoped BigOperators

-- @@ L1011-1011 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L1013-1036 verbatim
/-- Preservation of the split Euclidean Laplacian by exactly the split-orthogonal
infinitesimal fields, derived from their polynomial action. -/
lemma mixedLaplacian_linearField (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hM : ∀ i j,M j (Sum.swap i) = -M i (Sum.swap j))
    (P : SplitPolynomial ι) :
    mixedLaplacian (linearField M P) = linearField M (mixedLaplacian P) := by
  rw [mixedLaplacian_apply,mixedLaplacian_apply,map_sum]
  simp only [pderiv_twice_linearField,Finset.sum_add_distrib]
  have hc : (∑ i : ι,∑ k : ι ⊕ ι,M k (.inl i) • pderiv k (pderiv (.inr i) P)) +
      (∑ i : ι,∑ k : ι ⊕ ι,M k (.inr i) • pderiv (.inl i) (pderiv k P)) = 0 := by
    have hs := skew_hessian_sum (fun i j : ι ⊕ ι => M j (Sum.swap i)) hM P
    rw [Fintype.sum_sum_type] at hs
    simp only [Sum.swap_inl,Sum.swap_inr] at hs
    have he : (∑ i : ι,∑ k : ι ⊕ ι,M k (.inl i) • pderiv k (pderiv (.inr i) P)) =
        ∑ i : ι,∑ k : ι ⊕ ι,M k (.inl i) • pderiv (.inr i) (pderiv k P) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun Q : SplitPolynomial ι => M k (.inl i) • Q)
        (pderiv_commutes P k (.inr i))
    rw [he,add_comm]
    exact hs
  rw [add_assoc,hc,add_zero]


-- @@ L1038-1044 verbatim
lemma linearField_harmonic {l : ℕ} (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hM : ∀ i j,M j (Sum.swap i) = -M i (Sum.swap j))
    {P : SplitPolynomial ι} (hP : P ∈ harmonicSpace ι l) :
    linearField M P ∈ harmonicSpace ι l := by
  refine ⟨linearField_homogeneous hP.1 M,?_⟩
  change mixedLaplacian (linearField M P) = 0
  rw [mixedLaplacian_linearField M hM,hP.2,map_zero]


-- @@ L1046-1046 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L1048-1048 verbatim
end


-- @@ L1050-1050 verbatim
noncomputable section

-- @@ L1051-1051 verbatim
open Matrix

-- @@ L1052-1052 verbatim
open scoped BigOperators

-- @@ L1053-1053 verbatim
open scoped Topology

-- @@ L1054-1054 verbatim
open Filter

-- @@ L1055-1055 verbatim
open Matrix

-- @@ L1056-1056 verbatim
open scoped BigOperators

-- @@ L1057-1057 verbatim
open Matrix MvPolynomial

-- @@ L1058-1058 verbatim
open Matrix

-- @@ L1059-1059 verbatim
open scoped BigOperators


-- @@ L1061-1061 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1062-1062 verbatim
open Module

-- @@ L1063-1063 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L1064-1065 verbatim
variable {𝕜 V W : Type*} [Field 𝕜] [CharZero 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]


-- @@ L1067-1071 verbatim
def traceFreeEnd : Module.End 𝕜 W →ₗ[𝕜] Module.End 𝕜 W where
  toFun A := A-(LinearMap.trace 𝕜 W A/(Module.finrank 𝕜 W:𝕜)) • 1
  map_add' A B := by simp only [map_add,add_div,add_smul]; abel
  map_smul' c A := by
    simp only [map_smul,smul_eq_mul,mul_div_assoc,smul_sub,smul_smul,RingHom.id_apply]


-- @@ L1073-1075 verbatim
omit [CharZero 𝕜] in
lemma traceFreeEnd_eq_self {A : Module.End 𝕜 W} (hA : LinearMap.trace 𝕜 W A = 0) :
    traceFreeEnd A = A := by simp [traceFreeEnd,hA]


-- @@ L1077-1082 verbatim
lemma traceFreeEnd_lie (A B : Module.End 𝕜 W) :
    traceFreeEnd ⁅A,B⁆ = ⁅traceFreeEnd A,traceFreeEnd B⁆ := by
  rw [traceFreeEnd_eq_self (LinearMap.trace_lie A B)]
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,Ring.lie_def,
    mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,smul_sub,smul_smul]
  module


-- @@ L1084-1089 verbatim
lemma traceFreeEnd_one [FiniteDimensional 𝕜 W] [Nontrivial W] :
    traceFreeEnd (1 : Module.End 𝕜 W) = 0 := by
  have hn : (Module.finrank 𝕜 W:𝕜) ≠ 0 := by
    exact_mod_cast ne_of_gt (Module.finrank_pos (R := 𝕜) (M := W))
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.trace_one,
    div_self hn,one_smul,sub_self]


-- @@ L1091-1093 verbatim
lemma traceFreeEnd_sub_scalar [FiniteDimensional 𝕜 W] [Nontrivial W]
    (A : Module.End 𝕜 W) (c : 𝕜) : traceFreeEnd (A-c • 1) = traceFreeEnd A := by
  rw [map_sub,map_smul,traceFreeEnd_one,smul_zero,sub_zero]


-- @@ L1095-1120 verbatim
/-- A matrix acts on the genuine subspace with trace-free restriction in L.
The witness is an operator, not the desired controllability conclusion. -/
def liftedTraceLie (i : W →ₗ[𝕜] V) (L : LieSubalgebra 𝕜 (Module.End 𝕜 W)) :
    LieSubalgebra 𝕜 (Module.End 𝕜 V) where
  carrier := {A | ∃ B : Module.End 𝕜 W,A.comp i = i.comp B ∧ traceFreeEnd B ∈ L}
  zero_mem' := ⟨0,by ext x; simp,by simpa only [map_zero] using L.zero_mem⟩
  add_mem' := by
    rintro A C ⟨B,hB,hBL⟩ ⟨D,hD,hDL⟩
    refine ⟨B+D,?_,?_⟩
    · rw [LinearMap.add_comp,LinearMap.comp_add,hB,hD]
    · simpa only [map_add] using L.add_mem hBL hDL
  smul_mem' := by
    rintro c A ⟨B,hB,hBL⟩
    refine ⟨c • B,?_,?_⟩
    · rw [LinearMap.smul_comp,LinearMap.comp_smul,hB]
    · simpa only [map_smul] using L.smul_mem c hBL
  lie_mem' := by
    rintro A C ⟨B,hB,hBL⟩ ⟨D,hD,hDL⟩
    refine ⟨⁅B,D⁆,?_,?_⟩
    · change (A*C-C*A).comp i = i.comp (B*D-D*B)
      simp only [LinearMap.sub_comp,LinearMap.comp_sub,Module.End.mul_eq_comp,
        LinearMap.comp_assoc,hB,hD]
      rw [← LinearMap.comp_assoc,hB,← LinearMap.comp_assoc,hD]
      simp only [LinearMap.comp_assoc]
    · rw [traceFreeEnd_lie]
      exact L.lie_mem hBL hDL


-- @@ L1122-1131 verbatim
lemma liftedTraceLie_restriction (i : W →ₗ[𝕜] V) (hi : Function.Injective i)
    (L : LieSubalgebra 𝕜 (Module.End 𝕜 W)) {A : Module.End 𝕜 V}
    (hA : A ∈ liftedTraceLie i L) {B : Module.End 𝕜 W} (hB : A.comp i = i.comp B) :
    traceFreeEnd B ∈ L := by
  obtain ⟨C,hC,hCL⟩ := hA
  have he : C = B := by
    ext x
    apply hi
    exact congrArg (fun f : W →ₗ[𝕜] V => f x) (hC.symm.trans hB)
  exact he ▸ hCL


-- @@ L1133-1133 verbatim
end HarmonicCounterexample.Control


-- @@ L1135-1135 verbatim
end


-- @@ L1137-1137 verbatim
noncomputable section

-- @@ L1138-1138 verbatim
open Matrix

-- @@ L1139-1139 verbatim
open scoped BigOperators

-- @@ L1140-1140 verbatim
open scoped Topology

-- @@ L1141-1141 verbatim
open Filter

-- @@ L1142-1142 verbatim
open Matrix

-- @@ L1143-1143 verbatim
open scoped BigOperators

-- @@ L1144-1144 verbatim
open Matrix MvPolynomial

-- @@ L1145-1145 verbatim
open Matrix

-- @@ L1146-1146 verbatim
open scoped BigOperators


-- @@ L1148-1148 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L1149-1149 verbatim
open MvPolynomial HarmonicCounterexample.Control

-- @@ L1150-1150 verbatim
open HarmonicCounterexample.Berger HarmonicCounterexample.Berger.ComplexStructure

-- @@ L1151-1151 verbatim
open scoped BigOperators


-- @@ L1153-1154 verbatim
lemma X_pow_ne_zero_complex {σ : Type*} (i : σ) (l : ℕ) :
    (X i : MvPolynomial σ ℂ)^l ≠ 0 := pow_ne_zero l (X_ne_zero i)


-- @@ L1156-1167 verbatim
instance harmonicSpace_nontrivial (l : ℕ) : Nontrivial (harmonicSpace (Fin 8) l) := by
  let a : (Fin 8 ⊕ Fin 8) → ℂ := Pi.single (.inl 0) 1
  have ha : MvPolynomial.eval a (quadric (Fin 8)) = 0 := by
    simp [quadric,a,Pi.single_apply]
  have he : linearForm a = X (Sum.inl (0 : Fin 8)) := by
    simp [linearForm,a]
  refine ⟨⟨isotropicPower l ⟨a,ha⟩,0,?_⟩⟩
  intro h
  have hz := congrArg (fun P : harmonicSpace (Fin 8) l => (P : SplitPolynomial (Fin 8))) h
  change linearForm a^l=0 at hz
  rw [he] at hz
  exact X_pow_ne_zero_complex (σ := Fin 8 ⊕ Fin 8) (.inl 0) l hz


-- @@ L1169-1170 verbatim
def harmonicEmbedding (l : ℕ) : harmonicSpace (Fin 8) l →ₗ[ℂ]
    homogeneousSubmodule (Fin 8 ⊕ Fin 8) ℂ l := Submodule.inclusion inf_le_left


-- @@ L1172-1173 verbatim
lemma harmonicEmbedding_injective (l : ℕ) : Function.Injective (harmonicEmbedding l) :=
  Submodule.inclusion_injective _


-- @@ L1175-1181 verbatim
/-- The genuine harmonic restriction of an orthogonal angular field. -/
def harmonicField (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    Module.End ℂ (harmonicSpace (Fin 8) l) where
  toFun P := ⟨linearField (splitFieldMatrix J.matrix) P.1,
    linearField_harmonic _ (splitFieldMatrix_skew _ J.skew) P.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (Derivation.map_smul _ _ _)


-- @@ L1183-1185 verbatim
lemma harmonicField_intertwine (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    (homogeneousField l (splitFieldMatrix J.matrix)).comp (harmonicEmbedding l) =
      (harmonicEmbedding l).comp (harmonicField l J) := by ext P; rfl


-- @@ L1187-1187 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L1189-1189 verbatim
end


-- @@ L1191-1191 verbatim
noncomputable section

-- @@ L1192-1192 verbatim
open Matrix

-- @@ L1193-1193 verbatim
open scoped BigOperators

-- @@ L1194-1194 verbatim
open scoped Topology

-- @@ L1195-1195 verbatim
open Filter

-- @@ L1196-1196 verbatim
open Matrix

-- @@ L1197-1197 verbatim
open scoped BigOperators

-- @@ L1198-1198 verbatim
open Matrix MvPolynomial

-- @@ L1199-1199 verbatim
open Matrix

-- @@ L1200-1200 verbatim
open scoped BigOperators


-- @@ L1202-1202 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1203-1203 verbatim
open Matrix MvPolynomial HarmonicCounterexample.ComplexAngular HarmonicCounterexample.Berger

-- @@ L1204-1204 verbatim
open HarmonicCounterexample.Berger.ComplexStructure

-- @@ L1205-1205 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L1207-1212 verbatim
/-- Exactly the trace-free squared angular-field Lie algebra on genuine harmonic
polynomials. No irreducibility or controllability assumption is used. -/
def harmonicAngularLie (l : ℕ) : LieSubalgebra ℂ
    (Module.End ℂ (harmonicSpace (Fin 8) l)) :=
  LieSubalgebra.lieSpan ℂ _ (Set.range fun J : ComplexStructure (Fin 8 ⊕ Fin 8) =>
    traceFreeEnd (harmonicField l J*harmonicField l J))


-- @@ L1214-1216 verbatim
lemma harmonicAngularLie_generator (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    traceFreeEnd (harmonicField l J*harmonicField l J) ∈ harmonicAngularLie l :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self J)


-- @@ L1218-1219 verbatim
lemma traceFree_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : traceFree M = M-(M.trace/(Fintype.card ι:ℂ)) • 1 := rfl


-- @@ L1221-1224 verbatim
lemma angularRepresentation_toMatrix {s : ℕ} (l : ℕ)
    (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :
    angularRepresentation l M = LinearMap.toMatrixAlgEquiv (homogeneousBasis l)
      (homogeneousField l (splitFieldMatrix M)) := rfl


-- @@ L1226-1230 verbatim
lemma angularRepresentation_toEnd {s : ℕ} (l : ℕ)
    (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :
    (LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm (angularRepresentation l M) =
      homogeneousField l (splitFieldMatrix M) := by
  rw [angularRepresentation_toMatrix,AlgEquiv.symm_apply_apply]


-- @@ L1232-1245 verbatim
lemma homogeneous_traceFree_restriction (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    (LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm
      (traceFree (angularRepresentation l J.matrix*angularRepresentation l J.matrix)) ∈
      liftedTraceLie (harmonicEmbedding l) (harmonicAngularLie l) := by
  let c : ℂ := Matrix.trace (angularRepresentation l J.matrix*angularRepresentation l J.matrix)/
    Fintype.card (MonomialIndex (Fin 8 ⊕ Fin 8) l)
  refine ⟨harmonicField l J*harmonicField l J-c • 1,?_,?_⟩
  · rw [traceFree_apply,map_sub,map_mul,map_smul,map_one,
      angularRepresentation_toEnd]
    ext P : 1
    apply Subtype.ext
    rfl
  · rw [traceFreeEnd_sub_scalar]
    exact harmonicAngularLie_generator l J


-- @@ L1247-1260 verbatim
/-- Every operator generated on homogeneous polynomials has precisely the
trace-free restriction generated on the harmonic subspace. -/
lemma angularLie_harmonic_restriction (l : ℕ)
    {A : Matrix (MonomialIndex (Fin 8 ⊕ Fin 8) l) (MonomialIndex (Fin 8 ⊕ Fin 8) l) ℂ}
    (hA : A ∈ angularLie l) :
    (LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm A ∈
      liftedTraceLie (harmonicEmbedding l) (harmonicAngularLie l) := by
  let L := (liftedTraceLie (harmonicEmbedding l) (harmonicAngularLie l)).comap
    (LinearMap.toMatrixAlgEquiv (homogeneousBasis l)).symm.toAlgHom.toLieHom
  have h : angularLie l ≤ L := by
    apply LieSubalgebra.lieSpan_le.2
    rintro _ ⟨J,rfl⟩
    exact homogeneous_traceFree_restriction l J
  exact h hA


-- @@ L1262-1262 verbatim
end HarmonicCounterexample.Control


-- @@ L1264-1264 verbatim
end


-- @@ L1266-1266 verbatim
noncomputable section

-- @@ L1267-1267 verbatim
open Matrix

-- @@ L1268-1268 verbatim
open scoped BigOperators

-- @@ L1269-1269 verbatim
open scoped Topology

-- @@ L1270-1270 verbatim
open Filter

-- @@ L1271-1271 verbatim
open Matrix

-- @@ L1272-1272 verbatim
open scoped BigOperators

-- @@ L1273-1273 verbatim
open Matrix MvPolynomial

-- @@ L1274-1274 verbatim
open Matrix

-- @@ L1275-1275 verbatim
open scoped BigOperators


-- @@ L1277-1277 verbatim
namespace HarmonicCounterexample.ComplexAngular

-- @@ L1278-1278 verbatim
open MvPolynomial HarmonicCounterexample.Control

-- @@ L1279-1279 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L1281-1290 verbatim
lemma roundPairing_power_eval (l : ℕ)
    (a : {a : (ι ⊕ ι) → ℂ | MvPolynomial.eval a (quadric ι) = 0})
    (P : harmonicSpace ι l) :
    roundPairing l (isotropicPower l a) P =
      (l.factorial:ℂ)*MvPolynomial.eval (a.1 ∘ Sum.swap) P.1 := by
  rw [roundPairing_symm,roundPairing_apply]
  change fischer (swapPolynomial P.1) (linearForm a.1^l) = _
  rw [fischer_linearForm_pow (swapPolynomial_mem_harmonicSpace P.2).1]
  congr 1
  exact MvPolynomial.eval_rename Sum.swap a.1 P.1


-- @@ L1292-1292 verbatim
end HarmonicCounterexample.ComplexAngular


-- @@ L1294-1294 verbatim
end


-- @@ L1296-1296 verbatim
noncomputable section

-- @@ L1297-1297 verbatim
open Matrix

-- @@ L1298-1298 verbatim
open scoped BigOperators

-- @@ L1299-1299 verbatim
open scoped Topology

-- @@ L1300-1300 verbatim
open Filter

-- @@ L1301-1301 verbatim
open Matrix

-- @@ L1302-1302 verbatim
open scoped BigOperators

-- @@ L1303-1303 verbatim
open Matrix MvPolynomial

-- @@ L1304-1304 verbatim
open Matrix

-- @@ L1305-1305 verbatim
open scoped BigOperators


-- @@ L1307-1307 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1308-1308 verbatim
open MvPolynomial HarmonicCounterexample.ComplexAngular

-- @@ L1309-1309 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L1311-1321 verbatim
lemma harmonicRankOne_intertwine (l : ℕ)
    (a : {a : (Fin 8 ⊕ Fin 8) → ℂ | MvPolynomial.eval a (quadric (Fin 8)) = 0}) :
    (homogeneousPowerRankOne l a.1).comp (harmonicEmbedding l) =
      (harmonicEmbedding l).comp ((l.factorial:ℂ)⁻¹ •
        outer (roundPairing l) (isotropicPower l a) (isotropicPower l a)) := by
  ext P : 1
  apply Subtype.ext
  change MvPolynomial.eval (a.1 ∘ Sum.swap) P.1 • linearForm a.1^l =
    (l.factorial:ℂ)⁻¹ • (roundPairing l (isotropicPower l a) P • linearForm a.1^l)
  rw [roundPairing_power_eval,smul_smul,← mul_assoc,inv_mul_cancel₀,one_mul]
  exact_mod_cast Nat.factorial_ne_zero l


-- @@ L1323-1341 verbatim
/-- Every genuine isotropic-power rank-one operator belongs to the Lie algebra
of trace-free squares on the ACTUAL harmonic polynomial space. -/
theorem harmonicAngularLie_rankones (l : ℕ) (hl : 2 ≤ l)
    (a : {a : (Fin 8 ⊕ Fin 8) → ℂ | MvPolynomial.eval a (quadric (Fin 8)) = 0}) :
    outer (roundPairing l) (isotropicPower l a) (isotropicPower l a) ∈ harmonicAngularLie l := by
  have ha : ∑ j : Fin 8,a.1 (.inl j)*a.1 (.inr j) = 0 := by
    simpa only [Set.mem_ofPred_eq,quadric,map_sum,map_mul,eval_X] using a.2
  have hA := angularLie_harmonic_restriction l (angularLie_all_rankones l hl a.1 ha)
  rw [powerRankOneMatrix,AlgEquiv.symm_apply_apply] at hA
  have h := liftedTraceLie_restriction (harmonicEmbedding l) (harmonicEmbedding_injective l)
    (harmonicAngularLie l) hA (harmonicRankOne_intertwine l a)
  have hz : LinearMap.trace ℂ (harmonicSpace (Fin 8) l)
      (outer (roundPairing l) (isotropicPower l a) (isotropicPower l a)) = 0 := by
    rw [outer,LinearMap.trace_smulRight]
    exact roundPairing_isotropicPower l (by omega) a
  rw [map_smul,traceFreeEnd_eq_self hz] at h
  have hm := (harmonicAngularLie l).smul_mem (l.factorial:ℂ) h
  have hc : (l.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  simpa only [smul_smul,mul_inv_cancel₀ hc,one_smul] using hm


-- @@ L1343-1349 verbatim
/-- Full skew algebra producer on genuine harmonic polynomials, with the
correct invariant symmetric form in split coordinates. -/
theorem harmonicAngularLie_wedges (l : ℕ) (hl : 2 ≤ l)
    (u v : harmonicSpace (Fin 8) l) :
    wedgeLeft (roundPairing l) u v ∈ harmonicAngularLie l :=
  wedges_mem_of_isotropic_rankones (harmonicAngularLie l) (roundPairing l)
    (roundPairing_symm l) (roundPairing_injective l) (harmonicAngularLie_rankones l hl) u v


-- @@ L1351-1351 verbatim
end HarmonicCounterexample.Control


-- @@ L1353-1353 verbatim
end


-- @@ L1355-1355 verbatim
noncomputable section

-- @@ L1356-1356 verbatim
open Matrix

-- @@ L1357-1357 verbatim
open scoped BigOperators

-- @@ L1358-1358 verbatim
open scoped Topology

-- @@ L1359-1359 verbatim
open Filter

-- @@ L1360-1360 verbatim
open Matrix

-- @@ L1361-1361 verbatim
open scoped BigOperators

-- @@ L1362-1362 verbatim
open Matrix MvPolynomial

-- @@ L1363-1363 verbatim
open Matrix

-- @@ L1364-1364 verbatim
open scoped BigOperators


-- @@ L1366-1366 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1367-1367 verbatim
open Module

-- @@ L1368-1368 verbatim
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]


-- @@ L1370-1400 verbatim
/-- A symmetric nondegenerate complex bilinear form has a genuine normalized
basis. This uses square roots in ℂ, not a positive-definiteness assumption. -/
theorem exists_bilinear_orthonormal_basis
    (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ x y,B x y = B y x)
    (hinj : Function.Injective B) :
    ∃ b : Basis (Fin (finrank ℂ W)) ℂ W,
      ∀ i j,B (b i) (b j) = if i=j then 1 else 0 := by
  classical
  have hs : LinearMap.IsSymm B := ⟨hB⟩
  obtain ⟨b,hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  have hsep : B.SeparatingLeft := by
    intro x hx
    apply hinj
    ext y
    simpa only [map_zero,LinearMap.zero_apply] using hx y
  have hn (i) : B (b i) (b i) ≠ 0 := hb.not_isOrtho_basis_self_of_separatingLeft hsep i
  obtain ⟨c,hc⟩ := Classical.axiomOfChoice (fun i => IsAlgClosed.exists_eq_mul_self (B (b i) (b i)))
  have hc0 (i) : c i ≠ 0 := by
    intro h
    apply hn i
    rw [hc i,h,zero_mul]
  let d : Fin (finrank ℂ W) → ℂˣ := fun i => Units.mk0 (c i)⁻¹ (inv_ne_zero (hc0 i))
  refine ⟨b.unitsSMul d,?_⟩
  intro i j
  simp only [Basis.unitsSMul_apply,Units.smul_def,map_smul,LinearMap.smul_apply,smul_eq_mul,
    d,Units.val_mk0]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,hc i]
    field_simp [hc0]
  · rw [ite_eq_right hij,hb hij,mul_zero,mul_zero]


-- @@ L1402-1402 verbatim
end HarmonicCounterexample.Control


-- @@ L1404-1404 verbatim
end


-- @@ L1406-1406 verbatim
noncomputable section

-- @@ L1407-1407 verbatim
open Matrix

-- @@ L1408-1408 verbatim
open scoped BigOperators

-- @@ L1409-1409 verbatim
open scoped Topology

-- @@ L1410-1410 verbatim
open Filter

-- @@ L1411-1411 verbatim
open Matrix

-- @@ L1412-1412 verbatim
open scoped BigOperators

-- @@ L1413-1413 verbatim
open Matrix MvPolynomial

-- @@ L1414-1414 verbatim
open Matrix

-- @@ L1415-1415 verbatim
open scoped BigOperators


-- @@ L1417-1417 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1418-1418 verbatim
open Module Matrix

-- @@ L1419-1419 verbatim
open scoped BigOperators

-- @@ L1420-1420 verbatim
variable {W ι : Type*} [AddCommGroup W] [Module ℂ W] [Fintype ι] [DecidableEq ι]


-- @@ L1422-1427 verbatim
lemma bilin_basis_repr (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0) (u : W) (j : ι) :
    B u (b j) = b.repr u j := by
  conv_lhs => rw [← b.sum_repr u]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hb]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]


-- @@ L1429-1434 verbatim
lemma bilin_basis_pairing (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0) (u v : W) :
    B u v = ∑ j : ι,b.repr u j*b.repr v j := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum,map_smul,smul_eq_mul,bilin_basis_repr B b hb]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _


-- @@ L1436-1440 verbatim
lemma real_matrix_complex_orthogonal (R : Matrix ι ι ℝ) (hR : Rᵀ*R=1) :
    (R.map Complex.ofReal)ᵀ*R.map Complex.ofReal = 1 := by
  change (R.map (Complex.ofRealHom))ᵀ * R.map (Complex.ofRealHom) = 1
  rw [← Matrix.transpose_map,← Matrix.map_mul, hR]
  simp


-- @@ L1442-1485 verbatim
/-- An arbitrary nonzero null vector admits genuine normalized bilinear
coordinates u=r(e_i+I e_j). The orthogonal change is constructed from its real
and imaginary coefficient vectors. -/
theorem exists_bilinear_null_basis (B : W →ₗ[ℂ] W →ₗ[ℂ] ℂ) (b : Basis ι ℂ W)
    (hb : ∀ i j,B (b i) (b j) = if i=j then 1 else 0)
    (i j : ι) (hij : i ≠ j) (u : W) (hu : B u u=0) (hn : u ≠ 0) :
    ∃ (b' : Basis ι ℂ W) (r : ℝ),0 < r ∧
      (∀ a c,B (b' a) (b' c) = if a=c then 1 else 0) ∧
       u = (r:ℂ) • (b' i+Complex.I • b' j) := by
  have hz : ∑ a : ι,b.repr u a*b.repr u a = 0 := (bilin_basis_pairing B b hb u u).symm.trans hu
  have hzn : (fun a => b.repr u a) ≠ 0 := by
    intro h
    apply hn
    apply b.repr.injective
    ext a
    simpa using congrFun h a
  obtain ⟨r,R,hr,hR,hzR⟩ := nullVector_orthogonal_frame i j hij _ hz hzn
  let C : Matrix ι ι ℂ := R.map Complex.ofReal
  have hC : Cᵀ*C=1 := real_matrix_complex_orthogonal R hR
  have hC' : C*Cᵀ=1 := mul_eq_one_comm.1 hC
  let e : W ≃ₗ[ℂ] W := Matrix.toLinOfInv b b hC hC'
  let b' : Basis ι ℂ W := b.map e
  have he (a) : b' a = ∑ k : ι,C a k • b k := by
    change Matrix.toLin b b Cᵀ (b a) = _
    rw [Matrix.toLin_self]
    rfl
  refine ⟨b',r,hr,?_,?_⟩
  · intro a c
    rw [he a]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    have hrow (x) : B (b x) (b' c) = C c x := by
      rw [he c]
      simp only [map_sum,map_smul,smul_eq_mul,hb]
      simp
    simp only [hrow]
    have h := congrArg (fun M : Matrix ι ι ℂ => M a c) hC'
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using h
  · rw [he i,he j,Finset.smul_sum,← Finset.sum_add_distrib,Finset.smul_sum]
    rw [← b.sum_repr u]
    apply Finset.sum_congr rfl
    intro a _
    simp only [smul_smul,← add_smul]
    congr 1
    exact hzR a


-- @@ L1487-1487 verbatim
end HarmonicCounterexample.Control


-- @@ L1489-1489 verbatim
end


-- @@ L1491-1491 verbatim
end OAI
