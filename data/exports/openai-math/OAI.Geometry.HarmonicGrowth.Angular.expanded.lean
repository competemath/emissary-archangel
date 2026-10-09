import OAI.Geometry.HarmonicGrowth.RealForms


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L8-8 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L9-9 verbatim
open MvPolynomial Matrix Berger

-- @@ L10-10 verbatim
abbrev PolynomialSpace (n : ℕ) := MvPolynomial (Fin n) ℝ

-- @@ L11-11 verbatim
variable {n : ℕ}

-- @@ L12-13 verbatim
def polynomialLaplacian : PolynomialSpace n →ₗ[ℝ] PolynomialSpace n :=
  ∑ i : Fin n, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap


-- @@ L15-16 verbatim
def harmonicPolynomials (n l : ℕ) : Submodule ℝ (PolynomialSpace n) :=
  homogeneousSubmodule (Fin n) ℝ l ⊓ LinearMap.ker polynomialLaplacian


-- @@ L18-29 verbatim
lemma pderiv_commute (P : PolynomialSpace n) (i j : Fin n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P k hp =>
    simp only [pderiv_mul,map_add,pderiv_X,hp]
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j; rfl
    · subst i; simp [Ne.symm hj]
    · subst j; simp [Ne.symm hi]
    · simp [Ne.symm hi,Ne.symm hj]


-- @@ L31-34 verbatim
/-- Infinitesimal linear coordinate motion: `(M x) · ∇`. -/
def polynomialRotation (M : Mat n) : PolynomialSpace n →ₗ[ℝ] PolynomialSpace n :=
  ∑ i : Fin n, ∑ j : Fin n, M i j •
    ((LinearMap.mulLeft ℝ (X j)).comp (pderiv i).toLinearMap)


-- @@ L36-38 verbatim
lemma polynomialRotation_apply (M : Mat n) (P : PolynomialSpace n) :
    polynomialRotation M P = ∑ i,∑ j,M i j • (X j*pderiv i P) := by
  simp [polynomialRotation]


-- @@ L40-57 verbatim
lemma polynomialRotation_homogeneous {P : PolynomialSpace n} {l : ℕ}
    (hP : P.IsHomogeneous l) (M : Mat n) : (polynomialRotation M P).IsHomogeneous l := by
  rw [polynomialRotation_apply]
  by_cases hl : l = 0
  · have hc : P = C (P.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous (Fin n)).2 (hl ▸ hP))
    rw [hc]
    simp only [pderiv_C,mul_zero,smul_zero,Finset.sum_const_zero]
    exact isHomogeneous_zero (Fin n) ℝ l
  · apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    apply (homogeneousSubmodule (Fin n) ℝ l).smul_mem
    have h := (isHomogeneous_X ℝ j).mul (hP.pderiv (i := i))
    have he : 1+(l-1) = l := by omega
    change (X j*pderiv i P).IsHomogeneous l
    simpa only [he] using h


-- @@ L59-68 verbatim
lemma pderiv_rotation_term (P : PolynomialSpace n) (c : ℝ) (i j k : Fin n) :
    pderiv k (c • (X j*pderiv i P)) =
      c • (X j*pderiv i (pderiv k P)) + if k = j then c • pderiv i P else 0 := by
  rw [(pderiv k).map_smul,pderiv_mul,pderiv_commute P k i]
  by_cases h : k = j
  · subst j
    simp only [pderiv_X_self,one_mul,smul_add,ite_true]
    exact add_comm _ _
  · rw [pderiv_X_of_ne (Ne.symm h)]
    simp [h]


-- @@ L70-74 verbatim
lemma pderiv_rotation (M : Mat n) (P : PolynomialSpace n) (k : Fin n) :
    pderiv k (polynomialRotation M P) = polynomialRotation M (pderiv k P)+
      ∑ i,M i k • pderiv i P := by
  simp only [polynomialRotation_apply,map_sum,pderiv_rotation_term,Finset.sum_add_distrib]
  simp


-- @@ L76-78 verbatim
lemma polynomialLaplacian_apply (P : PolynomialSpace n) :
    polynomialLaplacian P = ∑ i : Fin n,pderiv i (pderiv i P) := by
  simp [polynomialLaplacian]


-- @@ L80-94 verbatim
lemma laplacian_rotation (M : Mat n) (P : PolynomialSpace n) :
    polynomialLaplacian (polynomialRotation M P) =
      polynomialRotation M (polynomialLaplacian P)+
        (2 : ℝ) • (∑ k : Fin n,∑ i : Fin n,M i k • pderiv k (pderiv i P)) := by
  simp only [polynomialLaplacian_apply,pderiv_rotation,map_add,map_sum,
    Derivation.map_smul,Finset.sum_add_distrib]
  have hcomm : (∑ k : Fin n,∑ i : Fin n,M i k • pderiv i (pderiv k P)) =
      ∑ k : Fin n,∑ i : Fin n,M i k • pderiv k (pderiv i P) := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [pderiv_commute P i k]
  rw [hcomm]
  module


-- @@ L96-114 verbatim
lemma laplacian_rotation_skew (M : Mat n) (hM : ∀ i j,M i j = -M j i)
    (P : PolynomialSpace n) :
    polynomialLaplacian (polynomialRotation M P) = polynomialRotation M (polynomialLaplacian P) := by
  have hs : (∑ k : Fin n,∑ i : Fin n,M i k • pderiv k (pderiv i P)) = 0 := by
    let S := ∑ k : Fin n,∑ i : Fin n,M i k • pderiv k (pderiv i P)
    have he : S = -S := by
      unfold S
      conv_lhs => rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [hM k i,pderiv_commute P i k,neg_smul,neg_neg]
    have : (2 : ℝ) • S = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.1 he
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  rw [laplacian_rotation,hs,smul_zero,add_zero]


-- @@ L116-120 verbatim
instance harmonicPolynomials_finite (n l : ℕ) : FiniteDimensional ℝ (harmonicPolynomials n l) := by
  let : FiniteDimensional ℝ (homogeneousSubmodule (Fin n) ℝ l) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin n) ℝ l)
  exact Submodule.finiteDimensional_of_le (show harmonicPolynomials n l ≤
    homogeneousSubmodule (Fin n) ℝ l from inf_le_left)


-- @@ L122-131 verbatim
def rotation (J : ComplexStructure (Fin n)) (l : ℕ) :
    harmonicPolynomials n l →ₗ[ℝ] harmonicPolynomials n l where
  toFun P := ⟨polynomialRotation J.matrix P, polynomialRotation_homogeneous P.property.1 _, by
    change polynomialLaplacian (polynomialRotation J.matrix (P : PolynomialSpace n)) = 0
    rw [laplacian_rotation_skew]
    · rw [show polynomialLaplacian (P : PolynomialSpace n) = 0 from P.property.2,map_zero]
    · intro i j
      exact congrFun (congrFun J.skew j) i⟩
  map_add' P Q := Subtype.ext (map_add _ _ _)
  map_smul' c P := Subtype.ext (map_smul _ _ _)



-- @@ L134-134 verbatim
end HarmonicCounterexample.Angular


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
noncomputable section

-- @@ L139-139 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L141-141 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L142-142 verbatim
open MvPolynomial Finsupp

-- @@ L143-143 verbatim
variable {n : ℕ}


-- @@ L145-146 verbatim
/-- Positive factorial monomial weights of the real Fischer form. -/
def factorialWeight (d : Fin n →₀ ℕ) : ℝ := ∏ i : Fin n, (d i).factorial


-- @@ L148-151 verbatim
lemma factorialWeight_pos (d : Fin n →₀ ℕ) : 0 < factorialWeight d := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast Nat.factorial_pos (d i)


-- @@ L153-166 verbatim
lemma factorialWeight_add_single (d : Fin n →₀ ℕ) (i : Fin n) :
    factorialWeight (d+single i 1) = ((d i:ℝ)+1)*factorialWeight d := by
  classical
  unfold factorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j : Fin n => ((d j).factorial:ℝ)) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, (((d+single i 1 : Fin n →₀ ℕ) j).factorial:ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((d j).factorial:ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Ne.symm (Finset.mem_erase.1 hj).1]
  rw [he]
  simp only [Finsupp.add_apply,single_eq_same,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring


-- @@ L168-171 verbatim
/-- Fischer bilinear form on the actual polynomial coefficient module. -/
def fischer : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (fun d => factorialWeight d • lcoeff ℝ d)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap


-- @@ L173-179 verbatim
lemma fischer_monomial (d : Fin n →₀ ℕ) (c : ℝ) (Q : MvPolynomial (Fin n) ℝ) :
    fischer (monomial d c) Q = c*factorialWeight d*Q.coeff d := by
  change (Finsupp.linearCombination ℝ (fun e : Fin n →₀ ℕ =>
    factorialWeight e • lcoeff ℝ e) (single d c)) Q = _
  rw [Finsupp.linearCombination_single]
  change c*(factorialWeight d*Q.coeff d) = _
  ring


-- @@ L181-184 verbatim
lemma fischer_apply (P Q : MvPolynomial (Fin n) ℝ) :
    fischer P Q = ∑ d ∈ P.support, P.coeff d*factorialWeight d*Q.coeff d := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum,LinearMap.sum_apply,fischer_monomial]


-- @@ L186-196 verbatim
lemma fischer_symm (P Q : MvPolynomial (Fin n) ℝ) : fischer P Q = fischer Q P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    induction Q using MvPolynomial.induction_on' with
    | monomial e b =>
      simp only [fischer_monomial,coeff_monomial]
      by_cases h : d = e
      · subst e; simp only [ite_true]; ring
      · simp [h,Ne.symm h]
    | add Q R hq hr => simp only [map_add,LinearMap.add_apply,hq,hr]
  | add P R hp hr => simp only [map_add,LinearMap.add_apply,hp,hr]


-- @@ L198-202 verbatim
lemma fischer_nonneg (P : MvPolynomial (Fin n) ℝ) : 0 ≤ fischer P P := by
  rw [fischer_apply]
  apply Finset.sum_nonneg
  intro d _
  nlinarith [factorialWeight_pos d,sq_nonneg (P.coeff d)]


-- @@ L204-215 verbatim
lemma fischer_definite {P : MvPolynomial (Fin n) ℝ} (h : fischer P P = 0) : P = 0 := by
  rw [fischer_apply] at h
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun d (_ : d ∈ P.support) =>
    show 0 ≤ P.coeff d*factorialWeight d*P.coeff d by
      nlinarith [factorialWeight_pos d,sq_nonneg (P.coeff d)])).1 h
  ext d
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases hd : d ∈ P.support
  · rcases mul_eq_zero.1 (hh d hd) with h | h
    · exact (mul_eq_zero.1 h).resolve_right (factorialWeight_pos d).ne'
    · exact h
  · exact MvPolynomial.notMem_support_iff.1 hd


-- @@ L217-224 verbatim
lemma fischer_mul_X (P Q : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    fischer (P*X i) Q = fischer P (pderiv i Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [← pow_one (X i),← monomial_add_single,fischer_monomial,fischer_monomial,
      coeff_pderiv,factorialWeight_add_single]
    ring
  | add P R hp hr => simp only [add_mul,map_add,LinearMap.add_apply,hp,hr]


-- @@ L226-231 verbatim
lemma fischer_pderiv (P Q : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    fischer (pderiv i P) Q = fischer P (Q*X i) := by
  calc
    _ = fischer Q (pderiv i P) := fischer_symm _ _
    _ = fischer (Q*X i) P := (fischer_mul_X Q P i).symm
    _ = _ := fischer_symm _ _


-- @@ L233-242 verbatim
/-- The actual polynomial norm is positive definite, not a formal assumed
round-space inner product. Its restriction is rotation invariant. -/
@[instance_reducible]
def fischerCore (n : ℕ) : InnerProductSpace.Core ℝ (MvPolynomial (Fin n) ℝ) where
  inner := fun P Q => fischer P Q
  conj_inner_symm P Q := by simpa only [conj_trivial] using fischer_symm Q P
  re_inner_nonneg P := fischer_nonneg P
  add_left P Q R := by simp only [map_add,LinearMap.add_apply]
  smul_left P Q c := by simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,conj_trivial]
  definite := fun _ h => fischer_definite h


-- @@ L244-244 verbatim
end HarmonicCounterexample.Angular


-- @@ L246-246 verbatim
end


-- @@ L248-248 verbatim
noncomputable section

-- @@ L249-249 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L251-251 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L252-252 verbatim
open MvPolynomial Finsupp

-- @@ L253-253 verbatim
variable {n : ℕ}


-- @@ L255-256 verbatim
instance homogeneous_finite (n l : ℕ) : FiniteDimensional ℝ (homogeneousSubmodule (Fin n) ℝ l) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg (Fin n) ℝ l)


-- @@ L258-259 verbatim
lemma degree_eq_univ_sum (d : Fin n →₀ ℕ) : d.degree = ∑ i : Fin n,d i :=
  Finsupp.sum_fintype d (fun _ a => a) fun _ => rfl


-- @@ L261-272 verbatim
lemma homogeneous_finrank (n l : ℕ) :
    Module.finrank ℝ (homogeneousSubmodule (Fin n) ℝ l) = (n+l-1).choose l := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have he : {d : Fin n →₀ ℕ | d.degree = l} =
      (↑((Finset.univ : Finset (Fin n)).finsuppAntidiag l) : Set (Fin n →₀ ℕ)) := by
    ext d
    simp [Finset.mem_finsuppAntidiag,degree_eq_univ_sum]
  rw [he,(AddMonoidAlgebra.supportedEquivFinsupp
    (R := ℝ) (S := ℝ) (↑((Finset.univ : Finset (Fin n)).finsuppAntidiag l) : Set (Fin n →₀ ℕ))).finrank_eq]
  simp only [Finset.coe_sort_coe,Module.finrank_finsupp,Module.finrank_self,mul_one,
    Fintype.card_coe,Finset.card_finsuppAntidiag_nat_eq_choose,Finset.card_univ,Fintype.card_fin]


-- @@ L274-276 verbatim
/-- The Fischer duality on any actual polynomial subspace. -/
def subFischer (U : Submodule ℝ (MvPolynomial (Fin n) ℝ)) : U →ₗ[ℝ] Module.Dual ℝ U :=
  U.subtype.dualMap.comp (fischer.comp U.subtype)


-- @@ L278-279 verbatim
lemma subFischer_apply (U : Submodule ℝ (MvPolynomial (Fin n) ℝ)) (P Q : U) :
    subFischer U P Q = fischer (P : MvPolynomial (Fin n) ℝ) (Q : MvPolynomial (Fin n) ℝ) := rfl


-- @@ L281-288 verbatim
lemma subFischer_injective (U : Submodule ℝ (MvPolynomial (Fin n) ℝ)) :
    Function.Injective (subFischer U) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  apply Subtype.ext
  apply fischer_definite
  exact congrArg (fun f : Module.Dual ℝ U => f P) hP


-- @@ L290-293 verbatim
lemma subFischer_surjective (U : Submodule ℝ (MvPolynomial (Fin n) ℝ)) [FiniteDimensional ℝ U] :
    Function.Surjective (subFischer U) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := U)).symm).1 (subFischer_injective U)


-- @@ L295-296 verbatim
/-- Squared Euclidean radius as an actual polynomial. -/
def quadraticRadius (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n,X i^2


-- @@ L298-301 verbatim
lemma quadraticRadius_homogeneous (n : ℕ) : (quadraticRadius n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (isHomogeneous_X ℝ i).pow 2


-- @@ L303-307 verbatim
lemma quadraticRadius_ne_zero (hn : 0 < n) : quadraticRadius n ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin n => (1:ℝ))) h
  have : (n:ℝ) = 0 := by simpa [quadraticRadius] using he
  exact (Nat.cast_ne_zero.2 hn.ne') this


-- @@ L309-315 verbatim
lemma fischer_radius_laplacian (P Q : MvPolynomial (Fin n) ℝ) :
    fischer (quadraticRadius n*P) Q = fischer P (∑ i : Fin n,pderiv i (pderiv i Q)) := by
  simp only [quadraticRadius,Finset.sum_mul,map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have he : X i^2*P = (P*X i)*X i := by ring
  rw [he,fischer_mul_X,fischer_mul_X]


-- @@ L317-325 verbatim
/-- Radius multiplication between actual homogeneous parts. -/
def radiusMultiply (n l : ℕ) : homogeneousSubmodule (Fin n) ℝ l →ₗ[ℝ]
    homogeneousSubmodule (Fin n) ℝ (l+2) where
  toFun P := ⟨quadraticRadius n*P, by
    change (quadraticRadius n * (P : MvPolynomial (Fin n) ℝ)).IsHomogeneous (l+2)
    have h := (quadraticRadius_homogeneous n).mul P.property
    simpa only [Nat.add_comm 2 l] using h⟩
  map_add' P Q := Subtype.ext (mul_add _ _ _)
  map_smul' c P := Subtype.ext (mul_smul_comm _ _ _)


-- @@ L327-331 verbatim
lemma radiusMultiply_injective (hn : 0 < n) (l : ℕ) :
    Function.Injective (radiusMultiply n l) := by
  intro P Q h
  apply Subtype.ext
  exact mul_left_cancel₀ (quadraticRadius_ne_zero hn) (congrArg Subtype.val h)


-- @@ L333-344 verbatim
/-- Restricted polynomial Laplacian, between the correct degree spaces. -/
def homogeneousLaplacian (n l : ℕ) : homogeneousSubmodule (Fin n) ℝ (l+2) →ₗ[ℝ]
    homogeneousSubmodule (Fin n) ℝ l where
  toFun P := ⟨∑ i : Fin n,pderiv i (pderiv i (P : MvPolynomial (Fin n) ℝ)), by
    apply IsHomogeneous.sum
    intro i _
    have h := (P.property.pderiv (i := i)).pderiv (i := i)
    simpa only [show l+2-1-1 = l from by omega] using h⟩
  map_add' P Q := by apply Subtype.ext; simp only [Submodule.coe_add,map_add,Finset.sum_add_distrib]
  map_smul' c P := by
    apply Subtype.ext
    simp only [Submodule.coe_smul,Derivation.map_smul,Finset.smul_sum,RingHom.id_apply]


-- @@ L346-361 verbatim
/-- The Laplacian is actually onto: the proof constructs its dual preimage from
injective radius multiplication and positive Fischer duality. -/
lemma homogeneousLaplacian_surjective (hn : 0 < n) (l : ℕ) :
    Function.Surjective (homogeneousLaplacian n l) := by
  intro Q
  obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_of_injective (radiusMultiply_injective hn l)
    (subFischer (homogeneousSubmodule (Fin n) ℝ l) Q)
  obtain ⟨P,hP⟩ := subFischer_surjective (homogeneousSubmodule (Fin n) ℝ (l+2)) φ
  refine ⟨P,subFischer_injective (homogeneousSubmodule (Fin n) ℝ l) ?_⟩
  ext R
  have h := congrArg (fun f : Module.Dual ℝ (homogeneousSubmodule (Fin n) ℝ l) => f R) hφ
  rw [← hP] at h
  change fischer (P : MvPolynomial (Fin n) ℝ) (quadraticRadius n*R) = fischer (Q: MvPolynomial (Fin n) ℝ) R at h
  change fischer (∑ i : Fin n,pderiv i (pderiv i (P : MvPolynomial (Fin n) ℝ))) R = _
  rw [fischer_symm,← fischer_radius_laplacian,fischer_symm]
  exact h


-- @@ L363-363 verbatim
end HarmonicCounterexample.Angular


-- @@ L365-365 verbatim
end


-- @@ L367-367 verbatim
noncomputable section

-- @@ L368-368 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L370-370 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L371-371 verbatim
open MvPolynomial

-- @@ L372-372 verbatim
variable {n : ℕ}


-- @@ L374-390 verbatim
/-- The kernel uses the actual polynomial Laplacian, not an abstract dimension count. -/
def harmonicKernelEquiv (n l : ℕ) : LinearMap.ker (homogeneousLaplacian n l) ≃ₗ[ℝ]
    harmonicPolynomials n (l+2) where
  toFun P := ⟨P.val.val, ⟨P.val.property, by
    change polynomialLaplacian P.val.val = 0
    have h := congrArg Subtype.val P.property
    rw [polynomialLaplacian_apply]
    exact h⟩⟩
  invFun P := ⟨⟨P.val,P.property.1⟩, by
    apply Subtype.ext
    change (∑ i : Fin n,pderiv i (pderiv i P.val)) = 0
    have h : polynomialLaplacian P.val = 0 := P.property.2
    simpa only [polynomialLaplacian_apply] using h⟩
  left_inv P := rfl
  right_inv P := rfl
  map_add' P Q := rfl
  map_smul' c P := rfl


-- @@ L392-399 verbatim
lemma harmonic_finrank_add (hn : 0 < n) (l : ℕ) :
    Module.finrank ℝ (harmonicPolynomials n (l+2)) + (n+l-1).choose l =
      (n+l+1).choose (l+2) := by
  have h := LinearMap.finrank_range_add_finrank_ker (homogeneousLaplacian n l)
  rw [LinearMap.range_eq_top.2 (homogeneousLaplacian_surjective hn l),
    finrank_top,(harmonicKernelEquiv n l).finrank_eq,homogeneous_finrank] at h
  rw [homogeneous_finrank] at h
  simpa only [show n+(l+2)-1 = n+l+1 from by omega, Nat.add_comm] using h


-- @@ L401-405 verbatim
lemma harmonic_finrank_succ_succ (hn : 0 < n) (l : ℕ) :
    Module.finrank ℝ (harmonicPolynomials n (l+2)) =
      (n+l+1).choose (l+2) - (n+l-1).choose l := by
  have h := harmonic_finrank_add hn l
  omega


-- @@ L407-416 verbatim
/-- Fischer decomposition obstruction: no nonzero harmonic polynomial is
itself a multiple of the squared radius. -/
lemma harmonic_radius_multiple_zero (P Q : PolynomialSpace n)
    (hP : polynomialLaplacian P = 0) (hQ : P = quadraticRadius n*Q) : P = 0 := by
  apply fischer_definite
  calc
    fischer P P = fischer (quadraticRadius n*Q) P := congrArg (fun R => fischer R P) hQ
    _ = fischer Q (polynomialLaplacian P) := by
      rw [polynomialLaplacian_apply,fischer_radius_laplacian]
    _ = 0 := by rw [hP,map_zero]


-- @@ L418-418 verbatim
end HarmonicCounterexample.Angular


-- @@ L420-420 verbatim
end


-- @@ L422-422 verbatim
noncomputable section

-- @@ L423-423 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L425-425 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L426-426 verbatim
open MvPolynomial

-- @@ L427-427 verbatim
variable {n : ℕ}


-- @@ L429-432 verbatim
lemma pderiv_homogeneous_zero {P : PolynomialSpace n} (hP : P.IsHomogeneous 0) (i : Fin n) :
    pderiv i P = 0 := by
  have hc := totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous (Fin n)).2 hP)
  rw [hc,pderiv_C]


-- @@ L434-439 verbatim
lemma polynomialLaplacian_low {P : PolynomialSpace n} {l : ℕ}
    (hP : P.IsHomogeneous l) (hl : l ≤ 1) : polynomialLaplacian P = 0 := by
  rw [polynomialLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact pderiv_homogeneous_zero (by simpa only [show l-1 = 0 from by omega] using hP.pderiv (i := i)) i


-- @@ L441-446 verbatim
lemma harmonicPolynomials_low (n l : ℕ) (hl : l ≤ 1) :
    harmonicPolynomials n l = homogeneousSubmodule (Fin n) ℝ l := by
  apply le_antisymm
  · exact inf_le_left
  · intro P hP
    exact ⟨hP,polynomialLaplacian_low hP hl⟩


-- @@ L448-450 verbatim
lemma harmonic_finrank_zero (n : ℕ) : Module.finrank ℝ (harmonicPolynomials n 0) = 1 := by
  rw [harmonicPolynomials_low n 0 (by omega),homogeneous_finrank]
  exact Nat.choose_zero_right _


-- @@ L452-454 verbatim
lemma harmonic_finrank_one (n : ℕ) : Module.finrank ℝ (harmonicPolynomials n 1) = n := by
  rw [harmonicPolynomials_low n 1 (by omega),homogeneous_finrank]
  simp


-- @@ L456-467 verbatim
/-- A finite mixture of distinct homogeneous degrees has unique coefficients. -/
lemma homogeneous_components_independent {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : Function.Injective d) (P : ι → PolynomialSpace n)
    (hP : ∀ i,(P i).IsHomogeneous (d i)) (hz : ∑ i,P i = 0) : ∀ i,P i = 0 := by
  classical
  intro i
  have h := congrArg (homogeneousComponent (d i)) hz
  simp only [map_sum,map_zero] at h
  have he (j : ι) : homogeneousComponent (d i) (P j) = if i = j then P j else 0 := by
    simp only [homogeneousComponent_of_mem (hP j),hd.eq_iff]
  simp only [he,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at h
  exact h


-- @@ L469-469 verbatim
end HarmonicCounterexample.Angular


-- @@ L471-471 verbatim
end


-- @@ L473-473 verbatim
noncomputable section

-- @@ L474-474 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L476-476 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L477-477 verbatim
open MvPolynomial




-- @@ L481-499 verbatim
lemma sum_harmonic_finrank (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (∑ l ∈ Finset.range (k+2),Module.finrank ℝ (harmonicPolynomials n l)) =
      (n+k).choose (k+1) + (n+k-1).choose k := by
  induction k with
  | zero =>
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [harmonic_finrank_zero,harmonic_finrank_one]
    simp only [Nat.add_zero,Nat.choose_one_right,Nat.choose_zero_right]
    omega
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 from by omega,Finset.sum_range_succ,ih]
    have h := harmonic_finrank_add hn k
    have he : n+(k+1) = n+k+1 := by omega
    have hf : n+k+1-1 = n+k := by omega
    rw [he,hf]
    change (n+k).choose (k+1) + (n+k-1).choose k +
      Module.finrank ℝ (harmonicPolynomials n (k+2)) =
      (n+k+1).choose (k+2) + (n+k).choose (k+1)
    omega


-- @@ L501-501 verbatim
end HarmonicCounterexample.Angular


-- @@ L503-503 verbatim
end


-- @@ L505-505 verbatim
noncomputable section

-- @@ L506-506 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L508-508 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L509-509 verbatim
open MvPolynomial Matrix

-- @@ L510-510 verbatim
variable {n : ℕ}


-- @@ L512-523 verbatim
/-- The infinitesimal rotation has its genuine Fischer adjoint. -/
lemma fischer_rotation (M : Mat n) (P Q : PolynomialSpace n) :
    fischer (polynomialRotation M P) Q = fischer P (polynomialRotation M.transpose Q) := by
  simp only [polynomialRotation_apply,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    smul_eq_mul,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [mul_comm (X j),fischer_mul_X,fischer_pderiv,mul_comm _ (X i)]


-- @@ L525-532 verbatim
lemma polynomialRotation_transpose_skew (M : Mat n) (hM : ∀ i j,M i j = -M j i)
    (P : PolynomialSpace n) : polynomialRotation M.transpose P = -polynomialRotation M P := by
  simp only [polynomialRotation_apply,Matrix.transpose_apply,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hM j i,neg_smul]


-- @@ L534-537 verbatim
lemma fischer_rotation_skew (M : Mat n) (hM : ∀ i j,M i j = -M j i)
    (P Q : PolynomialSpace n) :
    fischer (polynomialRotation M P) Q = -fischer P (polynomialRotation M Q) := by
  rw [fischer_rotation,polynomialRotation_transpose_skew M hM,map_neg]


-- @@ L539-558 verbatim
/-- A sum of Fischer pairings satisfies Cauchy--Schwarz; this avoids introducing
any assumed angular norm or a topological completion of the polynomial module. -/
lemma fischer_family_cauchy {ι : Type*} [Fintype ι]
    (P Q : ι → PolynomialSpace n) :
    (∑ i,fischer (P i) (Q i))^2 ≤
      (∑ i,fischer (P i) (P i))*(∑ i,fischer (Q i) (Q i)) := by
  have hp (t : ℝ) : 0 ≤ (∑ i,fischer (P i) (P i))*t^2+
      (2*(∑ i,fischer (P i) (Q i)))*t+(∑ i,fischer (Q i) (Q i)) := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => fischer_nonneg (t • P i+Q i))
    simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul] at h
    have he : (∑ i,fischer (Q i) (P i)) = ∑ i,fischer (P i) (Q i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact fischer_symm _ _
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
    rw [he] at h
    nlinarith
  have h := discrim_le_zero (fun t => by simpa only [sq] using hp t)
  unfold discrim at h
  nlinarith


-- @@ L560-571 verbatim
lemma fischer_gradient_energy {l : ℕ} {P : PolynomialSpace n} (hP : P.IsHomogeneous l) :
    (∑ i : Fin n,fischer (pderiv i P) (pderiv i P)) = (l:ℝ)*fischer P P := by
  calc
    _ = fischer P (∑ i : Fin n,X i*pderiv i P) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [fischer_pderiv,mul_comm]
    _ = _ := by
      rw [hP.sum_X_mul_pderiv]
      rw [map_nsmul]
      simp only [nsmul_eq_mul]


-- @@ L573-593 verbatim
/-- Orthogonal change of the gradient preserves its Fischer energy. -/
lemma fischer_gradient_orthogonal (M : Mat n)
    (hM : ∀ i k, (∑ j : Fin n,M i j*M k j) = if i = k then 1 else 0)
    (P : PolynomialSpace n) :
    (∑ j : Fin n,fischer (∑ i : Fin n,M i j • pderiv i P)
      (∑ k : Fin n,M k j • pderiv k P)) =
      ∑ i : Fin n,fischer (pderiv i P) (pderiv i P) := by
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have he (k : Fin n) :
      (∑ j : Fin n,M i j*(M k j*fischer (pderiv k P) (pderiv i P))) =
      (if i = k then 1 else 0)*fischer (pderiv k P) (pderiv i P) := by
    rw [← hM i k,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [he,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]


-- @@ L595-595 verbatim
end HarmonicCounterexample.Angular


-- @@ L597-597 verbatim
end


-- @@ L599-599 verbatim
noncomputable section

-- @@ L600-600 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L602-602 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L603-603 verbatim
open MvPolynomial Matrix

-- @@ L604-604 verbatim
variable {n : ℕ}


-- @@ L606-611 verbatim
lemma polynomialRotation_gradient (M : Mat n) (P : PolynomialSpace n) :
    polynomialRotation M P = ∑ j : Fin n,X j*(∑ i : Fin n,M i j • pderiv i P) := by
  rw [polynomialRotation_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum,mul_smul_comm]


-- @@ L613-639 verbatim
/-- The sharp degree-l rotation bound, proved on genuine polynomials by
Fischer duality, Euler's identity, and Cauchy--Schwarz. -/
lemma fischer_rotation_bound (M : Mat n)
    (hM : ∀ i k, (∑ j : Fin n,M i j*M k j) = if i = k then 1 else 0)
    {P : PolynomialSpace n} {l : ℕ} (hP : P.IsHomogeneous l) :
    fischer (polynomialRotation M P) (polynomialRotation M P) ≤
      (l:ℝ)^2*fischer P P := by
  let R : Fin n → PolynomialSpace n := fun j => ∑ i : Fin n,M i j • pderiv i P
  have he : fischer (polynomialRotation M P) (polynomialRotation M P) =
      ∑ j : Fin n,fischer (R j) (pderiv j (polynomialRotation M P)) := by
    conv_lhs => arg 1; rw [polynomialRotation_gradient]
    simp only [map_sum,LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (X j),fischer_mul_X]
  have hR : (∑ j : Fin n,fischer (R j) (R j)) = (l:ℝ)*fischer P P :=
    (fischer_gradient_orthogonal M hM P).trans (fischer_gradient_energy hP)
  have hS := fischer_gradient_energy (polynomialRotation_homogeneous hP M)
  have hc := fischer_family_cauchy R (fun j => pderiv j (polynomialRotation M P))
  rw [← he,hR,hS] at hc
  have hn := fischer_nonneg (polynomialRotation M P)
  by_cases hz : fischer (polynomialRotation M P) (polynomialRotation M P) = 0
  · rw [hz]
    exact mul_nonneg (sq_nonneg _) (fischer_nonneg P)
  · have hp := lt_of_le_of_ne hn (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := fischer (polynomialRotation M P) (polynomialRotation M P)) _ hp
    nlinarith


-- @@ L641-646 verbatim
lemma fischer_square_rotation_nonpos (M : Mat n) (hM : ∀ i j,M i j = -M j i)
    (P : PolynomialSpace n) :
    fischer P (polynomialRotation M (polynomialRotation M P)) ≤ 0 := by
  have h := fischer_nonneg (polynomialRotation M P)
  rw [fischer_rotation_skew M hM] at h
  linarith


-- @@ L648-654 verbatim
lemma fischer_square_rotation_lower (M : Mat n) (hSkew : ∀ i j,M i j = -M j i)
    (hOrth : ∀ i k, (∑ j : Fin n,M i j*M k j) = if i = k then 1 else 0)
    {P : PolynomialSpace n} {l : ℕ} (hP : P.IsHomogeneous l) :
    -(l:ℝ)^2*fischer P P ≤ fischer P (polynomialRotation M (polynomialRotation M P)) := by
  have h := fischer_rotation_bound M hOrth hP
  rw [fischer_rotation_skew M hSkew] at h
  linarith


-- @@ L656-656 verbatim
end HarmonicCounterexample.Angular


-- @@ L658-658 verbatim
end


-- @@ L660-660 verbatim
noncomputable section

-- @@ L661-661 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L663-663 verbatim
namespace HarmonicCounterexample.Angular

-- @@ L664-664 verbatim
open MvPolynomial Matrix Berger

-- @@ L665-665 verbatim
variable {n : ℕ}


-- @@ L667-668 verbatim
@[reducible] instance polynomialNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (PolynomialSpace n) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := fischerCore n)


-- @@ L670-673 verbatim
/-- Override the unrelated power-series coefficient topology with the topology
of the Fischer norm; the underlying polynomial algebra is unchanged. -/
@[reducible] instance polynomialUniformSpace (n : ℕ) : UniformSpace (PolynomialSpace n) :=
  (polynomialNormedAddCommGroup n).toMetricSpace.toUniformSpace


-- @@ L675-676 verbatim
@[reducible] instance polynomialTopologicalSpace (n : ℕ) : TopologicalSpace (PolynomialSpace n) :=
  (polynomialUniformSpace n).toTopologicalSpace


-- @@ L678-679 verbatim
@[reducible] instance polynomialInnerProductSpace (n : ℕ) : InnerProductSpace ℝ (PolynomialSpace n) :=
  InnerProductSpace.ofCore (fischerCore n).toCore


-- @@ L681-682 verbatim
@[reducible] instance harmonicNormedAddCommGroup (n l : ℕ) : NormedAddCommGroup (harmonicPolynomials n l) :=
  Submodule.normedAddCommGroup _

-- @@ L683-684 verbatim
@[reducible] instance harmonicSeminormedAddCommGroup (n l : ℕ) : SeminormedAddCommGroup (harmonicPolynomials n l) :=
  (harmonicNormedAddCommGroup n l).toSeminormedAddCommGroup

-- @@ L685-686 verbatim
@[reducible] instance harmonicTopologicalSpace (n l : ℕ) : TopologicalSpace (harmonicPolynomials n l) :=
  (harmonicNormedAddCommGroup n l).toMetricSpace.toUniformSpace.toTopologicalSpace

-- @@ L687-688 verbatim
@[reducible] instance harmonicUniformSpace (n l : ℕ) : UniformSpace (harmonicPolynomials n l) :=
  (harmonicNormedAddCommGroup n l).toMetricSpace.toUniformSpace

-- @@ L689-690 verbatim
@[reducible] instance harmonicInnerProductSpace (n l : ℕ) : InnerProductSpace ℝ (harmonicPolynomials n l) :=
  Submodule.innerProductSpace _


-- @@ L692-694 verbatim
instance harmonicOperatorNormSMulClass (n l : ℕ) :
    NormSMulClass ℝ (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) :=
  @NormedSpace.toNormSMulClass ℝ (harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l) _ _ _



-- @@ L697-697 verbatim
lemma polynomial_inner (P Q : PolynomialSpace n) : ⟪P,Q⟫_ℝ = fischer P Q := rfl


-- @@ L699-700 verbatim
lemma harmonic_inner {l : ℕ} (P Q : harmonicPolynomials n l) :
    ⟪P,Q⟫_ℝ = fischer (P : PolynomialSpace n) (Q : PolynomialSpace n) := rfl


-- @@ L702-705 verbatim
/-- The genuine infinitesimal Hopf operator as a bounded operator on V_l. -/
def rotationCLM (J : ComplexStructure (Fin n)) (l : ℕ) :
    harmonicPolynomials n l →L[ℝ] harmonicPolynomials n l :=
  LinearMap.toContinuousLinearMap (rotation J l)


-- @@ L707-710 verbatim
lemma rotationCLM_inner_skew (J : ComplexStructure (Fin n)) (l : ℕ)
    (P Q : harmonicPolynomials n l) :
    ⟪rotationCLM J l P,Q⟫_ℝ = -⟪P,rotationCLM J l Q⟫_ℝ := by
  exact fischer_rotation_skew J.matrix (fun i j => congrFun (congrFun J.skew j) i) _ _


-- @@ L712-717 verbatim
lemma complexStructure_rows (J : ComplexStructure (Fin n)) (i k : Fin n) :
    (∑ j : Fin n,J.matrix i j*J.matrix k j) = if i = k then 1 else 0 := by
  have hm : J.matrix * J.matrix.transpose = 1 := by
    rw [J.skew,mul_neg,J.square,neg_neg]
  have h := congrFun (congrFun hm i) k
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using h


-- @@ L719-725 verbatim
lemma rotationCLM_norm_le (J : ComplexStructure (Fin n)) (l : ℕ)
    (P : harmonicPolynomials n l) : ‖rotationCLM J l P‖ ≤ (l:ℝ)*‖P‖ := by
  have h := fischer_rotation_bound J.matrix (complexStructure_rows J) P.property.1
  change ⟪rotationCLM J l P,rotationCLM J l P⟫_ℝ ≤ (l:ℝ)^2*⟪P,P⟫_ℝ at h
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Nat.cast_nonneg l) (norm_nonneg P))
  nlinarith


-- @@ L727-729 verbatim
lemma rotationCLM_opNorm_le (J : ComplexStructure (Fin n)) (l : ℕ) :
    ‖rotationCLM J l‖ ≤ l :=
  ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg l) (rotationCLM_norm_le J l)


-- @@ L731-736 verbatim
lemma rotationCLM_square_symmetric (J : ComplexStructure (Fin n)) (l : ℕ) :
    (rotationCLM J l*rotationCLM J l).IsSymmetric := by
  intro P Q
  change ⟪rotationCLM J l (rotationCLM J l P),Q⟫_ℝ =
    ⟪P,rotationCLM J l (rotationCLM J l Q)⟫_ℝ
  rw [rotationCLM_inner_skew,rotationCLM_inner_skew,neg_neg]


-- @@ L738-741 verbatim
lemma rotationCLM_square_nonpos (J : ComplexStructure (Fin n)) (l : ℕ)
    (P : harmonicPolynomials n l) : ⟪P,(rotationCLM J l*rotationCLM J l) P⟫_ℝ ≤ 0 := by
  exact fischer_square_rotation_nonpos J.matrix
    (fun i j => congrFun (congrFun J.skew j) i) _


-- @@ L743-749 verbatim
lemma rotationCLM_square_lower (J : ComplexStructure (Fin n)) (l : ℕ)
    (P : harmonicPolynomials n l) :
    -(l:ℝ)^2*‖P‖^2 ≤ ⟪P,(rotationCLM J l*rotationCLM J l) P⟫_ℝ := by
  have h := fischer_square_rotation_lower J.matrix
    (fun i j => congrFun (congrFun J.skew j) i) (complexStructure_rows J) P.property.1
  change -(l:ℝ)^2*⟪P,P⟫_ℝ ≤ ⟪P,(rotationCLM J l*rotationCLM J l) P⟫_ℝ at h
  simpa only [real_inner_self_eq_norm_sq] using h


-- @@ L751-751 verbatim
end HarmonicCounterexample.Angular


-- @@ L753-753 verbatim
end


-- @@ L755-755 verbatim
noncomputable section

-- @@ L756-756 verbatim
open scoped BigOperators


-- @@ L758-758 verbatim
namespace HarmonicCounterexample.Control

-- @@ L759-759 verbatim
open MvPolynomial Matrix

-- @@ L760-760 verbatim
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]


-- @@ L762-764 verbatim
def directionalPolynomial (M : Matrix ι ι 𝕜) (i : ι) :
    MvPolynomial ι 𝕜 →ₗ[𝕜] MvPolynomial ι 𝕜 :=
  ∑ j : ι,M j i • (pderiv j).toLinearMap


-- @@ L766-769 verbatim
omit [DecidableEq ι] in
lemma directionalPolynomial_apply (M : Matrix ι ι 𝕜) (i : ι) (P : MvPolynomial ι 𝕜) :
    directionalPolynomial M i P=∑ j : ι,M j i • pderiv j P := by
  simp [directionalPolynomial]


-- @@ L771-776 verbatim
omit [DecidableEq ι] in
lemma directionalPolynomial_mul (M : Matrix ι ι 𝕜) (i : ι) (P Q : MvPolynomial ι 𝕜) :
    directionalPolynomial M i (P*Q)=
      directionalPolynomial M i P*Q+P*directionalPolynomial M i Q := by
  simp only [directionalPolynomial_apply,pderiv_mul,smul_add,Finset.sum_add_distrib,
    smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum]


-- @@ L778-788 verbatim
lemma pderiv_linearChange (M : Matrix ι ι 𝕜) (i : ι) (P : MvPolynomial ι 𝕜) :
    pderiv i (linearChange M P)=linearChange M (directionalPolynomial M i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [linearChange,directionalPolynomial_apply]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P j hp =>
    rw [map_mul,pderiv_mul,directionalPolynomial_mul,map_add,map_mul,map_mul,← hp]
    congr 1
    congr 1
    simp only [linearChange_X,map_sum,Derivation.map_smul,pderiv_X]
    simp [directionalPolynomial_apply,linearChange,Pi.single_apply]


-- @@ L790-791 verbatim
def ordinaryLaplacian : MvPolynomial ι 𝕜 →ₗ[𝕜] MvPolynomial ι 𝕜 :=
  ∑ i : ι,(pderiv i).toLinearMap.comp (pderiv i).toLinearMap


-- @@ L793-795 verbatim
omit [DecidableEq ι] in
lemma ordinaryLaplacian_apply (P : MvPolynomial ι 𝕜) :
    ordinaryLaplacian P=∑ i : ι,pderiv i (pderiv i P) := by simp [ordinaryLaplacian]


-- @@ L797-813 verbatim
lemma ordinaryLaplacian_linearChange (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    ordinaryLaplacian (linearChange M P)=
      linearChange M (∑ j : ι,∑ k : ι,(M*M.transpose) j k • pderiv j (pderiv k P)) := by
  simp only [ordinaryLaplacian_apply,pderiv_linearChange]
  rw [← map_sum]
  congr 1
  simp only [directionalPolynomial_apply,map_sum,Derivation.map_smul,
    smul_smul,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,pderiv_commutes]


-- @@ L815-824 verbatim
omit [DecidableEq ι] in
lemma ordinaryLaplacian_rename {τ : Type*} [Fintype τ] (e : ι ≃ τ)
    (P : MvPolynomial ι 𝕜) :
    ordinaryLaplacian (rename e P)=rename e (ordinaryLaplacian P) := by
  classical
  simp only [ordinaryLaplacian_apply,map_sum]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_rename e.injective,pderiv_rename e.injective]


-- @@ L826-830 verbatim
omit [DecidableEq ι] in
lemma ordinaryLaplacian_map {𝕜' : Type*} [Field 𝕜'] (f : 𝕜 →+* 𝕜')
    (P : MvPolynomial ι 𝕜) : ordinaryLaplacian (MvPolynomial.map f P)=
      MvPolynomial.map f (ordinaryLaplacian P) := by
  simp only [ordinaryLaplacian_apply,map_sum,pderiv_map]


-- @@ L832-832 verbatim
end HarmonicCounterexample.Control


-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
noncomputable section

-- @@ L837-837 verbatim
open scoped BigOperators


-- @@ L839-839 verbatim
namespace HarmonicCounterexample.Berger.ComplexStructure

-- @@ L840-840 verbatim
open Matrix

-- @@ L841-847 verbatim
lemma splitChange_gram (s : ℕ) :
    splitChange s*(splitChange s).transpose=fromBlocks 0 (2 : Matrix (Fin s) (Fin s) ℂ) 2 0 := by
  simp only [splitChange,fromBlocks_transpose,transpose_one,transpose_smul,fromBlocks_multiply,
    mul_one,mul_smul_comm,smul_smul]
  ext a b
  rcases a with a|a <;> rcases b with b|b <;>
    by_cases hab : a=b <;> simp [Matrix.fromBlocks,Matrix.ofNat_apply,hab] <;> norm_num

-- @@ L848-848 verbatim
end HarmonicCounterexample.Berger.ComplexStructure


-- @@ L850-850 verbatim
end


-- @@ L852-852 verbatim
noncomputable section

-- @@ L853-853 verbatim
open scoped BigOperators


-- @@ L855-855 verbatim
namespace HarmonicCounterexample.Control

-- @@ L856-856 verbatim
open MvPolynomial Matrix HarmonicCounterexample.Berger.ComplexStructure

-- @@ L857-857 verbatim
open HarmonicCounterexample.ComplexAngular


-- @@ L859-874 verbatim
lemma ordinaryLaplacian_split (s : ℕ) (P : SplitPolynomial (Fin s)) :
    ordinaryLaplacian (linearChange (splitChange s) P)=
      (4:ℂ) • linearChange (splitChange s) (mixedLaplacian P) := by
  rw [ordinaryLaplacian_linearChange,splitChange_gram]
  rw [← map_smul]
  congr 1
  simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_smul,Finset.sum_const_zero,
    zero_add,add_zero,Matrix.ofNat_apply]
  rw [mixedLaplacian_apply,Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  rw [pderiv_commutes P (Sum.inl i) (Sum.inr i), ← add_smul]
  norm_num


-- @@ L876-881 verbatim
lemma linearChange_injective {s : ℕ} : Function.Injective (linearChange (splitChange s)) := by
  intro P Q h
  have he := congrArg (linearChange (unsplitChange s)) h
  change ((linearChange (unsplitChange s)).comp (linearChange (splitChange s))) P=
    ((linearChange (unsplitChange s)).comp (linearChange (splitChange s))) Q at he
  simpa only [linearChange_comp,split_unsplit,linearChange_one,AlgHom.id_apply] using he


-- @@ L883-883 verbatim
end HarmonicCounterexample.Control


-- @@ L885-885 verbatim
end


-- @@ L887-887 verbatim
noncomputable section



-- @@ L890-890 verbatim
namespace HarmonicCounterexample.Control

-- @@ L891-891 verbatim
open MvPolynomial

-- @@ L892-892 verbatim
open scoped BigOperators

-- @@ L893-893 verbatim
variable {ι : Type*}


-- @@ L895-898 verbatim
def realCoefficients : MvPolynomial ι ℂ →ₗ[ℝ] MvPolynomial ι ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap Complex.reLm).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)


-- @@ L900-901 verbatim
lemma coeff_realCoefficients (P : MvPolynomial ι ℂ) (d : ι →₀ ℕ) :
    (realCoefficients P).coeff d=(P.coeff d).re := rfl


-- @@ L903-906 verbatim
lemma realCoefficients_ofReal (P : MvPolynomial ι ℝ) :
    realCoefficients (MvPolynomial.map Complex.ofRealHom P)=P := by
  ext d
  simp only [coeff_realCoefficients,coeff_map,Complex.ofRealHom_eq_coe,Complex.ofReal_re]


-- @@ L908-920 verbatim
lemma ofReal_realCoefficients {P : MvPolynomial ι ℂ}
    (hP : ComplexAngular.conjugate P=P) :
    MvPolynomial.map Complex.ofRealHom (realCoefficients P)=P := by
  ext d
  rw [coeff_map,coeff_realCoefficients]
  have hh := congrArg (fun polynomial => polynomial.coeff d) hP
  rw [ComplexAngular.coeff_conjugate] at hh
  have hz : (P.coeff d).im=0 := by
    have hi := congrArg Complex.im hh
    change -(P.coeff d).im=(P.coeff d).im at hi
    linarith
  simp only [Complex.ofRealHom_eq_coe]
  exact Complex.ext (by simp) (by simp [hz])


-- @@ L922-929 verbatim
lemma realCoefficients_homogeneous {P : MvPolynomial ι ℂ} {l : ℕ}
    (hP : P.IsHomogeneous l) : (realCoefficients P).IsHomogeneous l := by
  intro d hd
  apply hP
  rw [coeff_realCoefficients] at hd
  intro hc
  apply hd
  simp [hc]


-- @@ L931-931 verbatim
variable [Fintype ι]

-- @@ L932-937 verbatim
lemma ordinaryLaplacian_realCoefficients (P : MvPolynomial ι ℂ) :
    ordinaryLaplacian (realCoefficients P)=realCoefficients (ordinaryLaplacian P) := by
  ext d
  simp only [ordinaryLaplacian_apply,map_sum,coeff_sum,coeff_realCoefficients,coeff_pderiv]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero,mul_zero,sub_zero]


-- @@ L939-939 verbatim
end HarmonicCounterexample.Control


-- @@ L941-941 verbatim
end


-- @@ L943-943 verbatim
noncomputable section



-- @@ L946-946 verbatim
namespace HarmonicCounterexample.Control

-- @@ L947-947 verbatim
open MvPolynomial Matrix

-- @@ L948-948 verbatim
open HarmonicCounterexample.Berger.ComplexStructure HarmonicCounterexample.ComplexAngular

-- @@ L949-949 verbatim
open scoped BigOperators


-- @@ L951-954 verbatim
lemma linearChange_split_inl (s : ℕ) (i : Fin s) :
    linearChange (splitChange s) (X (Sum.inl i))=
      X (Sum.inl i)+Complex.I • X (Sum.inr i) := by
  simp [linearChange_X,splitChange,Fintype.sum_sum_type,Matrix.one_apply]


-- @@ L956-959 verbatim
lemma linearChange_split_inr (s : ℕ) (i : Fin s) :
    linearChange (splitChange s) (X (Sum.inr i))=
      X (Sum.inl i)-Complex.I • X (Sum.inr i) := by
  simp [linearChange_X,splitChange,Fintype.sum_sum_type,Matrix.one_apply,sub_eq_add_neg]


-- @@ L961-968 verbatim
lemma conjugate_split_X (s : ℕ) (i : Fin s ⊕ Fin s) :
    conjugate (linearChange (splitChange s) (X i))=
      linearChange (splitChange s) (X (Sum.swap i)) := by
  rcases i with i|i
  · rw [Sum.swap_inl,linearChange_split_inl,linearChange_split_inr]
    simp [conjugate,smul_eq_C_mul,sub_eq_add_neg]
  · rw [Sum.swap_inr,linearChange_split_inr,linearChange_split_inl]
    simp [conjugate,smul_eq_C_mul]


-- @@ L970-978 verbatim
lemma conjugate_split (s : ℕ) (P : SplitPolynomial (Fin s)) :
    conjugate (linearChange (splitChange s) P)=
      linearChange (splitChange s) (realConjugatePolynomial P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [linearChange,conjugate,realConjugatePolynomial,swapPolynomial]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    rw [map_mul,map_mul,realConjugatePolynomial_mul,map_mul,hP,
      realConjugatePolynomial_X,conjugate_split_X]


-- @@ L980-983 verbatim
/-- The literal Cartesian coefficient substitution z=x+iy,w=x-iy, including
 the index identification with the ambient Euclidean R^16. -/
def cartesianChange : SplitPolynomial (Fin 8) →ₐ[ℂ] MvPolynomial (Fin 16) ℂ :=
  (rename (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16)).comp (linearChange (splitChange 8))


-- @@ L985-987 verbatim
def inverseCartesianChange : MvPolynomial (Fin 16) ℂ →ₐ[ℂ] SplitPolynomial (Fin 8) :=
  (linearChange (unsplitChange 8)).comp
    (rename ((finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm))


-- @@ L989-994 verbatim
lemma inverse_cartesianChange (P : SplitPolynomial (Fin 8)) :
    inverseCartesianChange (cartesianChange P)=P := by
  simp only [inverseCartesianChange,cartesianChange,AlgHom.comp_apply,rename_rename,
    Equiv.symm_comp_self,rename_id]
  change ((linearChange (unsplitChange 8)).comp (linearChange (splitChange 8))) P=P
  rw [linearChange_comp,split_unsplit,linearChange_one,AlgHom.id_apply]


-- @@ L996-1009 verbatim
lemma cartesianChange_inverse (P : MvPolynomial (Fin 16) ℂ) :
    cartesianChange (inverseCartesianChange P)=P := by
  have hc := congrArg (fun f : SplitPolynomial (Fin 8) →ₐ[ℂ] SplitPolynomial (Fin 8) =>
    f (rename ((finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm) P))
      (linearChange_comp (splitChange 8) (unsplitChange 8))
  rw [unsplit_split,linearChange_one] at hc
  change rename (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16)
    (linearChange (splitChange 8) (linearChange (unsplitChange 8)
      (rename ((finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm) P)))=P
  rw [show linearChange (splitChange 8) (linearChange (unsplitChange 8)
    (rename ((finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm) P))=
    rename ((finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm) P from hc]
  rw [rename_rename]
  simp


-- @@ L1011-1012 verbatim
lemma cartesianChange_injective : Function.Injective cartesianChange :=
  Function.LeftInverse.injective inverse_cartesianChange


-- @@ L1014-1016 verbatim
lemma cartesianChange_homogeneous {P : SplitPolynomial (Fin 8)} {l : ℕ}
    (hP : P.IsHomogeneous l) : (cartesianChange P).IsHomogeneous l :=
  (linearChange_homogeneous hP _).rename_isHomogeneous


-- @@ L1018-1020 verbatim
lemma inverseCartesianChange_homogeneous {P : MvPolynomial (Fin 16) ℂ} {l : ℕ}
    (hP : P.IsHomogeneous l) : (inverseCartesianChange P).IsHomogeneous l :=
  linearChange_homogeneous hP.rename_isHomogeneous _


-- @@ L1022-1028 verbatim
lemma conjugate_cartesianChange (P : SplitPolynomial (Fin 8)) :
    conjugate (cartesianChange P)=cartesianChange (realConjugatePolynomial P) := by
  change MvPolynomial.map (starRingEnd ℂ) (rename _ _)=_
  rw [MvPolynomial.map_rename]
  change rename _ (conjugate (linearChange (splitChange 8) P))=_
  rw [conjugate_split]
  rfl


-- @@ L1030-1035 verbatim
lemma ordinaryLaplacian_cartesianChange (P : SplitPolynomial (Fin 8)) :
    ordinaryLaplacian (cartesianChange P)= (4:ℂ) • cartesianChange (mixedLaplacian P) := by
  have he := ordinaryLaplacian_rename (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16)
    (linearChange (splitChange 8) P)
  rw [ordinaryLaplacian_split,map_smul] at he
  exact he


-- @@ L1037-1037 verbatim
end HarmonicCounterexample.Control


-- @@ L1039-1039 verbatim
end


-- @@ L1041-1041 verbatim
noncomputable section



-- @@ L1044-1044 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1045-1045 verbatim
open MvPolynomial ComplexAngular


-- @@ L1047-1050 verbatim
lemma conjugate_ofReal {ι : Type*} (P : MvPolynomial ι ℝ) :
    conjugate (MvPolynomial.map Complex.ofRealHom P)=MvPolynomial.map Complex.ofRealHom P := by
  ext d
  simp [coeff_conjugate,coeff_map]


-- @@ L1052-1056 verbatim
lemma cartesianChange_fixed {l : ℕ} (P : realHarmonicSpace l) :
    conjugate (cartesianChange P.val.val)=cartesianChange P.val.val := by
  rw [conjugate_cartesianChange]
  have hp : realConjugatePolynomial P.val.val=P.val.val := congrArg Subtype.val P.property
  rw [hp]


-- @@ L1058-1060 verbatim
lemma cartesianChange_harmonic {l : ℕ} (P : realHarmonicSpace l) :
    ordinaryLaplacian (cartesianChange P.val.val)=0 := by
  rw [ordinaryLaplacian_cartesianChange,P.val.property.2,map_zero,smul_zero]


-- @@ L1062-1066 verbatim
lemma realCartesian_mem {l : ℕ} (P : realHarmonicSpace l) :
    realCoefficients (cartesianChange P.val.val) ∈ Angular.harmonicPolynomials 16 l := by
  refine ⟨realCoefficients_homogeneous (cartesianChange_homogeneous P.val.property.1),?_⟩
  change ordinaryLaplacian _=0
  rw [ordinaryLaplacian_realCoefficients,cartesianChange_harmonic,map_zero]


-- @@ L1068-1080 verbatim
lemma inverseCartesian_mem {l : ℕ} (P : Angular.harmonicPolynomials 16 l) :
    inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val) ∈ harmonicSpace (Fin 8) l := by
  refine ⟨inverseCartesianChange_homogeneous (P.property.1.map _),?_⟩
  change mixedLaplacian _=0
  have hP : ordinaryLaplacian P.val=0 := P.property.2
  have he := ordinaryLaplacian_cartesianChange
    (inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val))
  rw [cartesianChange_inverse,ordinaryLaplacian_map,hP,map_zero] at he
  have hz : cartesianChange (mixedLaplacian
      (inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val)))=0 :=
    (smul_eq_zero.mp he.symm).resolve_left (by norm_num)
  apply cartesianChange_injective
  simpa only [map_zero] using hz


-- @@ L1082-1086 verbatim
lemma inverseCartesian_fixed {l : ℕ} (P : Angular.harmonicPolynomials 16 l) :
    realConjugatePolynomial (inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val))=
      inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val) := by
  apply cartesianChange_injective
  rw [← conjugate_cartesianChange,cartesianChange_inverse,conjugate_ofReal]


-- @@ L1088-1113 verbatim
/-- Literal real polynomial equivalence: the split-coordinate real form is
 exactly the Cartesian harmonic space, not merely an abstract dimension copy. -/
def realCartesianHarmonic (l : ℕ) : realHarmonicSpace l ≃ₗ[ℝ] Angular.harmonicPolynomials 16 l where
  toFun P := ⟨realCoefficients (cartesianChange P.val.val),realCartesian_mem P⟩
  invFun P := ⟨⟨inverseCartesianChange (MvPolynomial.map Complex.ofRealHom P.val),inverseCartesian_mem P⟩,
    show IsSelfAdjoint _ from Subtype.ext (inverseCartesian_fixed P)⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change inverseCartesianChange (MvPolynomial.map Complex.ofRealHom
      (realCoefficients (cartesianChange P.val.val)))=P.val.val
    rw [ofReal_realCoefficients (cartesianChange_fixed P),inverse_cartesianChange]
  right_inv P := by
    apply Subtype.ext
    change realCoefficients (cartesianChange (inverseCartesianChange
      (MvPolynomial.map Complex.ofRealHom P.val)))=P.val
    rw [cartesianChange_inverse,realCoefficients_ofReal]
  map_add' P Q := by
    apply Subtype.ext
    change realCoefficients (cartesianChange (P.val.val+Q.val.val))=_
    rw [map_add,map_add]
    rfl
  map_smul' c P := by
    apply Subtype.ext
    change realCoefficients (cartesianChange (c • P.val.val))=c • _
    rw [AlgHom.map_smul_of_tower,map_smul]


-- @@ L1115-1116 verbatim
lemma realCartesianHarmonic_apply (l : ℕ) (P : realHarmonicSpace l) :
    (realCartesianHarmonic l P).val=realCoefficients (cartesianChange P.val.val) := rfl


-- @@ L1118-1120 verbatim
lemma ofReal_realCartesianHarmonic (l : ℕ) (P : realHarmonicSpace l) :
    MvPolynomial.map Complex.ofRealHom (realCartesianHarmonic l P).val=cartesianChange P.val.val :=
  ofReal_realCoefficients (cartesianChange_fixed P)

-- @@ L1121-1121 verbatim
end HarmonicCounterexample.Control


-- @@ L1123-1123 verbatim
end


-- @@ L1125-1125 verbatim
noncomputable section



-- @@ L1128-1128 verbatim
namespace HarmonicCounterexample.Control

-- @@ L1129-1129 verbatim
open MvPolynomial ComplexAngular Berger Berger.ComplexStructure ComplexStarModule

-- @@ L1130-1130 verbatim
open scoped BigOperators


-- @@ L1132-1136 verbatim
lemma linearField_map {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix ι ι R) (P : MvPolynomial ι R) :
    MvPolynomial.map f (linearField M P)=linearField (M.map f) (MvPolynomial.map f P) := by
  simp only [linearField_apply,map_sum,smul_eq_C_mul,map_mul,map_C,map_X,pderiv_map]
  rfl


-- @@ L1138-1149 verbatim
lemma linearField_rename {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι ℂ) (P : MvPolynomial ι ℂ) :
    rename e (linearField M P)=linearField (M.submatrix e.symm e.symm) (rename e P) := by
  simp only [linearField_apply,map_sum,map_smul,map_mul,rename_X]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rw [pderiv_rename e.injective]


-- @@ L1151-1158 verbatim
lemma linearChange_splitField (J : ComplexStructure (Fin 8 ⊕ Fin 8))
    (P : MvPolynomial (Fin 8 ⊕ Fin 8) ℂ) :
    linearChange (splitChange 8) (linearField (splitFieldMatrix J.matrix) P)=
      linearField (J.matrix.map Complex.ofRealHom) (linearChange (splitChange 8) P) := by
  apply linearChange_linearField
  change (splitChange 8*J.matrix.map Complex.ofReal*unsplitChange 8)*splitChange 8 = _
  rw [Matrix.mul_assoc _ (unsplitChange 8),unsplit_split,Matrix.mul_one]
  rfl


-- @@ L1160-1166 verbatim
lemma cartesianChange_field (J : ComplexStructure (Fin 8 ⊕ Fin 8))
    (P : MvPolynomial (Fin 8 ⊕ Fin 8) ℂ) :
    cartesianChange (linearField (splitFieldMatrix J.matrix) P)=
      linearField ((J.reindex finSumFinEquiv.symm).matrix.map Complex.ofRealHom)
        (cartesianChange P) := by
  simp only [cartesianChange,AlgHom.comp_apply,linearChange_splitField,linearField_rename]
  rfl


-- @@ L1168-1170 verbatim
lemma rotation_eq_field {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (P : MvPolynomial (Fin n) ℝ) :
    Angular.polynomialRotation M P=linearField M P := by
  rw [Angular.polynomialRotation_apply,linearField_apply]


-- @@ L1172-1176 verbatim
lemma harmonicField_star (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8)) :
    ∀ x,harmonicField l J (star x)=
      star (harmonicField l J x) := by
  intro x
  exact (spaceRealConjugation_harmonicField l J x).symm


-- @@ L1178-1185 verbatim
lemma restrictReal_harmonicField_val (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8))
    (P : realHarmonicSpace l) :
    (RealForm.restrictReal (harmonicField l J) P).val=
      harmonicField l J P.val := by
  have hs : IsSelfAdjoint (harmonicField l J P.val) := by
    change star _ = _
    rw [← harmonicField_star,P.property]
  exact hs.coe_realPart


-- @@ L1187-1198 verbatim
lemma realCartesian_rotation (l : ℕ) (J : ComplexStructure (Fin 8 ⊕ Fin 8))
    (P : realHarmonicSpace l) :
    realCartesianHarmonic l (RealForm.restrictReal (harmonicField l J) P)=
      Angular.rotation (J.reindex finSumFinEquiv.symm) l (realCartesianHarmonic l P) := by
  apply Subtype.ext
  apply (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective)
  rw [ofReal_realCartesianHarmonic]
  change cartesianChange _=MvPolynomial.map Complex.ofRealHom
    (Angular.polynomialRotation (J.reindex finSumFinEquiv.symm).matrix (realCartesianHarmonic l P).val)
  rw [restrictReal_harmonicField_val,rotation_eq_field,linearField_map,
    ofReal_realCartesianHarmonic]
  exact cartesianChange_field J P.val.val

-- @@ L1199-1199 verbatim
end HarmonicCounterexample.Control


-- @@ L1201-1201 verbatim
end


-- @@ L1203-1203 verbatim
end OAI
