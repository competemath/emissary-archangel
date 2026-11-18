import OAI.NumberTheory.DirichletL.Detector.IdealMultiplicative
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L9-9 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O


-- @@ L13-13 verbatim
abbrev PrimeIdeal := {P : Id // Prime P}


-- @@ L15-16 verbatim
def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime


-- @@ L18-19 verbatim
def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=>P.val^n)


-- @@ L21-23 verbatim
lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>pow_ne_zero _ P.property.ne_zero)


-- @@ L25-27 verbatim
@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]


-- @@ L29-30 verbatim
@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]


-- @@ L32-34 verbatim
lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]


-- @@ L36-45 verbatim
@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=>h (Subtype.ext hh)
    simp [Ne.symm h,hv]


-- @@ L47-51 verbatim
lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I^n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]


-- @@ L53-54 verbatim
@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]


-- @@ L56-58 verbatim
lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)


-- @@ L60-62 verbatim
@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]


-- @@ L64-72 verbatim
@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]


-- @@ L74-83 verbatim
@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI


-- @@ L85-89 verbatim
def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations


-- @@ L91-96 verbatim
lemma primeIdeal_coprime (P Q : PrimeIdeal) (h : P≠Q) : IsCoprime P.val Q.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : Q.val.IsPrime := Ideal.isPrime_of_prime Q.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  let : Q.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance Q.property.ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun hh=>h (Subtype.ext hh))


-- @@ L98-106 verbatim
lemma prime_coprime_idealFromValuations (P : PrimeIdeal) (v : PrimeIdeal →₀ ℕ)
    (hP : v P=0) : IsCoprime P.val (idealFromValuations v) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply IsCoprime.pow_right
  apply primeIdeal_coprime
  intro hh
  subst Q
  exact Finsupp.mem_support_iff.mp hQ hP


-- @@ L108-117 verbatim
def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)


-- @@ L119-119 verbatim
abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)

-- @@ L120-120 verbatim
abbrev NonzeroIdeal := {I : Id // I≠0}


-- @@ L122-127 verbatim
def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)


-- @@ L129-133 verbatim
@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl


-- @@ L135-135 verbatim
end SevenEighths.ProbePhysical

-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
end OAI
