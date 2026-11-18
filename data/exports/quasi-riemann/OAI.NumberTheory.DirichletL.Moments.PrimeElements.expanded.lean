import OAI.NumberTheory.DirichletL.Moments.PrimePool


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentPrimeElements

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentPrimePool CenteredMomentAmplificationGlobal

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-13 verbatim
def elementPool (P : Finset (Ideal O)) : Finset O := P.image primaryPrime


-- @@ L15-41 verbatim
theorem primaryPrime_data (P : Ideal O) (hp : Prime P) (hbad : P ∉ fixedBadPrimes) :
    Prime (primaryPrime P) ∧ Ideal.span {primaryPrime P} = P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ primaryPrime P - 1 ∧
    Supported (Ideal.span {primaryPrime P}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {primaryPrime P} ∧
    ringChar (O ⧸ Ideal.span {primaryPrime P}) ≠ 2 := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := (prime_good_iff_not_bad P).mpr hbad
  have hn := primaryPrime_ne_zero P hg.1
  have hs := (primaryPrime_spec P hn).2.2
  have hsupport : Supported P := by
    refine ⟨hp.ne_zero,?_⟩
    intro Q hQ
    have he : Q = P := by
      simpa only [UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
        normalize_eq,Multiset.mem_singleton] using hQ
    subst Q
    exact hg
  refine ⟨?_,hs.1,hs.2,?_,?_,?_⟩
  · apply (Ideal.span_singleton_prime hn).mp
    rw [hs.1]
    infer_instance
  · rwa [hs.1]
  · rw [hs.1]
    exact hg.1
  · rw [hs.1]
    exact hg.2


-- @@ L43-49 verbatim
theorem elementPool_card (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes) :
    (elementPool P).card = P.card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  rw [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1,
    ← (primaryPrime_data R (hp R hR) (hbad R hR)).2.1,he]


-- @@ L51-61 verbatim
theorem elementPool_data (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (p : O) (hpm : p ∈ elementPool P) :
    Prime p ∧ Ideal.span {p} ∈ P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ p-1 ∧
    Supported (Ideal.span {p}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p} ∧
    ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hpm
  obtain ⟨hpr,hspan,hprim,hs,hg,hc⟩ := primaryPrime_data Q (hp Q hQ) (hbad Q hQ)
  exact ⟨hpr,hspan.symm ▸ hQ,hprim,hs,hg,hc⟩


-- @@ L63-72 verbatim
theorem eligible_not_dvd (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (h : O) (hh : Ideal.span {h} ∣ R)
    (p : O) (hpm : p ∈ elementPool (eligiblePool P R)) : ¬p ∣ h := by
  have hd := elementPool_data (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1) p hpm
  intro hph
  apply (Finset.mem_filter.mp hd.2.1).2
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph)).trans hh


-- @@ L74-80 verbatim
theorem primePool_data (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : fixedBadPrimes ⊆ S) (a b x : ℝ)
    (Q : Ideal O) (hQ : Q ∈ primePool M H S a b x) :
    Prime Q ∧ Q ∉ fixedBadPrimes := by
  obtain ⟨hQ,hQS⟩ := Finset.mem_sdiff.mp hQ
  exact ⟨((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp hQ).2.1,
    fun hbad => hQS (hS hbad)⟩


-- @@ L82-95 verbatim
theorem elementPool_eligible (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) :
    (elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R) =
      elementPool (eligiblePool P R) := by
  ext p
  simp only [elementPool,eligiblePool,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨Q,hQ,rfl⟩,hnot⟩
    refine ⟨Q,⟨hQ,?_⟩,rfl⟩
    rwa [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]
  · rintro ⟨Q,⟨hQ,hnot⟩,rfl⟩
    refine ⟨⟨Q,hQ,rfl⟩,?_⟩
    rwa [(primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]


-- @@ L97-106 verbatim
theorem eligible_element_card_half (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (hR : R ≠ 0) (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P, Z^ell ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ell) ≤ P.card) :
    (P.card : ℝ)/2 ≤ ((elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R)).card := by
  rw [elementPool_eligible P hp hbad R,elementPool_card (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1)]
  exact eligiblePool_half P hp R hR Z ell B hZ hell hlower hupper hsize


-- @@ L108-127 verbatim
theorem ideal_pool_polynomial_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (h : O) (hh : ∀ Q ∈ P, ¬Q ∣ Ideal.span {h}) :
    ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2 ≤ (4/(P.card : ℝ))*
      ∑ p ∈ elementPool P,
        (‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  have he := polynomial_pool_bound S a ha c (elementPool P) (Finset.Nonempty.image hne _)
    (fun p hpm => (elementPool_data P hp hbad p hpm).1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.2) h (by
      intro p hpm hph
      apply hh (Ideal.span {p}) (elementPool_data P hp hbad p hpm).2.1
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph))
  simpa only [elementPool_card P hp hbad] using he


-- @@ L129-129 verbatim
end SevenEighths.CenteredMomentPrimeElements


-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
end OAI
