import OAI.NumberTheory.DirichletL.Detector.HighLFactorization


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler

-- @@ L9-9 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L10-10 verbatim
local notation "Id" => Ideal O


-- @@ L12-22 verbatim
lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))


-- @@ L24-27 verbatim
structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S


-- @@ L29-42 verbatim
theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)


-- @@ L44-50 verbatim
theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz


-- @@ L52-55 verbatim
theorem source_globalCorrection_principal (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x :=
  globalClosedCorrection_principal η S (outside_prime_supported S hS.bad) x


-- @@ L57-57 verbatim
end SevenEighths.ProbePhysical

-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
