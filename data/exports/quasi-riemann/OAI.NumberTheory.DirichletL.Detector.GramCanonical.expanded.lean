import OAI.NumberTheory.DirichletL.Detector.GramCommonSource
import OAI.NumberTheory.DirichletL.Detector.GramSourceBlock


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L9-9 verbatim
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion

-- @@ L10-10 verbatim
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O

-- @@ L13-13 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


-- @@ L15-15 verbatim
abbrev GramFrequency := {k : O // k≠0}

-- @@ L16-16 verbatim
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈IdealMobiusDivisorSum.primeSupport C.val}

-- @@ L17-17 verbatim
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val

-- @@ L18-19 verbatim
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero


-- @@ L21-21 verbatim
def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val

-- @@ L22-23 verbatim
lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)

-- @@ L24-25 verbatim
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : λ₀∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1

-- @@ L26-28 verbatim
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)

-- @@ L29-33 verbatim
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈IdealMobiusDivisorSum.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm


-- @@ L35-37 verbatim
instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (support_prime P.property).ne_zero)

-- @@ L38-39 verbatim
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _

-- @@ L40-43 verbatim
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1

-- @@ L44-44 verbatim
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _


-- @@ L46-53 verbatim
structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : λ₀^2∣good-1
  factor : k.val=unit.val*λ₀^lambdaExponent*(2:O)^twoExponent*good


-- @@ L55-57 verbatim
lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,hr,hpr,hf⟩⟩

-- @@ L58-58 verbatim
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)


-- @@ L60-64 verbatim
def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m


-- @@ L66-72 verbatim
lemma canonicalJoint_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ‖canonicalJoint S hS σ C k n m‖≤(Ideal.absNorm C.val:ℝ) := by
  have hh := jointExtension_norm S hS σ (primaryGenerator C.val) k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramPrime C) (gramPrime_good C)
    (gramExponent C) (gramExponent_pos C) n m
  simpa only [←gramPrime_product C,canonicalJoint] using hh


-- @@ L74-74 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end OAI
