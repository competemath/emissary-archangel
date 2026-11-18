import OAI.NumberTheory.DirichletL.Moments.SecondLedger
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondCanonical

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily

-- @@ L13-13 verbatim
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation

-- @@ L14-14 verbatim
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-17 verbatim
def commonPrime (C D : Ideal O) (P : CommonIndex C D) : O := primaryGenerator P.val


-- @@ L19-22 verbatim
theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))


-- @@ L24-26 verbatim
theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)


-- @@ L28-31 verbatim
theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P


-- @@ L33-38 verbatim
theorem commonPrime_coprime (C D : Ideal O) (hC : Supported C) :
    Pairwise (Function.onFun IsCoprime (commonPrime C D)) := by
  intro P Q hPQ
  change IsCoprime (commonPrime C D P) (commonPrime C D Q)
  rw [←Ideal.isCoprime_span_singleton_iff,commonPrime_span C D hC P,commonPrime_span C D hC Q]
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))


-- @@ L40-48 verbatim
theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change CompletedGauss.primeSupport C∩CompletedGauss.primeSupport D=
      CompletedGauss.primeSupport C∩CompletedGauss.primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC


-- @@ L50-54 verbatim
theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]


-- @@ L56-60 verbatim
theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]


-- @@ L62-68 verbatim
theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryGenerator C := by
  have he := congrArg primaryGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he


-- @@ L70-76 verbatim
theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryGenerator D := by
  have he := congrArg primaryGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he


-- @@ L78-79 verbatim
def commonFrequencyGenerator (C D : Ideal O) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P)


-- @@ L81-107 verbatim
theorem actual_ideal_secondSaving_lower (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (w : O) (Z : ℝ) (hZ : 1<Z)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    (Real.logb Z (Ideal.absNorm C:ℝ)+Real.logb Z (Ideal.absNorm D:ℝ))/3≤
      secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) w Z := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P]
    infer_instance
  have hg (P : CommonIndex C D) : goodLambda∉Ideal.span {commonPrime C D P} := by
    rw [commonPrime_span C D hC P]
    exact common_good C D hC P
  have hc (P : CommonIndex C D) : ringChar (O⧸Ideal.span {commonPrime C D P})≠2 := by
    rw [commonPrime_span C D hC P]
    exact common_odd C D hC P
  have hn : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (commonFrequencyGenerator C D*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      idealCorrelation] using hne
  have hh := actual_secondSaving_lower (commonPrime C D) (commonPrime_supported C D hC) hg hc
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) w Z hZ hn
  rw [left_ideal_product C D hC hCD,right_ideal_product C D hC hD hCD] at hh
  exact hh


-- @@ L109-109 verbatim
end SevenEighths.CenteredMomentSecondCanonical


-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end OAI
