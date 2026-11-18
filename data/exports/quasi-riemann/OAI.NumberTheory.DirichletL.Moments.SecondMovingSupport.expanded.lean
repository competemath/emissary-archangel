import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondMovingSupport

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L11-11 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm

-- @@ L12-12 verbatim
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-34 verbatim
theorem actual_unequal_min_six (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl


-- @@ L36-37 verbatim
def fixedExponent (C D : Ideal O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0


-- @@ L39-40 verbatim
def fixedActiveSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)


-- @@ L42-59 verbatim
theorem fixedActiveSet_subset (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := fun h=>hn (Finset.mem_union_left _ h)
  have hV : P∉nonunitPartitionSet C D U := fun h=>hn (Finset.mem_union_right _ h)
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hU⟩)
  rw [fixedExponent,ite_eq_right hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · rw [hc,min_self] at ha
    exact heq ⟨hc,by simpa only [hc] using ha⟩
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)


-- @@ L61-85 verbatim
theorem fixed_active_log_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (Ideal.absNorm (∏P∈fixedActiveSet C D U,P.val):ℝ)≤
      Real.logb Z (Ideal.absNorm (∏P∈U,P.val):ℝ)+
        Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ) := by
  have hn (P : CommonIndex C D) : 0≤Real.logb Z (Ideal.absNorm P.val:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)))
  have hlog (T : Finset (CommonIndex C D)) :
      Real.logb Z (Ideal.absNorm (∏P∈T,P.val):ℝ)=∑P∈T,Real.logb Z (Ideal.absNorm P.val:ℝ) := by
    simp only [map_prod,Nat.cast_prod]
    exact Real.logb_prod _ _ (fun P _=>Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))
  rw [CenteredMomentSecondCanonicalLedger.nonunitFrequencyGenerator_span,unitIdeal]
  simp only [commonPrime_span C D hC]
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hU hV
    exact (Finset.mem_sdiff.mp hV).2 hU
  rw [hlog,hlog,hlog,←Finset.sum_union hdis]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fixedActiveSet_subset C D hC hD hCD U w hne)
    (fun P _ _=>hn P)


-- @@ L87-87 verbatim
end SevenEighths.CenteredMomentSecondMovingSupport


-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
end OAI
