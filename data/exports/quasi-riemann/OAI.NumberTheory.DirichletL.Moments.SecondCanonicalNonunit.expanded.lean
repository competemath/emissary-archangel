import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondCanonicalNonunit

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst

-- @@ L11-11 verbatim
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT

-- @@ L12-12 verbatim
open CenteredMomentSupport

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-16 verbatim
def equalActiveSet (C D : Ideal O) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P)


-- @@ L18-19 verbatim
def nonunitPartitionSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  equalActiveSet C D\U


-- @@ L21-22 verbatim
def nonunitFrequencyGenerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P∈nonunitPartitionSet C D U,commonPrime C D P


-- @@ L24-36 verbatim
theorem commonPrime_dividedFrequency_iff (C D : Ideal O) (hC : Supported C)
    (w : O) (P : CommonIndex C D) :
    commonPrime C D P∣dividedFrequency (commonPrime C D) (leftExponent C D) (rightExponent C D) w P ↔
      commonPrime C D P∣w := by
  have hc : IsCoprime (commonPrime C D P)
      (cofactor (fun Q=>commonPrime C D Q^min (leftExponent C D Q) (rightExponent C D Q)) P) := by
    unfold cofactor
    apply IsCoprime.prod_right
    intro Q hQ
    exact (commonPrime_coprime C D hC (Finset.mem_erase.mp hQ).1.symm).pow_right
  constructor
  · exact fun h=>hc.dvd_of_dvd_mul_left h
  · exact fun h=>h.trans (dvd_mul_left _ _)


-- @@ L38-46 verbatim
theorem nonunitPartitionSet_eq_actual (C D : Ideal O) (U : Finset (CommonIndex C D))
    (w : O) (hpart : canonicalPartition C D U w) :
    nonunitPartitionSet C D U=actualNonunitSet (commonPrime C D) (leftExponent C D) (rightExponent C D) w := by
  unfold canonicalPartition at hpart
  rw [nonunitPartitionSet,←hpart]
  ext P
  simp only [equalActiveSet,actualUnitSet,actualNonunitSet,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and]
  tauto


-- @@ L48-51 verbatim
theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))


-- @@ L53-61 verbatim
theorem nonunitFrequencyGenerator_dvd (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (w : O) (hpart : canonicalPartition C D U w) :
    nonunitFrequencyGenerator C D U∣w := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hPQ
    exact commonPrime_coprime C D hC hPQ
  · intro P hP
    rw [nonunitPartitionSet_eq_actual C D U w hpart] at hP
    exact (commonPrime_dividedFrequency_iff C D hC w P).mp (Finset.mem_filter.mp hP).2.2.2


-- @@ L63-80 verbatim
theorem partition_tsum_nonunit (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        idealCorrelation C D hC hD ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)*
          F (nonunitFrequencyGenerator C D U*h) else 0 := by
  let f : O→ℂ := fun w=>if canonicalPartition C D U w then
    idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)*F w else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,ite_eq_right hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm


-- @@ L82-82 verbatim
end SevenEighths.CenteredMomentSecondCanonicalNonunit


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
