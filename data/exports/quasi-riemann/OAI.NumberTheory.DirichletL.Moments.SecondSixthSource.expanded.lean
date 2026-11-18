import OAI.NumberTheory.DirichletL.Moments.SecondSixthReduction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondSixthSource

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L11-11 verbatim
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction

-- @@ L12-12 verbatim
open CenteredMomentCanonicalFirst

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-26 verbatim
theorem sixthFactor_span_dvd (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  split_ifs <;> omega


-- @@ L28-33 verbatim
theorem fixed_sixth_coefficient (C D : Ideal O) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]


-- @@ L35-41 verbatim
theorem residual_sixth_coefficient (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]


-- @@ L43-43 verbatim
abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)


-- @@ L45-46 verbatim
def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val


-- @@ L48-49 verbatim
def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6


-- @@ L51-54 verbatim
theorem activeExponent_pos (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : 0<activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=>hp (Nat.dvd_of_mod_eq_zero h))


-- @@ L56-57 verbatim
theorem activeExponent_lt (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : activeExponent C D U P<6 := Nat.mod_lt _ (by norm_num)


-- @@ L59-70 verbatim
theorem reducedNumerator_active_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]


-- @@ L72-72 verbatim
end SevenEighths.CenteredMomentSecondSixthSource


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
