import OAI.NumberTheory.DirichletL.Moments.SecondRadicalFamily


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondRadicalColumns

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L11-11 verbatim
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction

-- @@ L12-12 verbatim
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily

-- @@ L13-13 verbatim
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion

-- @@ L14-14 verbatim
open CenteredMomentCanonicalFirst

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-28 verbatim
theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega


-- @@ L30-36 verbatim
theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]


-- @@ L38-55 verbatim
theorem exists_actual_masked_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      ∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,he,hτ⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hN,?_⟩
  intro I hI hi t
  rw [hτ I hI t]
  rcases hi with hi|hi
  · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
  · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]


-- @@ L57-57 verbatim
end SevenEighths.CenteredMomentSecondRadicalColumns


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
