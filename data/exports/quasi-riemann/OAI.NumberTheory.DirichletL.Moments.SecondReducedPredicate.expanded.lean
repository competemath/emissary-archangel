import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondReducedPredicate

-- @@ L11-11 verbatim
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L12-12 verbatim
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy

-- @@ L13-13 verbatim
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows

-- @@ L14-14 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L15-15 verbatim
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion

-- @@ L16-16 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L18-26 verbatim
theorem fixed_mask_change (η : Character) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2


-- @@ L28-41 verbatim
theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm


-- @@ L43-54 verbatim
theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]


-- @@ L56-56 verbatim
end SevenEighths.CenteredMomentSecondReducedPredicate


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
