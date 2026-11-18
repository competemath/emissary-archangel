import OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
import OAI.NumberTheory.DirichletL.Moments.SecondBlockSupport
import OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondLiveFamily

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L12-12 verbatim
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst

-- @@ L13-13 verbatim
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L14-14 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth

-- @@ L15-15 verbatim
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns

-- @@ L16-16 verbatim
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport

-- @@ L17-17 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows

-- @@ L18-18 verbatim
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion

-- @@ L19-19 verbatim
local notation "O" => HeckeFamily.O


-- @@ L21-62 verbatim
theorem exists_live_source_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)):
    ∃τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff (τ χ) t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I)) ∧
      (∀χ:RayCharacter,∀Q:Ideal O,∀m z:O,m≠0 →
        ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
        (nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
          z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z)) ∧
      ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K → ∀n:Fin 4→ℤ,
      physicalBlock η t S β C D hC hD U R rows W K n≠0 →
      ∀χ:RayCharacter,
        (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
          (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z:ℝ,1<Z → ∀z∈liveRows C D U R rows,
        Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)):=by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,?_,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro χ Q m z hm hml hm2
    exact actual_nonexceptional_iff η (τ χ) χ C D hC U (he χ) Q m z hm hml hm2
  · intro t S β R rows W K hK n hne
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,hw,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    intro χ
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2


-- @@ L64-64 verbatim
end SevenEighths.CenteredMomentSecondLiveFamily


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end OAI
