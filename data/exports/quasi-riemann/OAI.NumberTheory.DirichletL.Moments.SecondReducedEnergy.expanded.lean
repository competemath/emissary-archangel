import OAI.NumberTheory.DirichletL.Moments.SecondSixthSource
import OAI.NumberTheory.DirichletL.Moments.SecondWindowSource


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L8-8 verbatim
open MeasureTheory


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentSecondReducedEnergy

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L12-12 verbatim
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled

-- @@ L13-13 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily

-- @@ L14-14 verbatim
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentChildAssembly

-- @@ L15-15 verbatim
open CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion CenteredMomentLogDyadic

-- @@ L16-16 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L17-17 verbatim
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondWindowSource

-- @@ L18-18 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L20-43 verbatim
theorem masked_source_energy (η τ τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O)
    (keep : O→Prop) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τr t) Φ H := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs with hi
  · have hI : Supported (I:Ideal O) := (Finset.mem_filter.mp I.property).2
    rw [hτ I hI t,hτr I hI t,residual_sixth_coefficient C D hC hCD U I hI hi.1]
  · simp only [zero_mul]


-- @@ L45-75 verbatim
theorem original_window_from_reduced_source (η τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (_hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τr v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
          (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 := by
    rw [fixed_sixth_factorization]
    exact mul_ne_zero (reducedNumerator_ne_zero C D hC U) (pow_ne_zero _ (sixthFactor_ne_zero C D hC U))
  obtain ⟨τ,hN,hτ⟩ := exists_second_family η χ _ hA
  apply sector_window_from_source η τ χ _ hτ S β C hC L keep t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE
  intro v
  rw [masked_source_energy η τ τr χ C D hC hCD U hτ hτr S β L keep v Φ H]
  exact hsource v


-- @@ L77-77 verbatim
end SevenEighths.CenteredMomentSecondReducedEnergy


-- @@ L79-79 verbatim
end


-- @@ L81-81 verbatim
end OAI
