import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
import OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
import OAI.NumberTheory.DirichletL.Moments.LogDyadic
import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L11-11 verbatim
open MeasureTheory


-- @@ L13-13 verbatim
namespace SevenEighths.CenteredMomentSecondWindowSource

-- @@ L14-14 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L15-15 verbatim
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled

-- @@ L16-16 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily

-- @@ L17-17 verbatim
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource

-- @@ L18-18 verbatim
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion

-- @@ L19-19 verbatim
open CenteredMomentLogDyadic CenteredMomentConjugateWindow

-- @@ L20-20 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L22-50 verbatim
theorem sector_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  have he (v : ℝ) := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L v)
  simp_rw [sector_divisor_coefficient η τ χ A hτ S β C hC L t]
  have hh := restricted_window_energy_from_height keep V hVc hVs J Finset.univ
    (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I : sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←sector_child_energy η τ χ A hτ S β C hC L v keep Φ H,he v] at hs
  simpa only [sectorElement_span] using hs


-- @@ L52-53 verbatim
theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]


-- @@ L55-58 verbatim
theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]


-- @@ L60-80 verbatim
theorem sector_conjugate_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) Φ H≤
      (E*heightCost t (-θ)^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  simp only [star_logAnnulus_column]
  exact sector_window_from_source η τ χ A hτ S β C hC L keep t (-θ) X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE hsource


-- @@ L82-82 verbatim
end SevenEighths.CenteredMomentSecondWindowSource


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
