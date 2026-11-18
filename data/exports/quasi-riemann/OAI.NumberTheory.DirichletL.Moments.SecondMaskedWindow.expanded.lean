import OAI.NumberTheory.DirichletL.Moments.SecondReducedEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L7-7 verbatim
open MeasureTheory


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondMaskedWindow

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled

-- @@ L12-12 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily

-- @@ L13-13 verbatim
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource

-- @@ L14-14 verbatim
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion

-- @@ L15-15 verbatim
open CenteredMomentLogDyadic CenteredMomentRowNorm CenteredMomentSourceRow

-- @@ L16-16 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L18-32 verbatim
theorem masked_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  have hi : IsCoprime C (I:Ideal O) := (Finset.mem_filter.mp I.property).2
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,
    hτ I (sectorPool_supported C hC.1 S I) hi t]
  dsimp only [sectorElement]
  split_ifs <;> ring


-- @@ L34-58 verbatim
theorem masked_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H := by
  have he := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  rw [he]
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_rowPolynomial S (fun I=>(if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  have hc : (fun I : supportedColumns (residualPool C hC.1 S)=>
      if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I : supportedColumns (residualPool C hC.1 S)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) := by
    funext I
    split_ifs <;> simp_all
  rw [hc]


-- @@ L60-92 verbatim
theorem original_window_from_masked_source (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀v:ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hc := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  change restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
    (fun I=>(divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ) I*_) Φ H≤_
  rw [hc]
  have hh := restricted_window_energy_from_height keep logAnnulus logAnnulus_compact logAnnulus_smooth J
    Finset.univ (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I:sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←masked_child_energy η τ χ A C hC hτ S β L v keep Φ H] at hs
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ S β L v)] at hs
  simpa only [sectorElement_span] using hs


-- @@ L94-94 verbatim
end SevenEighths.CenteredMomentSecondMaskedWindow


-- @@ L96-96 verbatim
end


-- @@ L98-98 verbatim
end OAI
