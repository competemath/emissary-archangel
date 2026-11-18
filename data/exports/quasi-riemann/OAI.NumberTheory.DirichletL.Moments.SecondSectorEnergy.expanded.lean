import OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
import OAI.NumberTheory.DirichletL.Moments.RestrictedSource


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondSectorEnergy

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy

-- @@ L12-12 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily

-- @@ L13-13 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L14-14 verbatim
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy

-- @@ L15-15 verbatim
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion

-- @@ L16-16 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L18-29 verbatim
theorem sector_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,hτ I (sectorPool_supported C hC.1 S I) t]
  dsimp only [sectorElement]
  split_ifs <;> ring


-- @@ L31-45 verbatim
theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp


-- @@ L47-63 verbatim
theorem sector_child_row (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) =>
          (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) z := by
  have he := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L t)
  rw [he,sector_rowPolynomial S (fun I => (if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  congr 1
  funext I
  split_ifs <;> simp_all


-- @@ L65-79 verbatim
theorem sector_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) W K=
      sourceRestrictedEnergy keep (residualPool C hC.1 S)
        (fun I => if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) W K := by
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_child_row η τ χ A hτ S β C hC L t z]


-- @@ L81-81 verbatim
end SevenEighths.CenteredMomentSecondSectorEnergy


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
