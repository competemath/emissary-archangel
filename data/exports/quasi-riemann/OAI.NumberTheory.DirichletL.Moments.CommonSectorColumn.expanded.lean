import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentCommonSectorColumn

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L12-12 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope

-- @@ L13-13 verbatim
open CenteredMomentCommonLinearSource CenteredMomentSecondMaskedWindow

-- @@ L14-14 verbatim
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns

-- @@ L15-15 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L16-16 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors

-- @@ L17-17 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource

-- @@ L18-18 verbatim
open RayFourExpansion ActualEisensteinCubic CenteredMomentSourceRow CompletedGauss

-- @@ L19-19 verbatim
local notation "O" => HeckeFamily.O

-- @@ L20-20 verbatim
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

-- @@ L21-21 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L23-49 verbatim
omit [DecidableEq ι] in
theorem actual_sector_column (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ) z=
      sourceColumn (withHeight s τ t) C hC R seed L z:=by
  dsimp only
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ _ _ L t)]
  apply (sector_rowPolynomial (finiteColumns (Fintype.piFinset s.pools))
    (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
      else 0)*heightCoeff τ t I) C hC z).trans
  unfold sourceColumn
  dsimp only [withHeight,Input.pools]
  apply congrArg (fun c=>rowPolynomial Finset.univ
    (sourceGenerator (residualPool C hC.1 (finiteColumns (Fintype.piFinset (Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)))))) c z)
  funext I
  change (if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I else 0)=
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then _ else 0)*heightCoeff τ t I
  split_ifs <;> simp_all


-- @@ L51-51 verbatim
end SevenEighths.CenteredMomentCommonSectorColumn


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
