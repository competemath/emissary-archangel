import OAI.NumberTheory.DirichletL.Moments.CommonSectorColumn
import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
import OAI.NumberTheory.DirichletL.Moments.ReflectedSource
import OAI.NumberTheory.DirichletL.Moments.SecondWindowSource


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open scoped Classical BigOperators


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentCommonSectorWindow

-- @@ L12-12 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L13-13 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource

-- @@ L14-14 verbatim
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns

-- @@ L15-15 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L16-16 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow

-- @@ L17-17 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair

-- @@ L18-18 verbatim
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth CenteredMomentSecondWindowSource

-- @@ L19-19 verbatim
open RayFourExpansion CenteredMomentLogDyadic

-- @@ L20-20 verbatim
local notation "O" => HeckeFamily.O

-- @@ L21-21 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

-- @@ L22-22 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L24-49 verbatim
omit [DecidableEq ι] in
theorem actual_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(V:ℝ→ℂ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z=
      windowColumn s C hC R seed L τ t θ X V z:=by
  dsimp only
  simp_rw [masked_divisor_coefficient η τ χ A C hC hτ]
  rw [sector_rowPolynomial _ (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)*
      heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) C hC z]
  unfold windowColumn
  rw [←rowPolynomial_factor]
  apply congrArg (fun c=>rowPolynomial Finset.univ (sourceGenerator (columns s C hC)) c z)
  funext I
  dsimp only [coefficient]
  split_ifs <;> simp_all ; ring


-- @@ L51-62 verbatim
omit [DecidableEq ι] in
theorem window_neg (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):
    windowColumn s C hC R seed L η t θ X V (-z)=
      windowColumn s C hC R seed L (reflected η) t θ X V z:=by
  unfold windowColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [reflected_height η t I (Finset.mem_filter.mp I.property).2,
    show -z=(-1)*z by ring,idealRowHom_argument_mul,sourceGenerator_span]
  ring


-- @@ L64-81 verbatim
omit [DecidableEq ι] in
theorem actual_reflected_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) (-z)=
      windowColumn s C hC R seed L (reflected τ) t (-θ) X logAnnulus z:=by
  dsimp only
  simp only [star_logAnnulus_column]
  rw [actual_sector_window s η τ χ A C hC R seed L t (-θ) X logAnnulus (-z) hτ,window_neg]


-- @@ L83-83 verbatim
end SevenEighths.CenteredMomentCommonSectorWindow


-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
end OAI
