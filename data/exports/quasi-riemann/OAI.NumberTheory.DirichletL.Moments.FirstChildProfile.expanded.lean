import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstChildProfile

-- @@ L9-9 verbatim
open HeckeFamily CenteredMomentFirstIdealFamily CenteredMomentHeckeColumnWindow

-- @@ L10-10 verbatim
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentHeckeExpansion

-- @@ L11-11 verbatim
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentSourceRow

-- @@ L12-12 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-24 verbatim
theorem divisor_column_of_family (η τ : Character) (m : O) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*(F (CompletedGauss.primaryGenerator I)*
        rayCharacter ξ (CompletedGauss.primaryGenerator I)))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (fun J => β J*rowWeight η m 1 1 t J*F (CompletedGauss.primaryGenerator J)) ξ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring


-- @@ L26-48 verbatim
theorem exists_first_divisor_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*leftCoefficient e r ρ (CompletedGauss.primaryGenerator J)) ξ₁ I=
          (if L∣I then β I else 0)*heightCoeff τ₁ t I) ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*rightCoefficient e r ρ (CompletedGauss.primaryGenerator J)) ξ₂ I=
          (if L∣I then β I else 0)*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro L I hI β t
    exact divisor_column_of_family η τ₁ m _ ξ₁ h₁ L I hI β t
  · intro L I hI β t
    exact divisor_column_of_family η τ₂ m _ ξ₂ h₂ L I hI β t


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentFirstChildProfile


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
