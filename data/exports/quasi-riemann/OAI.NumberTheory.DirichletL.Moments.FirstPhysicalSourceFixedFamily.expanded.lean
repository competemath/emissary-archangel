import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
import OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L11-11 verbatim
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve

-- @@ L12-12 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily

-- @@ L13-13 verbatim
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion

-- @@ L14-14 verbatim
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice

-- @@ L15-15 verbatim
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport

-- @@ L16-16 verbatim
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss

-- @@ L17-17 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L19-36 verbatim
structure FixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : Character
  right : Character
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))


-- @@ L38-42 verbatim
def fixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩⟩)


-- @@ L44-52 verbatim
theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus


-- @@ L54-54 verbatim
variable {ι:Type*}[Fintype ι]

-- @@ L55-55 verbatim
local instance firstFixedFamilyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L57-62 verbatim
theorem beta_coprime (s:OriginalData ι)(I:Ideal O)(h:s.beta I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) s.profile I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]


-- @@ L64-69 verbatim
lemma extracted_mask_redundant (s:OriginalData ι)(C:Ideal O):
    maskedSource (idealGenerator s.R) (fun I=>s.beta (C*I))=(fun I=>s.beta (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (beta_coprime s (C*I) hI).of_mul_left_right


-- @@ L71-82 verbatim
theorem fixed_divisor_column (s:OriginalData ι)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>s.beta (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh


-- @@ L84-84 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end OAI
