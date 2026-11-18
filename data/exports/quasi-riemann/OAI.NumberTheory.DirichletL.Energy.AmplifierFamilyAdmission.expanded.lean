import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
import OAI.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
import OAI.NumberTheory.DirichletL.Moments.FirstMixedMainError
import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L12-12 verbatim
open Filter


-- @@ L14-14 verbatim
namespace SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

-- @@ L15-15 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic

-- @@ L16-16 verbatim
open CenteredMomentFirstSourceConductorCaps CenteredMomentAmplificationRadicalFamily

-- @@ L17-17 verbatim
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice

-- @@ L18-18 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows

-- @@ L19-19 verbatim
open CenteredMomentSectorLocalization CenteredMomentFirstAmplifiedFourCoefficients

-- @@ L20-20 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L21-21 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L23-23 verbatim
def referenceCost : ℝ := max 1 rayCost


-- @@ L25-25 verbatim
lemma referenceCost_ge_one : 1≤referenceCost := le_max_left _ _


-- @@ L27-49 verbatim
theorem actual_error_reference_cap (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent n)):
    (υ.modulus.absNorm:ℝ)≤referenceCost*(ρ.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (n+1)):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
  calc
    _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        Z^(errorMoving p Z (n+1)):=by apply hN.trans;gcongr
    _=rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
      unfold rayCost fixedPresentationCost;ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      exact mul_le_mul_of_nonneg_right (le_max_right 1 rayCost) (Nat.cast_nonneg _)


-- @@ L51-51 verbatim
end SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
