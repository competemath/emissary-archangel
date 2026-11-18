import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair


-- @@ L13-13 verbatim
namespace OAI


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff


-- @@ L18-18 verbatim
namespace SevenEighths.CenteredMomentSecondNonexceptionalCost

-- @@ L19-19 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT

-- @@ L20-20 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst

-- @@ L21-21 verbatim
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar

-- @@ L22-22 verbatim
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport

-- @@ L23-23 verbatim
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled

-- @@ L24-24 verbatim
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm

-- @@ L25-25 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion

-- @@ L26-26 verbatim
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget

-- @@ L27-27 verbatim
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource

-- @@ L28-28 verbatim
open CenteredMomentSecondIdealBlockBound

-- @@ L29-29 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L31-31 verbatim
open Filter

-- @@ L32-32 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise

-- @@ L33-33 verbatim
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L34-34 verbatim
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy

-- @@ L35-35 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

-- @@ L36-36 verbatim
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _


-- @@ L38-38 verbatim
open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren

-- @@ L39-39 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar

-- @@ L40-40 verbatim
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel

-- @@ L41-41 verbatim
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair


-- @@ L43-43 verbatim
open CenteredMomentSecondHeightFamily

-- @@ L44-44 verbatim
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit

-- @@ L45-45 verbatim
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice

-- @@ L46-46 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair


-- @@ L48-48 verbatim
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar

-- @@ L49-49 verbatim
open CenteredMomentSecondRadicalBudget


-- @@ L51-144 verbatim
theorem actual_canonical_child_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  have hτ:∀χ:RayCharacter,((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤E:=
    family_child_envelope hf s.t S β R rows W Kphys hKphys n hzero
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    apply (hleft L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₁)
      (show 0≤(1+‖v‖)^(2*J₁) by positivity)
    simpa only [mul_assoc] using hh
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    apply (hright L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₂)
      (show 0≤(1+‖v‖)^(2*J₂) by positivity)
    simpa only [mul_assoc] using hh
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E] <;> ring


-- @@ L146-146 verbatim
end SevenEighths.CenteredMomentSecondNonexceptionalCost


-- @@ L148-148 verbatim
end


-- @@ L150-150 verbatim
end OAI
