import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport


-- @@ L10-10 verbatim
namespace OAI


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L14-14 verbatim
open Filter MeasureTheory


-- @@ L16-16 verbatim
namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

-- @@ L17-17 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid

-- @@ L18-18 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource

-- @@ L19-19 verbatim
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns

-- @@ L20-20 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L21-21 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow

-- @@ L22-22 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair

-- @@ L23-23 verbatim
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth

-- @@ L24-24 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost

-- @@ L25-25 verbatim
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily

-- @@ L26-26 verbatim
open CenteredMomentSecondExceptionalPairBound

-- @@ L27-27 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon

-- @@ L28-28 verbatim
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical

-- @@ L29-29 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency

-- @@ L30-30 verbatim
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows

-- @@ L31-31 verbatim
open CenteredMomentSecondPhysicalBlock

-- @@ L32-32 verbatim
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization

-- @@ L33-33 verbatim
open CenteredMomentSecondDyadicRowSupport


-- @@ L35-35 verbatim
open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical

-- @@ L36-36 verbatim
open CenteredMomentSecondExceptionalCommonSaving

-- @@ L37-37 verbatim
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation

-- @@ L38-38 verbatim
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport

-- @@ L39-39 verbatim
local notation "O" => HeckeFamily.O

-- @@ L40-40 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

-- @@ L41-41 verbatim
universe u

-- @@ L42-42 verbatim
variable {ι:Type u}[Fintype ι][DecidableEq ι]


-- @@ L44-109 verbatim
theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring


-- @@ L111-111 verbatim
end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical


-- @@ L113-113 verbatim
end


-- @@ L115-115 verbatim
end OAI
