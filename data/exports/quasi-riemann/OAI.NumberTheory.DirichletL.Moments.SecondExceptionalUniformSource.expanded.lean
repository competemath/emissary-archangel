import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQSource
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFixedQChosenBlock
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalUniform
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport


-- @@ L19-19 verbatim
namespace OAI


-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L23-23 verbatim
open Filter MeasureTheory


-- @@ L25-25 verbatim
namespace SevenEighths.CenteredMomentSecondExceptionalUniformSource

-- @@ L26-26 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid

-- @@ L27-27 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource

-- @@ L28-28 verbatim
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns

-- @@ L29-29 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L30-30 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow

-- @@ L31-31 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair

-- @@ L32-32 verbatim
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth

-- @@ L33-33 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost

-- @@ L34-34 verbatim
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily

-- @@ L35-35 verbatim
open CenteredMomentSecondExceptionalPairBound

-- @@ L36-36 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon

-- @@ L37-37 verbatim
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical

-- @@ L38-38 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency

-- @@ L39-39 verbatim
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows

-- @@ L40-40 verbatim
open CenteredMomentSecondPhysicalBlock

-- @@ L41-41 verbatim
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization

-- @@ L42-42 verbatim
open CenteredMomentSecondDyadicRowSupport


-- @@ L44-44 verbatim
open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical

-- @@ L45-45 verbatim
open CenteredMomentSecondExceptionalCommonSaving

-- @@ L46-46 verbatim
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation

-- @@ L47-47 verbatim
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport

-- @@ L48-48 verbatim
local notation "O" => HeckeFamily.O

-- @@ L49-49 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

-- @@ L50-50 verbatim
universe u

-- @@ L51-51 verbatim
variable {ι:Type u}[Fintype ι][DecidableEq ι]


-- @@ L53-53 verbatim
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily

-- @@ L54-54 verbatim
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock

-- @@ L55-55 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport

-- @@ L56-56 verbatim
open CenteredMomentFiniteProfileExceptionalPhysical


-- @@ L58-58 verbatim
open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate

-- @@ L59-59 verbatim
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary

-- @@ L60-60 verbatim
open CenteredMomentSecondRetainedAggregate

-- @@ L61-61 verbatim
open CenteredMomentActiveSource


-- @@ L63-97 verbatim
theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ) :=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hsource⟩:=
    CenteredMomentSecondExceptionalFixedQSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ (5*B+1) B 1 hε hδ hθ (by positivity) hB zero_lt_one
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hsource⟩:=hsource Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hsource,CenteredMomentSecondExceptionalSourceCaps.eventually_source_caps] with Z hZ hcaps
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRN r hX1 hX2 hY1 hY2
  obtain ⟨hHlarge,hcond⟩:=hcaps.2 s.η R0 (sourceRadius s) R B hB hH0 hR.le hη hR0N hH hRN
  exact hZ.2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hHlarge χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys hR (by simpa using hRN) hcond r hX1 hX2 hY1 hY2


-- @@ L99-99 verbatim
end SevenEighths.CenteredMomentSecondExceptionalUniformSource


-- @@ L101-101 verbatim
end


-- @@ L103-103 verbatim
end OAI
