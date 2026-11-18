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


-- @@ L17-17 verbatim
namespace OAI


-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L21-21 verbatim
open Filter MeasureTheory


-- @@ L23-23 verbatim
namespace SevenEighths.CenteredMomentSecondExceptionalFixedQSource

-- @@ L24-24 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid

-- @@ L25-25 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource

-- @@ L26-26 verbatim
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns

-- @@ L27-27 verbatim
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm

-- @@ L28-28 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow

-- @@ L29-29 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair

-- @@ L30-30 verbatim
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth

-- @@ L31-31 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost

-- @@ L32-32 verbatim
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily

-- @@ L33-33 verbatim
open CenteredMomentSecondExceptionalPairBound

-- @@ L34-34 verbatim
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon

-- @@ L35-35 verbatim
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical

-- @@ L36-36 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency

-- @@ L37-37 verbatim
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows

-- @@ L38-38 verbatim
open CenteredMomentSecondPhysicalBlock

-- @@ L39-39 verbatim
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization

-- @@ L40-40 verbatim
open CenteredMomentSecondDyadicRowSupport


-- @@ L42-42 verbatim
open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical

-- @@ L43-43 verbatim
open CenteredMomentSecondExceptionalCommonSaving

-- @@ L44-44 verbatim
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation

-- @@ L45-45 verbatim
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport

-- @@ L46-46 verbatim
local notation "O" => HeckeFamily.O

-- @@ L47-47 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

-- @@ L48-48 verbatim
universe u

-- @@ L49-49 verbatim
variable {ι:Type u}[Fintype ι][DecidableEq ι]


-- @@ L51-51 verbatim
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily

-- @@ L52-52 verbatim
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock

-- @@ L53-53 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport

-- @@ L54-54 verbatim
open CenteredMomentFiniteProfileExceptionalPhysical


-- @@ L56-56 verbatim
open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate

-- @@ L57-57 verbatim
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary

-- @@ L58-58 verbatim
open CenteredMomentSecondRetainedAggregate

-- @@ L59-59 verbatim
open CenteredMomentActiveSource


-- @@ L61-153 verbatim
theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hblock⟩:=chosen_exceptional_block wlo whi hwlo hwhi lo hi W
    ε δ θ B B hε hδ hθ hB hB
  obtain ⟨Cm,hCm,hmass⟩:=source_part_radical_bound B L Cr δ hB hL hCr hδ
  refine ⟨J,Sprofile,hSp,Ck*Cm,mul_nonneg hCk hCm.le,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hblock⟩:=hblock Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRcap hcond r hX1 hX2 hY1 hY2
  have hp0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hh':=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hp0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hp0 1
  let V:=volume s.toData
  let a:ℝ:=(∏i,s.lo i)*wlo*wlo
  let F:=Ck*profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ+2*B*θ-2*max r 0/3)*V^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
    have hzp:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F,V]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hcap)
    true s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) V F
    hKphys hRcap hcap (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:CenteredMomentSecondBlockAggregate.SourceBlocks q.val.1 q.val.2 U Kphys R (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U R
        (partRows true s.η χ₀ Q m q.val.1 q.val.2 U R) W Kphys (fun i=>(n i:ℤ))‖/V≤
          F*radicalWeight q.val.1 q.val.2:=by
    intro q hq U n
    have hg:=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource S β) _ _ q.property
    have hcnd:(expandedFactor s.η:ℝ)*R0.absNorm*q.val.1.absNorm*q.val.2.absNorm*(4*R)≤Z^B:=by
      apply le_trans _ hcond
      have hH:0≤sourceRadius s:=(Nat.cast_nonneg q.val.1.absNorm).trans hg.2.2.2.2.2.1
      calc
        _=(expandedFactor s.η:ℝ)*R0.absNorm*((q.val.1.absNorm:ℝ)*q.val.2.absNorm)*(4*R):=by ring
        _≤(expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s*sourceRadius s)*(4*R):=by
          gcongr
          · exact hg.2.2.2.2.2.1
          · exact hg.2.2.2.2.2.2
        _=_:=by ring
    have hh:=hZ.2 s p hlo hhi hP hW1 hW2 q.val.1 q.val.2 hs.1 hs.2 R0 seed hR0
      hg.2.2.2.1 hg.2.2.2.2.1 (hg.2.2.2.2.2.1.trans hcap) (hg.2.2.2.2.2.2.trans hcap)
      hg.2.2.1 U r hX1 hX2 hY1 hY2 χ₀ ((mem_liveLabels _ _ _ q).mp hq).1
      m hm hml hm2 hcap R Kphys hKphys hcnd (fun i=>(n i:ℤ))
    rw [←physicalBlock_active]
    exact hh.trans_eq (by dsimp only [F,V,a,radicalWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ=
      Z^(2*ε+2*δ+2*B*θ-2*max r 0/3):=by
    rw [←Real.rpow_add (zero_lt_one.trans hZ.1)]
    congr 1
    ring
  dsimp only [F,V,a]
  calc
    _=(Ck*Cm)*profileFactor Sprofile s p J Q K*
      (Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]


-- @@ L155-155 verbatim
end SevenEighths.CenteredMomentSecondExceptionalFixedQSource


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
