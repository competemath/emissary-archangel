import OAI.NumberTheory.DirichletL.Moments.SecondFrozenRatioCost
import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L9-9 verbatim
open Filter

-- @@ L10-10 verbatim
open SevenEighths.CenteredMomentSecondNonexceptionalScalar


-- @@ L12-12 verbatim
namespace SevenEighths.CenteredMomentSecondFrozenLiveSource

-- @@ L13-13 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion

-- @@ L14-14 verbatim
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L15-15 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost

-- @@ L16-16 verbatim
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate

-- @@ L17-17 verbatim
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate

-- @@ L18-18 verbatim
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass

-- @@ L19-19 verbatim
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource

-- @@ L20-20 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst

-- @@ L21-21 verbatim
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization

-- @@ L22-22 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource

-- @@ L23-23 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise

-- @@ L24-24 verbatim
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy

-- @@ L25-25 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily

-- @@ L26-26 verbatim
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair

-- @@ L27-27 verbatim
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget

-- @@ L28-28 verbatim
open CenteredMomentSecondActivePhysicalDictionary

-- @@ L29-29 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar

-- @@ L30-30 verbatim
local notation "O" => HeckeFamily.O

-- @@ L31-31 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

-- @@ L32-32 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L34-144 verbatim
theorem original_nonexceptional_energy (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (B L Cr δ ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hδ:0<δ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀s:Input ι,(∀i,s.lo i=lo i)→(∀i,s.hi i=hi i)→
      s.W₁ 0=0→s.W₂ 0=0→0≤sourceRadius s→sourceRadius s≤Z^B→
    ∀R0 seed:Ideal O,Squarefree seed→seed≠0→
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀(χ₀:RayCharacter)(Q:Ideal O)(m:O),Q≤Ideal.span {(72:O)}→
      m≠0→goodLambda∣m→(2:O)∣m→
    ∀Kphys Tsec ξ:ℝ,0<Kphys→frequencyRadius Tsec Z ξ≤Cr*Z^L→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      C*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ) := by
  obtain ⟨Ck,hCk,hblock⟩:=actual_canonical_child_ratio_cost lo hi W J₁ J₂ B δ hB hδ
  obtain ⟨Cm,hCm,hmass⟩:=source_part_harmonic_bound B L Cr ε hB hL hCr hε
  refine ⟨Ck*Cm,mul_pos hCk hCm,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s hlo hhi hz1 hz2 hH0 hH R0 seed hseed hseed0 S β
  have hg (q:ActiveLabel S β):=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
  have hs (q:ActiveLabel S β):=commonLabels_supported (activeSource S β) _ _ q.property
  choose τ hf using fun (q:ActiveLabel S β) (U:Finset (CommonIndex q.val.1 q.val.2))=>
    exists_exceptional_family s.η q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.1 U
  refine ⟨τ,hf,?_⟩
  intro χ₀ Q m hQ hm hml hm2 Kphys Tsec ξ hKphys hR E₁ E₂ hE₁ hE₂ hleft hright
  let F:=Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
    Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by
    have hp:=profileCost_nonneg s
    have ht:=heightEnvelope_pos s.t
    have hm1:=profileMoment_nonneg J₁
    have hm2:=profileMoment_nonneg J₂
    have hz:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hH)
    false s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) (volume s.toData) F
    hKphys hR hH (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))‖/volume s.toData≤F*pairWeight q.val.1 q.val.2:=by
    intro q hq U n
    by_cases hzero:physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))=0
    · rw [hzero,norm_zero,zero_div]
      exact mul_nonneg hF (pairWeight_nonneg _ _)
    · have hh:=hZ.2 Kphys hKphys (fun i=>(n i:ℤ)) s (τ q U) hlo hhi R0 seed
        q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.2.1 (hg q).2.2.2.2.1
        ((hg q).2.2.2.2.2.1.trans hH) ((hg q).2.2.2.2.2.2.trans hH) (hg q).2.2.1 U (hf q U)
        hz1 hz2 hH0 hH (frequencyRadius Tsec Z ξ) Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂
        (hleft q hq U n hzero) (hright q hq U n hzero)
      rw [←physicalBlock_active]
      exact hh.trans_eq (by dsimp only [F,pairWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*δ)*Z^ε=Z^(2*δ+ε):=by rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [F]
  calc
    _=(Ck*Cm)*(Z^(2*δ)*Z^ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]

-- @@ L145-145 verbatim
end SevenEighths.CenteredMomentSecondFrozenLiveSource


-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end OAI
