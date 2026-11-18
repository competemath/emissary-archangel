import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff


-- @@ L13-13 verbatim
namespace SevenEighths.CenteredMomentEnergyCanonicalMainUniform

-- @@ L14-14 verbatim
open HeckeFamily ConcreteTraceCRT

-- @@ L15-15 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

-- @@ L16-16 verbatim
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

-- @@ L17-17 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

-- @@ L18-18 verbatim
open CenteredMomentRadialEligibleEnergy

-- @@ L19-19 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L20-20 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]


-- @@ L22-22 verbatim
open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity

-- @@ L23-23 verbatim
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid

-- @@ L24-24 verbatim
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport

-- @@ L25-25 verbatim
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

-- @@ L26-26 verbatim
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous

-- @@ L27-27 verbatim
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

-- @@ L28-28 verbatim
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L29-29 verbatim
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

-- @@ L30-30 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero

-- @@ L31-31 verbatim
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

-- @@ L32-32 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

-- @@ L33-33 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

-- @@ L34-34 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

-- @@ L35-35 verbatim
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

-- @@ L36-36 verbatim
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound


-- @@ L38-38 verbatim
open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

-- @@ L39-39 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L40-40 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L41-41 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L43-43 verbatim
open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary

-- @@ L44-44 verbatim
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon

-- @@ L45-45 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

-- @@ L46-46 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

-- @@ L47-47 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

-- @@ L48-48 verbatim
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

-- @@ L49-49 verbatim
open CenteredMomentSecondHeightFamily

-- @@ L50-50 verbatim
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius


-- @@ L52-152 verbatim
theorem actual_main_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+
          (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3)+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    CenteredMomentEnergyCanonicalMainPaid.actual_main_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
  obtain ⟨Zr,hZr,hr⟩:=CenteredMomentFirstAmplifiedPaidReserve.eventually_actual_amplified_reserves
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hsmall:sourceReserve src (child src C R0 B τ t) C D Z delta reserve cost asource≤
      delta+reserve+θsource:=
    (hr Z hZrZ src hcard hlowerSrc hupperSrc C D R0 hC.1 hD.1 B τ t delta reserve cost asource
      hdelta hreserve hcost haSource).1
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad:=
    envelope_pos _ (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)


-- @@ L154-154 verbatim
end SevenEighths.CenteredMomentEnergyCanonicalMainUniform


-- @@ L156-156 verbatim
end


-- @@ L158-158 verbatim
end OAI
