import OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated
import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform
import OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary


-- @@ L19-19 verbatim
namespace OAI


-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff


-- @@ L24-24 verbatim
namespace SevenEighths.CenteredMomentEnergyCanonicalMainSubsets

-- @@ L25-25 verbatim
open HeckeFamily ConcreteTraceCRT

-- @@ L26-26 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

-- @@ L27-27 verbatim
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

-- @@ L28-28 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

-- @@ L29-29 verbatim
open CenteredMomentRadialEligibleEnergy

-- @@ L30-30 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L31-31 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]

-- @@ L32-32 verbatim
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


-- @@ L34-34 verbatim
open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity

-- @@ L35-35 verbatim
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid

-- @@ L36-36 verbatim
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport

-- @@ L37-37 verbatim
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

-- @@ L38-38 verbatim
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous

-- @@ L39-39 verbatim
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

-- @@ L40-40 verbatim
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L41-41 verbatim
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

-- @@ L42-42 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero

-- @@ L43-43 verbatim
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

-- @@ L44-44 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

-- @@ L45-45 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

-- @@ L46-46 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

-- @@ L47-47 verbatim
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

-- @@ L48-48 verbatim
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound


-- @@ L50-50 verbatim
open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

-- @@ L51-51 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L52-52 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L53-53 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L55-55 verbatim
open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary

-- @@ L56-56 verbatim
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon

-- @@ L57-57 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

-- @@ L58-58 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

-- @@ L59-59 verbatim
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

-- @@ L60-60 verbatim
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

-- @@ L61-61 verbatim
open CenteredMomentSecondHeightFamily

-- @@ L62-62 verbatim
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius


-- @@ L64-64 verbatim
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

-- @@ L65-65 verbatim
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

-- @@ L66-66 verbatim
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

-- @@ L67-67 verbatim
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

-- @@ L68-68 verbatim
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

-- @@ L69-69 verbatim
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

-- @@ L70-70 verbatim
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates


-- @@ L72-72 verbatim
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

-- @@ L73-209 verbatim
theorem actual_original_subsets_main_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=>lows i.val) (fun i=>highs i.val)
      (fun i=>hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=>hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0<Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1<Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤Jheight:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|t|+height)^(Jj Aorig)≤(1+|t|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|t|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity


-- @@ L211-211 verbatim
end SevenEighths.CenteredMomentEnergyCanonicalMainSubsets


-- @@ L213-213 verbatim
end


-- @@ L215-215 verbatim
end OAI
