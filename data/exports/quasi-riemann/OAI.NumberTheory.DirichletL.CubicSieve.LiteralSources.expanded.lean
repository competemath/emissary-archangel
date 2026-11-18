import OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators


-- @@ L73-73 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L74-74 verbatim
namespace SecondPassArithmetic

-- @@ L75-75 verbatim
open ActualEisensteinCubic

-- @@ L76-76 verbatim
open JointLogSeparation (frequencyTwist)

-- @@ L77-77 verbatim
open SecondPassIntegration (densityChildEnergy)


-- @@ L79-79 verbatim
section

-- @@ L80-83 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


-- @@ L85-89 verbatim
def globalSecondLiteralBinSource (γ : GlobalSecondData ι → ℂ)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) : ℂ :=
  ∑ ray : SecondRayIndex,∑ x∈globalLogSector p s side j,
    γ x * globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g₁ g₂ W ell Y side x


-- @@ L91-98 verbatim
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalArithmeticBin {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (f : GlobalSecondData ι → M) :
    ∑ x∈globalLogSector p s side j,f x =
    ∑ q∈globalBinTriples p s side j,∑ x∈globalArithmeticBin p s side q j,f x := by
  have h := sum_globalSecondFixedTriple p (globalLogSector p s side j) f
  simpa only [globalBinTriples,globalLogSector,globalArithmeticBin,Finset.filter_filter,and_comm] using h

-- @@ L99-99 verbatim
end


-- @@ L101-160 verbatim
theorem globalSecondLiteralBinSource_transfer
    (ε : ℝ) (hε : 0 < ε) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (M : ℝ) (hM : 0 ≤ M)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ M) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ M)
    (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0 ≤ C ∧
      (∀ i,HasCompactSupport (windows i)) ∧
      (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
        (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨U,hUc,hUs,hUone,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := globalSecondLiteralTerm_twisted_profiles U hUc hUs
    g₁ g₂ W M hM (fun t ht => hUone t (hg₁ t ht)) (fun t ht => hUone t (hg₂ t ht)) hg₁ hg₂
  obtain ⟨C,hC,htrans⟩ := weightedGlobalPositiveBin_transfer ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have heq : globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
      (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j) =
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows ell (globalPooledRowScale K ell B F j) := by
    unfold globalSecondLiteralBinSource
    apply Finset.sum_congr rfl
    intro ray hray
    rw [sum_globalArithmeticBin p s side j]
    apply Finset.sum_congr rfl
    intro q hq
    unfold weightedGlobalArithmeticBinSource globalSecondRawSource
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have h := hid p hp hcop hg hinj hpr pool Ψ m ray θ₁ θ₂ ell
      (globalPooledRowScale K ell B F j) side x hell (hs x hxs).2.1 (hk x hxs)
    dsimp only at h
    rw [hxj] at h
    rw [h,mul_assoc]
  rw [heq]
  simpa only [globalDescentWeight,norm_neg] using
    htrans p hp hcop hg hinj hc (-θ₁) θ₂ K ell B F s side j pool Ψ m γ Γ
      hK hell hB hF hΓ hγ hΨ hs hk


-- @@ L162-162 verbatim
end SecondPassArithmetic


-- @@ L164-164 verbatim
namespace CubicEisenstein

-- @@ L165-165 verbatim
open Filter MeasureTheory

-- @@ L166-166 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise


-- @@ L168-168 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L170-174 verbatim
lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]


-- @@ L176-178 verbatim
lemma matrixFrobenius_nonneg (g : SL(2,ℂ)) : 0≤matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity


-- @@ L180-185 verbatim
lemma matrixFrobenius_mul_le (g h : SL(2,ℂ)) :
    matrixFrobenius (g*h)≤matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]


-- @@ L187-192 verbatim
lemma matrixFrobenius_inv (g : SL(2,ℂ)) : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring


-- @@ L194-196 verbatim
lemma hyperbolicFrobenius_nonneg (w : HyperbolicSpace) : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g


-- @@ L198-204 verbatim
lemma matrixFrobenius_le_displacement (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb


-- @@ L206-208 verbatim
instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩


-- @@ L210-229 verbatim
instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _


-- @@ L231-231 verbatim
end CubicEisenstein


-- @@ L233-233 verbatim
open Filter MeasureTheory

-- @@ L234-234 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise


-- @@ L236-236 verbatim
namespace CubicEisenstein


-- @@ L238-238 verbatim
section

-- @@ L239-239 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L241-242 verbatim
instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace

-- @@ L243-244 verbatim
instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace

-- @@ L245-246 verbatim
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology


-- @@ L248-249 verbatim
instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace

-- @@ L250-251 verbatim
instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace


-- @@ L253-261 verbatim
lemma integralOrbitRel_eq (H : Subgroup (SL(2,O))) :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  change (∃M:H,M • u=v) ↔ ∃M:H,M • v=u
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩


-- @@ L263-266 verbatim
instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance


-- @@ L268-270 verbatim
lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)


-- @@ L272-281 verbatim
lemma integralOrbitProjection_eq_iff (H : Subgroup (SL(2,O))) (u v : HyperbolicSpace) :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩


-- @@ L283-287 verbatim
theorem integralOrbitProjection_quotientCovering (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)


-- @@ L289-291 verbatim
lemma integralOrbitProjection_covering (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap


-- @@ L293-296 verbatim
lemma integralOrbitProjection_openQuotient (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩


-- @@ L298-299 verbatim
instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace

-- @@ L300-302 verbatim
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree)


-- @@ L304-305 verbatim
instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace


-- @@ L307-308 verbatim
lemma kernelQuotient_localHomeomorph : IsLocalHomeomorph (integralOrbitProjection globalKubotaKernel) :=
  (integralOrbitProjection_covering globalKubotaKernel globalKubotaKernel_le_levelThree).isLocalHomeomorph


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
open Filter MeasureTheory

-- @@ L313-313 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal


-- @@ L315-325 verbatim
lemma integralOrbitProjection_preimage_image (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (S : Set HyperbolicSpace) :
    integralOrbitProjection H ⁻¹' (integralOrbitProjection H '' S)=⋃M:H,M • S := by
  ext w
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff H w u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨M,⟨u,hu,hM⟩⟩
  · intro hw
    obtain ⟨M,u,hu,rfl⟩ := Set.mem_iUnion.mp hw
    exact ⟨u,hu,(integralOrbitProjection_eq H M u).symm⟩


-- @@ L327-342 verbatim
lemma kernelProjection_translates_disjoint (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)


-- @@ L344-358 verbatim
theorem kernelProjection_measure_image (S : Set HyperbolicSpace) (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)


-- @@ L360-379 verbatim
theorem kernelProjection_measurePreserving_on (U : Set HyperbolicSpace) (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    ext q
    constructor
    · rintro ⟨hq,w,hw,rfl⟩
      exact ⟨w,⟨hq,hw⟩,rfl⟩
    · rintro ⟨w,⟨hw,hu⟩,rfl⟩
      exact ⟨hw,⟨w,hu,rfl⟩⟩
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]


-- @@ L381-385 verbatim
theorem kernelL2_continuous_compact_approx (f : KernelQuotientL2) (ε : ℝ≥0∞) (hε : ε≠0) :
    ∃g : IntegralOrbitQuotient globalKubotaKernel → ℂ,
      HasCompactSupport g ∧ eLpNorm ((f : _ → ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)≤ε ∧
      Continuous g ∧ MemLp g 2 (integralQuotientVolume globalKubotaKernel) := by
  exact (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε


-- @@ L387-387 verbatim
end CubicEisenstein


-- @@ L389-389 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L390-390 verbatim
namespace SecondPassArithmetic


-- @@ L392-392 verbatim
section

-- @@ L393-393 verbatim
open ActualEisensteinCubic

-- @@ L394-394 verbatim
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)


-- @@ L396-400 verbatim
@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι


-- @@ L402-402 verbatim
namespace GlobalFirstData

-- @@ L403-403 verbatim
variable {ι : Type*}

-- @@ L404-405 verbatim
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩

-- @@ L406-406 verbatim
end GlobalFirstData


-- @@ L408-408 verbatim
namespace GlobalSecondData

-- @@ L409-409 verbatim
variable {ι : Type*}

-- @@ L410-411 verbatim
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩

-- @@ L412-412 verbatim
@[simp] theorem append_first (x : GlobalSecondData ι) : x.first.append x.source=x := by cases x; rfl

-- @@ L413-413 verbatim
@[simp] theorem first_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).first=b := rfl

-- @@ L414-414 verbatim
@[simp] theorem source_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).source=x := rfl

-- @@ L415-415 verbatim
end GlobalSecondData


-- @@ L417-417 verbatim
section

-- @@ L418-418 verbatim
variable {ι : Type*} [DecidableEq ι]


-- @@ L420-421 verbatim
def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon


-- @@ L423-425 verbatim
def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)


-- @@ L427-436 verbatim
theorem mem_globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (x : GlobalSecondData ι) :
    x∈globalFirstExpansionPool pool s cutoff ↔
      x.first∈s ∧ x.source∈secondExpansionPool (globalFirstRawPool pool x.first) (cutoff x.first) := by
  simp only [globalFirstExpansionPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,z,hz,rfl⟩
    exact ⟨hb,hz⟩
  · rintro ⟨hb,hx⟩
    exact ⟨x.first,hb,x.source,hx,x.append_first⟩


-- @@ L438-455 verbatim
theorem sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by
  unfold globalFirstExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro x hx y hy heq
    exact congrArg GlobalSecondData.source heq
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalSecondData.first heq).symm


-- @@ L457-457 verbatim
end


-- @@ L459-462 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


-- @@ L464-465 verbatim
def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell/(primeProductNorm p (b.cube.sideDivisor side)*primeProductNorm p b.common)


-- @@ L467-468 verbatim
def globalFirstBlockLabel (b : GlobalFirstData ι) : O :=
  secondBaseLabel p b.cube.support b.common b.cube.leftExponent b.cube.rightExponent b.cube.leftBit b.cube.rightBit


-- @@ L470-471 verbatim
def globalFirstBlockBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit


-- @@ L473-475 verbatim
def globalFirstBlockTest (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  normalizedColumn p (fun A => g (columnLog p
    (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) A))


-- @@ L477-486 verbatim
def globalFirstTruncatedSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondSource p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)


-- @@ L488-514 verbatim
theorem globalFirstTruncatedSource_eq_literal
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstExpansionPool pool s cutoff,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  unfold globalFirstTruncatedSource
  simp_rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  rw [Finset.sum_comm]
  simp_rw [sum_globalFirstExpansionPool]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold secondExpansionSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [globalSecondLiteralTerm,GlobalFirstData.append,GlobalSecondData.first,
    globalSecondRawPool,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    globalFirstBlockTest,globalFirstBlockColumnScale,globalFirstColumnScale,
    secondExpansionSource,Finset.sum_singleton,mul_assoc]


-- @@ L516-516 verbatim
end


-- @@ L518-518 verbatim
open ActualEisensteinCubic

-- @@ L519-519 verbatim
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)

-- @@ L520-520 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L521-521 verbatim
open RayFourExpansion (RayCharacter)


-- @@ L523-525 verbatim
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})


-- @@ L527-535 verbatim
def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayCharacter)
    (r : FirstCoreIndex) (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t z


-- @@ L537-540 verbatim
def globalFirstCoreCorrection (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) : ℝ :=
  ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon ∅‖^2


-- @@ L542-550 verbatim
def globalFirstSourceTail (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    secondSourceTail p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)


-- @@ L552-560 verbatim
def globalFirstSourceZero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)


-- @@ L562-575 verbatim
theorem globalFirstTruncatedSource_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      globalFirstTruncatedSource p hp hg hinj pool s w (fun b G E => (cutoff b G E).erase 0) Ψ m g W ell side Y +
      globalFirstSourceZero p hg pool s w cutoff Ψ m g W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceZero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncatedSecondSource_eq_nonzero_add_zero]
  exact mul_add _ _ _


-- @@ L577-606 verbatim
theorem globalFirstCoreRows_smoothed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b) :
    (∑ b∈s,w b*∑' z : O,W (‖eisEmbedding z‖^2/Y b)*
      (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)) =
      globalFirstTruncatedSource p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y +
      globalFirstSourceTail p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hX : 0 < globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc
    (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m g V W (globalFirstBlockColumnScale p ell side b) hX (Y b) (hY b hb)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (cutoff b)
  dsimp only at he
  have he' := congrArg (fun z : ℂ => w b*z) he
  simpa only [globalFirstCoreRow,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    secondBaseLabel,globalFirstBlockTest,mul_add,mul_assoc,Complex.ofReal_inv] using he'


-- @@ L608-649 verbatim
theorem globalFirstCoreRows_finite_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by
  have henergy : (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      (∑ b∈s,(w b : ℂ)*∑' z : O,rowMajorant (‖eisEmbedding z‖^2/Y b)*
        (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hh := firstCoreInputRow_finite_le_corrected_source p hg
      (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
      V (columnLog p (globalFirstBlockColumnScale p ell side b))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (T b) (Y b) (hY b hb) (hT b hb) (hT0 b hb)
    have hh' := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hh) (hw b hb)
    simpa only [globalFirstCoreRow,globalFirstCoreCorrection,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh'
  rw [globalFirstCoreRows_smoothed p hp hg hinj hc pool s (fun b => w b) cutoff Ψ m g V rowMajorant ell hell side χ r t Y hY,
    globalFirstTruncatedSource_split] at henergy
  exact henergy.trans ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)))


-- @@ L651-651 verbatim
end SecondPassArithmetic


-- @@ L653-653 verbatim
end


-- @@ L655-655 verbatim
end OAI
