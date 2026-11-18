import OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing
import OAI.NumberTheory.DirichletL.Eisenstein.CuspResidues


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open MulChar AddChar

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory Real

-- @@ L14-14 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L15-15 verbatim
open Finset Complex

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open Filter Real Asymptotics

-- @@ L19-19 verbatim
open ActualEisensteinCubic

-- @@ L20-20 verbatim
open Filter

-- @@ L21-21 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L22-22 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open scoped Topology

-- @@ L25-25 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L26-26 verbatim
open MulChar AddChar

-- @@ L27-27 verbatim
open Filter Asymptotics

-- @@ L28-28 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L29-29 verbatim
open Filter

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L33-33 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L34-34 verbatim
open scoped Topology

-- @@ L35-35 verbatim
open Filter Asymptotics

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Filter Asymptotics

-- @@ L42-42 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L43-43 verbatim
open scoped Topology

-- @@ L44-44 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L45-45 verbatim
open Filter

-- @@ L46-46 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L47-47 verbatim
open scoped Topology

-- @@ L48-48 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L49-49 verbatim
open scoped Topology

-- @@ L50-50 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L51-51 verbatim
open scoped Topology

-- @@ L52-52 verbatim
open MeasureTheory Real

-- @@ L53-53 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical

-- @@ L60-60 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L61-61 verbatim
open scoped BigOperators Classical

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical

-- @@ L66-66 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L67-67 verbatim
open MeasureTheory Set

-- @@ L68-68 verbatim
open scoped BigOperators

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators

-- @@ L74-74 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L75-75 verbatim
open scoped BigOperators Classical


-- @@ L77-77 verbatim
namespace CubicEisenstein


-- @@ L79-79 verbatim
section

-- @@ L80-80 verbatim
open Filter MeasureTheory

-- @@ L81-81 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise


-- @@ L83-83 verbatim
open CubicKubota

-- @@ L84-84 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L86-95 verbatim
lemma globalKubotaKernel_conjugate_mem (M : levelThree) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨n,hn,hnval⟩ := N.property
  change (n:SL(2,ActualEisensteinCubic.O))=(N:SL(2,ActualEisensteinCubic.O)) at hnval
  refine ⟨M*n*M⁻¹,?_,?_⟩
  · change finiteCubicMultiplier (M*n*M⁻¹)=1
    change finiteCubicMultiplier n=1 at hn
    simp only [map_mul,map_inv,hn,mul_one,mul_inv_cancel]
  · change (M:SL(2,ActualEisensteinCubic.O))*(n:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹=_
    rw [hnval]


-- @@ L97-102 verbatim
def kernelConjugate (M : levelThree) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹,globalKubotaKernel_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]


-- @@ L104-105 verbatim
lemma kernelConjugate_coe (M : levelThree) (N : globalKubotaKernel) :
    (kernelConjugate M N : SL(2,ActualEisensteinCubic.O))=(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹ := rfl


-- @@ L107-117 verbatim
lemma level_action_respects_kernel (M : levelThree) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (complexMatrix M • u) (complexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (complexMatrix M • u)=complexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change complexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((complexMatrix M)⁻¹ • (complexMatrix M • u)))=_
  rw [inv_smul_smul,hN]


-- @@ L119-120 verbatim
def kernelLevelAction (M : levelThree) : KernelQuotient→KernelQuotient :=
  Quotient.map' (fun w => complexMatrix M • w) (level_action_respects_kernel M)


-- @@ L122-124 verbatim
lemma kernelLevelAction_mk (M : levelThree) (w : HyperbolicSpace) :
    kernelLevelAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • w) := rfl


-- @@ L126-130 verbatim
lemma kernelLevelAction_one (q : KernelQuotient) : kernelLevelAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]


-- @@ L132-138 verbatim
lemma kernelLevelAction_mul (M N : levelThree) (q : KernelQuotient) :
    kernelLevelAction (M*N) q=kernelLevelAction M (kernelLevelAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • (complexMatrix N • w))
    rw [map_mul,mul_smul]


-- @@ L140-141 verbatim
lemma kernelLevelAction_continuous (M : levelThree) : Continuous (kernelLevelAction M) :=
  (continuous_hyperbolic_action (complexMatrix M)).quotient_map' (level_action_respects_kernel M)


-- @@ L143-149 verbatim
def kernelLevelHomeomorph (M : levelThree) : KernelQuotient ≃ₜ KernelQuotient where
  toFun := kernelLevelAction M
  invFun := kernelLevelAction M⁻¹
  left_inv q := by rw [←kernelLevelAction_mul,inv_mul_cancel,kernelLevelAction_one]
  right_inv q := by rw [←kernelLevelAction_mul,mul_inv_cancel,kernelLevelAction_one]
  continuous_toFun := kernelLevelAction_continuous M
  continuous_invFun := kernelLevelAction_continuous M⁻¹


-- @@ L151-157 verbatim
lemma kernelLevelAction_eisenstein (M : levelThree) (s : ℂ) (hs : 2<s.re)
    (q : KernelQuotient) :
    kernelQuotientEisenstein s hs (kernelLevelAction M q)=
      complexCharacter M*kernelQuotientEisenstein s hs q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact hyperbolicEisenstein_automorphy M s hs w


-- @@ L159-162 verbatim
lemma kernelLevelAction_seed (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientSeed a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeed_automorphy a b s M w


-- @@ L164-167 verbatim
lemma kernelLevelAction_defect (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientDefect a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientDefect a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeedDefect_automorphy a b s M w


-- @@ L169-185 verbatim
lemma kernelLevelAction_fundamentalDomain (M : levelThree) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => complexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (complexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (complexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (complexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelConjugate M⁻¹).toEquiv
  intro N w
  change complexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (complexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change complexMatrix M • (((complexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((complexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]


-- @@ L187-206 verbatim
lemma kernelLevelAction_measurePreserving (M : levelThree) :
    MeasurePreserving (kernelLevelAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelLevelAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => complexMatrix M • w
  have hmap := (measurePreserving_smul (complexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (complexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelLevelAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelLevelAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelLevelAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelLevelAction_fundamentalDomain M)


-- @@ L208-208 verbatim
end


-- @@ L210-210 verbatim
open Filter MeasureTheory

-- @@ L211-211 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L213-213 verbatim
open CubicKubota


-- @@ L215-216 verbatim
def kernelLevelPullback (M : levelThree) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelLevelAction M) (kernelLevelAction_measurePreserving M)


-- @@ L218-221 verbatim
lemma kernelLevelPullback_ae_eq (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelLevelAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelLevelAction_measurePreserving M)


-- @@ L223-226 verbatim
lemma kernelLevelPullback_one (F : KernelQuotientL2) : kernelLevelPullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq 1 F] with q hq
  simpa only [kernelLevelAction_one] using hq


-- @@ L228-236 verbatim
lemma kernelLevelPullback_comp (M N : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M (kernelLevelPullback N F)=kernelLevelPullback (N*M) F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLevelPullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelLevelPullback N F),hcomp,
    kernelLevelPullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelLevelAction_mul N M q).symm)


-- @@ L238-241 verbatim
lemma kernelLevelPullback_surjective (M : levelThree) : Function.Surjective (kernelLevelPullback M) := by
  intro F
  refine ⟨kernelLevelPullback M⁻¹ F,?_⟩
  rw [kernelLevelPullback_comp,inv_mul_cancel,kernelLevelPullback_one]


-- @@ L243-244 verbatim
def kernelLevelUnitary (M : levelThree) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelLevelPullback M) (kernelLevelPullback_surjective M)


-- @@ L246-247 verbatim
lemma kernelLevelUnitary_apply (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelUnitary M F=kernelLevelPullback M F := rfl


-- @@ L249-259 verbatim
lemma kernelLevelPullback_defect (M : levelThree) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelLevelPullback M (kernelL2Defect a b ha hab s)=
      complexCharacter M • kernelL2Defect a b ha hab s := by
  have hdef := kernelL2Defect_ae_eq a b ha hab s
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hdef
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelL2Defect a b ha hab s),hcomp,hdef,
    Lp.coeFn_smul (complexCharacter M) (kernelL2Defect a b ha hab s)] with q hp hc hd hs
  change _=complexCharacter M * kernelL2Defect a b ha hab s q at hs
  rw [hp,hs,hd]
  exact hc.trans (kernelLevelAction_defect M a b s q)


-- @@ L261-273 verbatim
lemma kernelLevelPullback_of_remainder_ae (M : levelThree) (a b : ℝ) (s : ℂ)
    (hs : 2<s.re) (F : KernelQuotientL2)
    (hF : F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M F=complexCharacter M • F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hF
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M F,hcomp,hF,Lp.coeFn_smul (complexCharacter M) F]
    with q hp hc hf hsmul
  change _=complexCharacter M*F q at hsmul
  rw [hp,hsmul,hf]
  dsimp only [Function.comp_def] at hc
  rw [hc,kernelLevelAction_eisenstein,kernelLevelAction_seed,mul_sub]


-- @@ L275-303 verbatim
lemma kernelCorrection_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    ∀s∈cuspUpperParameterRegion,
      kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s)=
        complexCharacter M • kernelEisensteinL2Correction a b ha hab s := by
  have hc : AnalyticOnNhd ℂ (kernelEisensteinL2Correction a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      cuspUpperParameterRegion := by
    intro s hs
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelLevelPullback M).toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hr : AnalyticOnNhd ℂ (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s)
      cuspUpperParameterRegion := by
    intro s hs
    exact (hc s hs).const_smul (c := complexCharacter M)
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLevelPullback_of_remainder_ae M a b s (by linarith [hs.1]) _ (hoverlap s hs.1 hs.2)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hevent


-- @@ L305-319 verbatim
lemma thetaApproach_tendsto_complex_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Continuous (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
    have ht := (hh.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith


-- @@ L321-349 verbatim
lemma kernelEisensteinResidueVector_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
      complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  have hlim := (kernelEisensteinResidueVector_limit a b ha hab).comp thetaApproach_tendsto_complex_punctured
  have hl := (kernelLevelPullback M).continuous.continuousAt.tendsto.comp hlim
  have hr := hlim.const_smul (complexCharacter M)
  have hevent :
      (fun t : ℝ => kernelLevelPullback M
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ => complexCharacter M •
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I∈cuspUpperParameterRegion := by
      simp only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      norm_num
      exact ht
    rw [map_smul,kernelCorrection_character_of_initial_overlap M a b ha hab hoverlap _ hs]
    exact smul_comm _ _ _
  exact tendsto_nhds_unique_of_eventuallyEq hl hr hevent


-- @@ L351-369 verbatim
lemma kernelCuspAverageFamily_eq_of_initial_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspAverageFamily a b ha hab s=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hrestr := ae_restrict_of_ae hcorrected (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  rw [kernelCuspAverageFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact hw.trans (kernelQuotientEisenstein_mk s hs w)


-- @@ L371-384 verbatim
lemma kernelEisensteinResidueVector_nonzero_character_of_initial_overlap (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelEisensteinResidueVector a b ha hab≠0 ∧
      ∀M : levelThree,kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
        complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  constructor
  · apply kernelEisensteinResidueVector_ne_zero_of_overlap a b ha hab
    intro s hs hi
    exact kernelCuspAverageFamily_eq_of_initial_overlap a b ha hab s (by linarith) (hoverlap s hs hi)
  · intro M
    exact kernelEisensteinResidueVector_character_of_initial_overlap M a b ha hab hoverlap


-- @@ L386-386 verbatim
end CubicEisenstein


-- @@ L388-388 verbatim
open scoped BigOperators

-- @@ L389-389 verbatim
namespace QuadraticAllOddCRT

-- @@ L390-390 verbatim
open ActualEisensteinCubic

-- @@ L391-391 verbatim
open QuadraticGaussRay hiding O

-- @@ L392-392 verbatim
open ActualEisensteinCoordinates hiding O omega

-- @@ L393-393 verbatim
open EisensteinEPrimaryPhase (Coord odd)


-- @@ L395-397 verbatim
def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3


-- @@ L399-399 verbatim
def fourthRoot (a : ZMod 4) : ℂ := Complex.I^(a.val:ℤ)


-- @@ L401-406 verbatim
lemma fourthRoot_add (a b : ZMod 4) : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp


-- @@ L408-421 verbatim
lemma quadraticRayValue_eq_fourthRoot (r : Coord) (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf


-- @@ L423-427 verbatim
def quadraticRaySign (r s : Coord) : ℤ :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0


-- @@ L429-435 verbatim
lemma quadraticRaySign_mul_left (r s t : Coord) :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide
  exact h r s t


-- @@ L437-443 verbatim
lemma quadraticRaySign_mul_right (r s t : Coord) :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  have h : ∀r s t : Coord,
      quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
        quadraticRaySign r s*quadraticRaySign r t := by decide
  exact h r s t


-- @@ L445-447 verbatim
lemma quadraticRaySign_symm (r s : Coord) : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide
  exact h r s


-- @@ L449-453 verbatim
lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [ite_eq_left ⟨hr,hs⟩]
  split_ifs <;> norm_num


-- @@ L455-461 verbatim
lemma quadraticRaySign_exponent (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide
  exact h r s hr hs


-- @@ L463-468 verbatim
lemma quadraticRaySign_root (r s : Coord) (hr : odd r) (hs : odd s) :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]


-- @@ L470-472 verbatim
lemma odd_mul (r s : Coord) (hr : odd r) (hs : odd s) : odd (EisensteinEPrimaryPhase.mul r s) := by
  have h : ∀r s : Coord,odd r → odd s → odd (EisensteinEPrimaryPhase.mul r s) := by decide
  exact h r s hr hs


-- @@ L474-479 verbatim
theorem quadraticRayValue_mul (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul r s hr hs),quadraticRaySign_exponent r s hr hs,
    fourthRoot_add,fourthRoot_add,quadraticRaySign_root r s hr hs,
    quadraticRayValue_eq_fourthRoot r hr,quadraticRayValue_eq_fourthRoot s hs]


-- @@ L481-487 verbatim
lemma quadraticRayPair_eq_sign (r s : Coord) (hr : odd r) (hs : odd s) :
    MixedCrossSeparation.quadraticRayPair r s=(quadraticRaySign r s:ℂ) := by
  unfold MixedCrossSeparation.quadraticRayPair
  rw [quadraticRayValue_mul r s hr hs]
  apply (div_eq_iff (mul_ne_zero (quadraticRayValue_ne_zero_of_odd r hr)
    (quadraticRayValue_ne_zero_of_odd s hs))).mpr
  ring


-- @@ L489-489 verbatim
end QuadraticAllOddCRT


-- @@ L491-491 verbatim
open scoped BigOperators Classical

-- @@ L492-492 verbatim
namespace CanonicalRowCompletion


-- @@ L494-494 verbatim
section

-- @@ L495-495 verbatim
open ActualEisensteinCubic

-- @@ L496-496 verbatim
open CompletedGauss hiding O

-- @@ L497-497 verbatim
open CanonicalQuadraticSieve hiding O

-- @@ L498-498 verbatim
open CubicJacobiGlobal hiding O

-- @@ L499-499 verbatim
open QuadraticGaussRay hiding O

-- @@ L500-500 verbatim
open QuadraticAllOddCRT

-- @@ L501-501 verbatim
open ActualEisensteinCoordinates hiding O omega

-- @@ L502-502 verbatim
open UniqueFactorizationMonoid


-- @@ L504-508 verbatim
lemma supported_factors_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩


-- @@ L510-512 verbatim
lemma idealRowHom_one_supported (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) : idealRowHom 1 I=1 := by
  have h := CanonicalUnitEuler.idealRowHom_unit_norm (1:ActualEisensteinCubic.Oˣ) I hI.1 (supported_factors_good I hI)
  simpa using h


-- @@ L514-517 verbatim
lemma supported_prime_data (p : ActualEisensteinCubic.O) (hp : Prime p) (hs : Supported (Ideal.span {p})) :
    lambda∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) ∧ ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)


-- @@ L519-520 verbatim
lemma supported_residue_odd (p : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {p})) : EisensteinEPrimaryPhase.odd (residue p) :=
  (ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2


-- @@ L522-569 verbatim
theorem idealRowHom_prime_reciprocity (p q : ActualEisensteinCubic.O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q})) :
    idealRowHom q (Ideal.span {p})=
      (quadraticRaySign (residue p) (residue q):ℂ)*idealRowHom p (Ideal.span {q}) := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  obtain ⟨hgP,hcP⟩ := supported_prime_data p hp hsP
  obtain ⟨hgQ,hcQ⟩ := supported_prime_data q hq hsQ
  by_cases he : (Ideal.span {p}:Ideal ActualEisensteinCubic.O)=Ideal.span {q}
  · have hqp : q∈(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by rw [he];exact Ideal.subset_span (by simp)
    have hpq : p∈(Ideal.span {q}:Ideal ActualEisensteinCubic.O) := by rw [←he];exact Ideal.subset_span (by simp)
    rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
      Ideal.Quotient.eq_zero_iff_mem.mpr hqp,Ideal.Quotient.eq_zero_iff_mem.mpr hpq]
    simp only [MulChar.map_zero,mul_zero]
  · have hcop : IsCoprime (Ideal.span {p}:Ideal ActualEisensteinCubic.O) (Ideal.span {q}) := Ideal.isCoprime_of_isMaximal he
    have hqp : q∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by
      intro h
      apply he
      exact ((inferInstance : (Ideal.span {q}:Ideal ActualEisensteinCubic.O).IsMaximal).eq_of_le
        (Ideal.IsMaximal.ne_top inferInstance)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))).symm
    have h2 : idealRowHom q (Ideal.span {p})^2=idealRowHom p (Ideal.span {q})^2 := by
      rw [idealRowHom_square,idealRowHom_square]
      exact congrArg ConcreteTraceCRT.eisEmbedding (symbol_reciprocity q p hq.ne_zero hp.ne_zero hprimaryQ hprimaryP)
    have h6 : idealRowHom q (Ideal.span {p})^6=1 := by
      rw [idealRowHom_prime q _ hgP]
      have h := canonicalSextic_sixth_power_mask (Ideal.span {p}) hgP q
      change actualSextic _ hgP (Ideal.Quotient.mk _ (q^6))=_ at h
      simpa only [map_pow,ite_eq_right hqp] using h
    have hcross := quadratic_ray_cross p q hp.ne_zero hq.ne_zero hcop hcP hcQ
    rw [residue_mul,quadraticRayValue_mul _ _ (supported_residue_odd p hsP) (supported_residue_odd q hsQ)] at hcross
    have h3 (x y : ActualEisensteinCubic.O) (hg : lambda∉(Ideal.span {x}:Ideal ActualEisensteinCubic.O)) [(Ideal.span {x}).IsMaximal] :
        idealRowHom y (Ideal.span {x})^3=
          character (Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) y) := by
      rw [idealRowHom_prime y _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    have hc : idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3=
        (quadraticRaySign (residue p) (residue q):ℂ) := by
      rw [h3 p q hgP,h3 q p hgQ]
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd p hsP))
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd q hsQ))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hcross.symm
    calc
      _ = idealRowHom q (Ideal.span {p})*idealRowHom q (Ideal.span {p})^6 := by rw [h6,mul_one]
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom q (Ideal.span {p})^2)^2 := by ring
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom p (Ideal.span {q})^2)^2 := by rw [h2]
      _ = (idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3)*idealRowHom p (Ideal.span {q}) := by ring
      _ = _ := by rw [hc]


-- @@ L571-571 verbatim
end


-- @@ L573-573 verbatim
open ActualEisensteinCubic

-- @@ L574-574 verbatim
open CompletedGauss hiding O

-- @@ L575-575 verbatim
open CanonicalQuadraticSieve hiding O

-- @@ L576-576 verbatim
open CubicJacobiGlobal hiding O

-- @@ L577-577 verbatim
open QuadraticAllOddCRT

-- @@ L578-578 verbatim
open ActualEisensteinCoordinates hiding O omega


-- @@ L580-581 verbatim
def sexticReciprocityPhase (a b : ActualEisensteinCubic.O) : ℂ :=
  (quadraticRaySign (residue a) (residue b):ℂ)


-- @@ L583-585 verbatim
lemma sexticReciprocityPhase_mul_left (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase (a*b) c=sexticReciprocityPhase a c*sexticReciprocityPhase b c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_left,Int.cast_mul]


-- @@ L587-589 verbatim
lemma sexticReciprocityPhase_mul_right (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase a (b*c)=sexticReciprocityPhase a b*sexticReciprocityPhase a c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_right,Int.cast_mul]


-- @@ L591-599 verbatim
lemma sexticReciprocityPhase_one_right (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase a 1=1 := by
  have h1 : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0) := by
    have h : (1:ActualEisensteinCubic.O)=eval 1 0 := by simp [eval]
    rw [h,residue_eval]
    norm_num
  have ht : ∀r : EisensteinEPrimaryPhase.Coord,EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1:ZMod 4),0)=1 := by decide
  simp only [sexticReciprocityPhase,h1,ht _ (supported_residue_odd a ha),Int.cast_one]


-- @@ L601-605 verbatim
lemma sexticReciprocityPhase_one_left (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase 1 a=1 := by
  have he : sexticReciprocityPhase 1 a=sexticReciprocityPhase a 1 := by
    simp only [sexticReciprocityPhase,quadraticRaySign_symm]
  rw [he,sexticReciprocityPhase_one_right a ha]


-- @@ L607-632 verbatim
lemma idealRowHom_prime_primary_reciprocity (p b : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimaryP : lambda^2∣p-1) (hprimaryB : lambda^2∣b-1)
    (hsP : Supported (Ideal.span {p})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {p})=sexticReciprocityPhase p b*idealRowHom p (Ideal.span {b}) := by
  have hb0 : b≠0 := by
    intro h
    apply hsB.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization b hb0 hprimaryB
  rw [←hprod] at hsB ⊢
  clear hprod hb0 hprimaryB b
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsP,sexticReciprocityPhase_one_right p hsP,mul_one]
  | @cons q s ih =>
    have hq := hfactors q (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {q}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsB
    rw [Multiset.prod_cons,idealRowHom_argument_mul,←Ideal.span_singleton_mul_span_singleton,
      map_mul,sexticReciprocityPhase_mul_right,
      idealRowHom_prime_reciprocity p q hp hq.1 hprimaryP hq.2 hsP hsplit.1,
      ih hsplit.2 htail]
    simp only [sexticReciprocityPhase]
    ring


-- @@ L634-658 verbatim
theorem idealRowHom_primary_reciprocity (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=sexticReciprocityPhase a b*idealRowHom a (Ideal.span {b}) := by
  have ha0 : a≠0 := by
    intro h
    apply hsA.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization a ha0 hprimaryA
  rw [←hprod] at hsA ⊢
  clear hprod ha0 hprimaryA a
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsB,sexticReciprocityPhase_one_left b hsB,one_mul]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsA
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_argument_mul,sexticReciprocityPhase_mul_left,
      idealRowHom_prime_primary_reciprocity p b hp.1 hp.2 hprimaryB hsplit.1 hsB,
      ih hsplit.2 htail]
    ring


-- @@ L660-666 verbatim
theorem idealRowHom_primary_reciprocity_ray (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=
      MixedCrossSeparation.quadraticRayPair (residue a) (residue b)*idealRowHom a (Ideal.span {b}) := by
  rw [quadraticRayPair_eq_sign _ _ (supported_residue_odd a hsA) (supported_residue_odd b hsB)]
  exact idealRowHom_primary_reciprocity a b hprimaryA hprimaryB hsA hsB


-- @@ L668-675 verbatim
theorem idealRowHom_ideal_reciprocity (I J : Ideal ActualEisensteinCubic.O) (hI : Supported I) (hJ : Supported J) :
    idealRowHom (primaryGenerator J) I=
      sexticReciprocityPhase (primaryGenerator I) (primaryGenerator J)*idealRowHom (primaryGenerator I) J := by
  have hpI := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have hpJ := primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)
  have h := idealRowHom_primary_reciprocity (primaryGenerator I) (primaryGenerator J)
    hpI.2 hpJ.2 (by rwa [hpI.1]) (by rwa [hpJ.1])
  simpa only [hpI.1,hpJ.1] using h


-- @@ L677-677 verbatim
end CanonicalRowCompletion


-- @@ L679-679 verbatim
end


-- @@ L681-681 verbatim
end OAI
