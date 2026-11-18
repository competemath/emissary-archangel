import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedSixBranches


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace CubicEisenstein


-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open MulChar AddChar

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
open MeasureTheory Real

-- @@ L15-15 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L16-16 verbatim
open Finset Complex

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open scoped Classical

-- @@ L19-19 verbatim
open Filter Real Asymptotics

-- @@ L20-20 verbatim
open ActualEisensteinCubic

-- @@ L21-21 verbatim
open Filter

-- @@ L22-22 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L23-23 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L24-24 verbatim
open Filter

-- @@ L25-25 verbatim
open scoped Topology

-- @@ L26-26 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L27-27 verbatim
open MulChar AddChar

-- @@ L28-28 verbatim
open Filter Asymptotics

-- @@ L29-29 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L30-30 verbatim
open Filter

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open MulChar AddChar

-- @@ L33-33 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L34-34 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L35-35 verbatim
open scoped Topology

-- @@ L36-36 verbatim
open Filter Asymptotics

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L42-42 verbatim
open Filter Asymptotics

-- @@ L43-43 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L44-44 verbatim
open scoped Topology

-- @@ L45-45 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L46-46 verbatim
open Filter

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L52-52 verbatim
open scoped Topology

-- @@ L53-53 verbatim
open MeasureTheory Real

-- @@ L54-54 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open scoped BigOperators Classical

-- @@ L67-67 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L68-68 verbatim
open MeasureTheory Set

-- @@ L69-69 verbatim
open scoped BigOperators

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open scoped BigOperators Classical

-- @@ L72-72 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L73-73 verbatim
open scoped BigOperators

-- @@ L74-74 verbatim
open scoped BigOperators

-- @@ L75-75 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L76-76 verbatim
open scoped BigOperators Classical


-- @@ L78-78 verbatim
section

-- @@ L79-79 verbatim
open Filter MeasureTheory

-- @@ L80-80 verbatim
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace


-- @@ L82-82 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L84-97 verbatim
lemma integralConjugatePullback_inverse_left {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) :
    integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F)=F := by
  apply Lp.ext
  have hi := integralConjugatePullback_ae e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F
  have hc := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp hi
  filter_upwards [integralConjugatePullback_ae e g he hH hJ
    (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),hc]
    with q hq hqi
  dsimp only [Function.comp_def] at hqi
  rw [hq,hqi,integralConjugateMap_inverse]


-- @@ L99-110 verbatim
lemma integralConjugatePullback_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) (G : IntegralQuotientL2 J) :
    ⟪F,integralConjugatePullback e g he hH hJ G⟫_ℂ=
      ⟪integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F,G⟫_ℂ := by
  calc
    _ = ⟪integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),
      integralConjugatePullback e g he hH hJ G⟫_ℂ := by
        rw [integralConjugatePullback_inverse_left]
    _ = _ := LinearIsometry.inner_map_map _ _ _


-- @@ L112-125 verbatim
theorem kernelCorrespondenceL2_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F G : KernelQuotientL2) :
    ⟪F,kernelCorrespondenceL2 hHK hJK e g he G⟫_ℂ=
      ⟪kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) F,G⟫_ℂ := by
  change ⟪F,integralCoverTrace hHK globalKubotaKernel_le_levelThree
    (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))⟫_ℂ=_
  rw [integralCoverTrace_pairing,integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm


-- @@ L127-138 verbatim
theorem kernelCorrespondenceL2_adjoint {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    ContinuousLinearMap.adjoint (kernelCorrespondenceL2 hHK hJK e g he)=
      kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact kernelCorrespondenceL2_pairing hHK hJK e g he F G


-- @@ L140-140 verbatim
end


-- @@ L142-142 verbatim
section

-- @@ L143-143 verbatim
open Filter MeasureTheory

-- @@ L144-144 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L146-146 verbatim
section


-- @@ L148-165 verbatim
lemma continuous_period_integral {X:Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f:X→ℂ→ℂ) (hf:Continuous f.uncurry) :
    Continuous (fun x=>∫z in periodDomain,f x z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U,hUc,hUn⟩:=exists_compact_mem_nhds x0
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(hUc.prod (isCompact_closedBall (0:ℂ) radius)).bddAbove_image hf.norm.continuousOn
  apply continuousAt_of_dominated
  · filter_upwards with x using (show Continuous (f x) from hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
    apply hC
    exact ⟨(x,z),⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz⟩,rfl⟩
  · let:=periodDomain_finiteMeasure
    exact integrable_const C
  · filter_upwards with z using (show Continuous (fun x=>f x z) from hf.comp (continuous_id.prodMk continuous_const)).continuousAt


-- @@ L167-168 verbatim
def continuousCuspSlice (f:HyperbolicSpace→ℂ) (freq:ℂ) (v:ℝ) :ℂ:=
  (∫z in periodDomain,f (cuspCoordinateLift (v,z))*ShortDraftTrace.breveE (-freq*z))/(v:ℂ)^3


-- @@ L170-187 verbatim
lemma continuousCuspSlice_integrable (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    IntegrableOn (continuousCuspSlice f freq) (Set.Icc a b) volume := by
  let g:HyperbolicSpace→ℂ:=fun w=>f w*arbitraryCuspWeightedPhase 1 freq w
  have hg:Continuous g:=hf.mul (arbitraryCuspWeightedPhase_continuous 1 freq)
  have hi:=cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hp:0<v:=ha.trans_le hv.1
  rw [integral_div,continuousCuspSlice]
  apply congrArg (fun c:ℂ=>c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only [g]
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)


-- @@ L189-210 verbatim
lemma continuousCuspSlice_continuousOn (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    ContinuousOn (continuousCuspSlice f freq) (Set.Icc a b) := by
  let coord:(ℝ × ℂ)→UpperCoordinates:=fun q=>⟨(q.2,max a q.1),ha.trans_le (le_max_left _ _)⟩
  have hc:Continuous coord:=by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (continuous_const.max continuous_fst)
  have hup:Continuous (fun q:(ℝ × ℂ)=>f (upperPoint q.2 (max a q.1) (ha.trans_le (le_max_left _ _)))):=
    hf.comp (continuous_upperCoordinates.comp hc)
  have he:Continuous (fun q:(ℝ × ℂ)=>ShortDraftTrace.breveE (-freq*q.2)):=by
    change Continuous (fun q:(ℝ × ℂ)=>Complex.exp (2*Real.pi*Complex.I*((-freq*q.2)+starRingEnd ℂ (-freq*q.2))))
    fun_prop
  have hi:=continuous_period_integral (fun v z=>f (upperPoint z (max a v) (ha.trans_le (le_max_left _ _)))*
      ShortDraftTrace.breveE (-freq*z)) (hup.mul he)
  have hnum:ContinuousOn (fun v:ℝ=>∫z in periodDomain,f (cuspCoordinateLift (v,z))*
      ShortDraftTrace.breveE (-freq*z)) (Set.Icc a b):=by
    apply hi.continuousOn.congr
    intro v hv
    have hp:0<v:=ha.trans_le hv.1
    simp only [max_eq_right hv.1,cuspCoordinateLift_positive v _ hp]
  exact hnum.div (Complex.continuous_ofReal.pow 3).continuousOn
    (fun v hv=>pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'))


-- @@ L212-232 verbatim
lemma continuousCuspSlice_test (f:HyperbolicSpace→ℂ) (hf:Continuous f) (freq:ℂ)
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,ρ v*continuousCuspSlice f freq v := by
  have hg:Continuous (fun w=>f w*arbitraryCuspWeightedPhase ρ freq w):=
    hf.mul (arbitraryCuspWeightedPhase_continuous ρ freq)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha _ hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hp:0<v:=ha.trans_le hv.1
  dsimp only
  rw [continuousCuspSlice,←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)


-- @@ L234-251 verbatim
theorem continuousCuspSlice_eq_of_tests (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (g:ℝ→ℂ)
    (hg:∀a b:ℝ,0<a→ContinuousOn g (Set.Icc a b))
    (ht:∀a b:ℝ,∀_ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
        ∫v in Set.Icc a b,ρ v*g v) (v:ℝ) (hv:0<v) :
    continuousCuspSlice f freq v=g v := by
  have ha:0<v/2:=half_pos hv
  have hab:v/2≠2*v:=by linarith
  have he:continuousCuspSlice f freq=ᵐ[volume.restrict (Set.Icc (v/2) (2*v))]g:=by
    apply interval_ae_eq_of_boundedContinuous_height_tests (v/2) (2*v) _ _
      (continuousCuspSlice_integrable f hf freq _ _ ha) ((hg _ _ ha).integrableOn_Icc)
    intro ρ
    rw [←continuousCuspSlice_test f hf freq _ _ ha ρ]
    exact ht _ _ ha ρ
  exact Measure.eqOn_Icc_of_ae_eq volume hab he
    (continuousCuspSlice_continuousOn f hf freq _ _ ha) (hg _ _ ha)
      (by constructor <;>linarith)


-- @@ L253-253 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L255-292 verbatim
theorem ramifiedSource_fourier_all_heights (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ramifiedArithmeticResidue side h hf*(v:ℂ)^(2/3:ℂ)*
        sourceFourierKernel (4/3) (ninthCuspFrequency h*v) := by
  let R:=ramifiedArithmeticResidue side h hf
  let g:ℝ→ℂ:=fun v=>R*(v:ℂ)^(-(4/3:ℂ)-1)*
    sourceFourierKernel (4/3) (ninthCuspFrequency h*v)
  have hg:∀a b:ℝ,0<a→ContinuousOn g (Set.Icc a b):=by
    intro a b ha x hx
    have hp:0<x:=ha.trans_le hx.1
    exact ((continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(4/3:ℂ)-1) (Or.inr hp.ne'))).mul
        ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
          ((Complex.continuous_ofReal.const_mul (ninthCuspFrequency h)).continuousAt))).continuousWithinAt
  have ht:∀a b:ℝ,∀ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
          ∫x in Set.Icc a b,ρ x*g x:=by
    intro a b ha ρ
    rw [ramifiedSource_height_residue_integral side h hf a b ha ρ,
      arbitraryIntervalWhittaker,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x=>by dsimp only [g,R];ring)
  have he:=continuousCuspSlice_eq_of_tests
    (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (ramifiedSourceFunction_continuous _)
    (ninthCuspFrequency h) g hg ht v hv
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only [continuousCuspSlice,g,R] at he
  simp only [cuspCoordinateLift_positive v _ hv,hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  convert he using 1 ;ring


-- @@ L294-294 verbatim
end


-- @@ L296-296 verbatim
section

-- @@ L297-297 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L299-311 verbatim
lemma continuous_period_fourier_bound (f:ℂ→ℂ) (hf:Continuous f) :
    ∃C:ℝ,0≤C∧∀freq:ℂ,‖∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z)‖≤C := by
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:ℂ) radius).bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 B*(volume.restrict periodDomain).real Set.univ,mul_nonneg (le_max_left _ _) (measureReal_nonneg),?_⟩
  intro freq
  let:=periodDomain_finiteMeasure
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
  rw [norm_mul,breveE_norm,mul_one]
  apply le_trans _ (le_max_right _ _)
  apply hB
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz,rfl⟩


-- @@ L313-353 verbatim
theorem continuous_fourier_bessel_subexponential (f:ℝ→ℂ→ℂ) (c:Eis→ℂ)
    (hf:∀v:ℝ,0<v→Continuous (f v))
    (hfour:∀v:ℝ,∀_hv:0<v,∀h:Eis,h≠0→
      (∫z in periodDomain,f v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*c h*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))
    (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖c h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let v:ℝ:=ε/(9*Real.pi)
  have hv:0<v:=div_pos hε (by positivity)
  let area:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea:0<‖area‖:=norm_pos_iff.mpr cusp_volume_ne_zero
  obtain ⟨B,hB,hbound⟩:=continuous_period_fourier_bound (f v) (hf v hv)
  let D:ℝ:=‖area‖*v*cubicBesselLowerConstant
  have hD:0<D:=mul_pos (mul_pos harea hv) cubicBesselLowerConstant_pos
  refine ⟨B/D,div_nonneg hB hD.le,?_⟩
  intro h hh
  have hx:0<4*Real.pi*‖cuspFrequency h‖*v:=by
    have hr:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hl: cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))≤
      ‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖:=by
    have hb:=(schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx).trans (Complex.re_le_norm _)
    convert hb using 1
    congr 2
    dsimp [v]
    field_simp

  have hb:=hbound (cuspFrequency h)
  rw [hfour v hv h hh,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hv.le] at hb
  have hm:‖c h‖*(D*Real.exp (-(ε*‖cuspFrequency h‖)))≤B:=by
    calc
      _ = (‖area‖*‖c h‖*v)*(cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))) := by dsimp [D];ring
      _ ≤ (‖area‖*‖c h‖*v)*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖ :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ B := hb
  have hexp:0<Real.exp (-(ε*‖cuspFrequency h‖)):=Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD hexp)).mpr at hm
  calc
    _ ≤ B/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hm
    _ = (B/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg];field_simp


-- @@ L355-371 verbatim
theorem continuous_periodic_eq_bessel (c:SubexponentialBesselCoefficients)
    (f:ℂ→ℂ) (hf:Continuous f) (v:ℝ) (hv:0<v)
    (hp:∀n:Eis,∀z:ℂ,f (z+3*ConcreteTraceCRT.eisEmbedding n)=f z)
    (hfour:∀h:Eis,(∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c.amplitude v h) :
    ∀z:ℂ,f z=c.fullFunction 0 (upperPoint z v hv) := by
  have hc:=c.fullFunction_height_continuous 0 v hv
  have he:f=ᵐ[volume.restrict periodDomain](fun z=>c.fullFunction 0 (upperPoint z v hv)):=by
    apply periodDomain_L2_ext _ _ (periodDomain_memLp_of_continuous f hf)
      (periodDomain_memLp_of_continuous _ hc)
    intro h
    rw [hfour,c.fullFunction_fourier]
    by_cases hh:h=0
    · simp [hh,SubexponentialBesselCoefficients.amplitude]
    · simp [hh]
  have hall:=ae_eq_of_periodDomain_eq f _ hp (fun n z=>c.fullFunction_period 0 v hv z n) he
  exact congrFun (Measure.eq_of_ae_eq hall hf hc)


-- @@ L373-373 verbatim
end


-- @@ L375-375 verbatim
section

-- @@ L376-376 verbatim
open ConcreteTraceCRT

-- @@ L377-377 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L379-382 verbatim
lemma ninthCuspFrequency_three (h:Eis) :
    3*ninthCuspFrequency h=cuspFrequency h := by
  unfold ninthCuspFrequency cuspFrequency
  ring


-- @@ L384-398 verbatim
lemma sourceFourierKernel_cubic_amplitude (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    (v:ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  have he:=sourceFourierKernel_cubic_height h hh v hv
  rw [hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  calc
    _ = ((v:ℂ)^(2/3:ℂ)/(v:ℂ)^3)*sourceFourierKernel (4/3) (cuspFrequency h*v) := by ring
    _ = _ := he
    _ = _ := by field_simp


-- @@ L400-412 verbatim
lemma ramified_kernel_scaled_bessel (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    ((3*v:ℝ):ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (ninthCuspFrequency h*(3*v:ℝ))=
      (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hfreq:ninthCuspFrequency h*((3*v:ℝ):ℂ)=cuspFrequency h*v:=by
    push_cast
    rw [←ninthCuspFrequency_three]
    ring
  have hp:((3*v:ℝ):ℂ)^(2/3:ℂ)=(3:ℂ)^(2/3:ℂ)*(v:ℂ)^(2/3:ℂ):=by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a:=3) (b:=v) (by norm_num) hv.le (2/3:ℂ)
  rw [hfreq,hp,mul_assoc,sourceFourierKernel_cubic_amplitude h hh v hv]
  ring


-- @@ L414-414 verbatim
end


-- @@ L416-416 verbatim
section

-- @@ L417-417 verbatim
open ConcreteTraceCRT

-- @@ L418-418 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L420-421 verbatim
def ramifiedScaledRow (side:Bool) (v:ℝ) (z:ℂ) :ℂ:=
  ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (cuspCoordinateLift (3*v,3*z))


-- @@ L423-427 verbatim
def ramifiedBesselValue (side:Bool) (h:Eis) :ℂ:=
  if hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side) then
    (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  else 0


-- @@ L429-437 verbatim
lemma ramifiedScaledRow_continuous (side:Bool) (v:ℝ) (hv:0<v) :
    Continuous (ramifiedScaledRow side v) := by
  have hp:0<3*v:=by positivity
  have he:ramifiedScaledRow side v=(fun z=>ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (3*z) (3*v) hp)):=by
    funext z
    exact congrArg (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (cuspCoordinateLift_positive (3*v) (3*z) hp)
  rw [he]
  exact (ramifiedSource_height_continuous side (3*v) hp).comp (continuous_const.mul continuous_id)


-- @@ L439-444 verbatim
lemma ramifiedScaledRow_periodic (side:Bool) (v:ℝ) (hv:0<v) (n:Eis) (z:ℂ) :
    ramifiedScaledRow side v (z+3*eisEmbedding n)=ramifiedScaledRow side v z := by
  have hp:0<3*v:=by positivity
  have he:=ramifiedScaledMode_periodic side 0 (3*v) hp n z
  simpa only [ramifiedScaledMode,cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp] using he


-- @@ L446-452 verbatim
lemma ramifiedScaledRow_zero (side:Bool) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedScaledRow side v z)=0 := by
  have hp:0<3*v:=by positivity
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  cases side
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode10 (3*v) hp
  · simpa [ramifiedCuspRoot,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode19 (3*v) hp


-- @@ L454-474 verbatim
lemma ramifiedScaledRow_fourier (side:Bool) (v:ℝ) (hv:0<v) (h:Eis) :
    (∫z in periodDomain,ramifiedScaledRow side v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then 0 else ramifiedBesselValue side h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)) := by
  by_cases hh:h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,AddChar.map_zero_eq_one,
      mul_one]
    simpa only [ite_true,mul_zero] using ramifiedScaledRow_zero side v hv
  have hp:0<3*v:=by positivity
  rw [ite_eq_right hh]
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  by_cases hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)
  · rw [ramifiedSource_scaled_fourier_active side h hf (3*v) hp,
      ramifiedSource_fourier_all_heights side h hf (3*v) hp,
      ramifiedBesselValue,dite_eq_left hf,mul_assoc,ramified_kernel_scaled_bessel h hh v hv]
    field_simp [cusp_volume_ne_zero]

  · rw [ramifiedSource_scaled_fourier_off_support side h hf (3*v) hp,
      ramifiedBesselValue,dite_eq_right hf]
    ring


-- @@ L476-481 verbatim
lemma ramifiedBesselValue_subexponential (side:Bool) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖ramifiedBesselValue side h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  apply continuous_fourier_bessel_subexponential (ramifiedScaledRow side) (ramifiedBesselValue side)
    (ramifiedScaledRow_continuous side) _ ε hε
  intro v hv h hh
  simpa only [ite_eq_right hh,mul_assoc] using ramifiedScaledRow_fourier side v hv h


-- @@ L483-485 verbatim
def ramifiedBesselCoefficients (side:Bool) :SubexponentialBesselCoefficients where
  value:=ramifiedBesselValue side
  growth:=ramifiedBesselValue_subexponential side


-- @@ L487-493 verbatim
theorem ramifiedScaledRow_eq_bessel (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedScaledRow side v z=(ramifiedBesselCoefficients side).fullFunction 0 (upperPoint z v hv) := by
  apply continuous_periodic_eq_bessel (ramifiedBesselCoefficients side) (ramifiedScaledRow side v)
    (ramifiedScaledRow_continuous side v hv) v hv (ramifiedScaledRow_periodic side v hv) _ z
  intro h
  simpa only [SubexponentialBesselCoefficients.amplitude,ramifiedBesselCoefficients] using
    ramifiedScaledRow_fourier side v hv h


-- @@ L495-511 verbatim
theorem ramifiedSource_cubic_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀v:ℝ,∀hv:0<v,∀z:ℂ,a≤v→
      ‖ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).fullFunction_zero_cubic_decay
    (a/3) (by positivity)
  refine ⟨27*C,by positivity,?_⟩
  intro v hv z hav
  have hp:0<v/3:=by positivity
  have he:=ramifiedScaledRow_eq_bessel side (v/3) hp (z/3)
  have hb:=hbound (v/3) hp (z/3) (by linarith)
  rw [←he] at hb
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simp only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv] at hb
  calc
    _ ≤ C/(v/3)^3 := hb
    _ = 27*C/v^3 := by field_simp;ring


-- @@ L513-513 verbatim
end


-- @@ L515-515 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L517-520 verbatim
def ramifiedCuspBesselTerm (side:Bool) (h:Eis) (v:ℝ) (z:ℂ) :ℂ:=
  (if h=0 then 0 else ramifiedBesselValue side h*((v/3:ℝ):ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/3)))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*z)


-- @@ L522-529 verbatim
lemma ramifiedCuspBesselTerm_eq (side:Bool) (h:Eis) (v:ℝ) (hv:0<v) (z:ℂ) :
    (ramifiedBesselCoefficients side).term h (v/3,z/3)=ramifiedCuspBesselTerm side h v z := by
  rw [SubexponentialBesselCoefficients.term_eq_amplitude _ _ (by positivity)]
  have he:cuspFrequency h*(z/3)=ninthCuspFrequency h*z:=by
    rw [←ninthCuspFrequency_three]
    ring
  simp only [SubexponentialBesselCoefficients.amplitude,ramifiedBesselCoefficients,
    ramifiedCuspBesselTerm,he]


-- @@ L531-540 verbatim
lemma ramifiedSource_eq_series (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).series (v/3,z/3) := by
  have he:=ramifiedScaledRow_eq_bessel side (v/3) (by positivity) (z/3)
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simpa only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv,
    SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] using he


-- @@ L542-546 verbatim
theorem ramifiedSource_bessel (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      ∑'h:Eis,ramifiedCuspBesselTerm side h v z := by
  rw [ramifiedSource_eq_series,SubexponentialBesselCoefficients.series]
  exact tsum_congr (fun h=>ramifiedCuspBesselTerm_eq side h v hv z)


-- @@ L548-558 verbatim
theorem ramifiedSource_bessel_normal (side:Bool) (a b:ℝ) (ha:0<a) (hab:a≤b) :
    ∃g:Eis→ℝ,Summable g∧∀h:Eis,∀v:ℝ,v∈Set.Icc a b→∀z:ℂ,
      ‖ramifiedCuspBesselTerm side h v z‖≤g h := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).slab_bound (a/3) (b/3)
    (by positivity) (by linarith)
  refine ⟨fun h=>C*Real.exp (-(Real.pi*(a/3))*‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm (Real.pi*(a/3)) (by positivity)).mul_left C,?_⟩
  intro h v hv z
  have hp:0<v:=ha.trans_le hv.1
  rw [←ramifiedCuspBesselTerm_eq side h v hp z]
  exact hbound h (v/3,z/3) ⟨by dsimp only;linarith [hv.1],by dsimp only;linarith [hv.2]⟩


-- @@ L560-568 verbatim
theorem ramifiedSource_exponential_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀v:ℝ,∀hv:0<v,∀z:ℂ,a≤v→
      ‖ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)‖≤
        C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).series_cusp_decay (a/3) (by positivity)
  refine ⟨C,hC,?_⟩
  intro v hv z hav
  rw [ramifiedSource_eq_series]
  convert hbound (v/3) (z/3) (by linarith) using 1 ;ring_nf


-- @@ L570-570 verbatim
end


-- @@ L572-572 verbatim
open Filter MeasureTheory

-- @@ L573-573 verbatim
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace

-- @@ L574-574 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L576-582 verbatim
lemma coverGradientAt_add (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F+G) p=coverGradientAt F p+coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_add hF hG,WithLp.equiv_apply,WithLp.ofLp_add,
    Pi.add_apply,_root_.add_apply,mul_add]


-- @@ L584-590 verbatim
lemma coverGradientAt_sub (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F-G) p=coverGradientAt F p-coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_sub hF hG,WithLp.equiv_apply,WithLp.ofLp_sub,
    Pi.sub_apply,_root_.sub_apply,mul_sub]


-- @@ L592-598 verbatim
lemma coverGradientAt_smul (c : ℂ) (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    coverGradientAt (c•F) p=c•coverGradientAt F p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_const_smul hF,WithLp.equiv_apply,WithLp.ofLp_smul,
    Pi.smul_apply,_root_.smul_apply,smul_eq_mul,mul_left_comm]


-- @@ L600-601 verbatim
def coverDirichletPair (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  inner ℂ (coverGradientAt F p) (coverGradientAt G p)


-- @@ L603-619 verbatim
lemma coverDirichletPair_polarization (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverDirichletPair F G p=
      ((coverEnergyDensity (F+G) p:ℂ)-(coverEnergyDensity (F-G) p:ℂ)+
        ((coverEnergyDensity (F-Complex.I•G) p:ℂ)-
          (coverEnergyDensity (F+Complex.I•G) p:ℂ))*Complex.I)/4 := by
  unfold coverDirichletPair
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [RCLike.I_to_complex]
  rw [←coverGradientAt_add F G p hF hG,←coverGradientAt_sub F G p hF hG,
    ←coverGradientAt_smul Complex.I G p hG,
    ←coverGradientAt_sub F (Complex.I•G) p hF (hG.const_smul _),
    ←coverGradientAt_add F (Complex.I•G) p hF (hG.const_smul _)]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,
    coverGradientAt_norm_sq _ _ (hF.add hG),coverGradientAt_norm_sq _ _ (hF.sub hG),
    coverGradientAt_norm_sq _ _ (hF.sub (hG.const_smul _)),
    coverGradientAt_norm_sq _ _ (hF.add (hG.const_smul _))]


-- @@ L621-639 verbatim
lemma coverDirichletPair_comp (g : SL(2,ℂ)) (F G : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hG : DifferentiableAt ℝ G (euclideanAction g p)) :
    coverDirichletPair (F ∘ euclideanAction g) (G ∘ euclideanAction g) p=
      coverDirichletPair F G (euclideanAction g p) := by
  obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry g p hp
  rw [coverDirichletPair_polarization _ _ p (hF.comp p hder.differentiableAt)
    (hG.comp p hder.differentiableAt),coverDirichletPair_polarization F G _ hF hG]
  have ha : (F ∘ euclideanAction g)+(G ∘ euclideanAction g)=(F+G) ∘ euclideanAction g := rfl
  have hs : (F ∘ euclideanAction g)-(G ∘ euclideanAction g)=(F-G) ∘ euclideanAction g := rfl
  have hai : (F ∘ euclideanAction g)+Complex.I•(G ∘ euclideanAction g)=
      (F+Complex.I•G) ∘ euclideanAction g := rfl
  have hsi : (F ∘ euclideanAction g)-Complex.I•(G ∘ euclideanAction g)=
      (F-Complex.I•G) ∘ euclideanAction g := rfl
  rw [ha,hs,hai,hsi,coverEnergyDensity_comp g _ p hp (hF.add hG),
    coverEnergyDensity_comp g _ p hp (hF.sub hG),
    coverEnergyDensity_comp g _ p hp (hF.add (hG.const_smul _)),
    coverEnergyDensity_comp g _ p hp (hF.sub (hG.const_smul _))]


-- @@ L641-645 verbatim
lemma coverDirichletPair_sum_right {ι : Type*} (s : Finset ι)
    (F : EuclideanSpatial→ℂ) (G : ι→EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hG : ∀i∈s,DifferentiableAt ℝ (G i) p) :
    coverDirichletPair F (fun x=>∑i∈s,G i x) p=∑i∈s,coverDirichletPair F (G i) p := by
  simp only [coverDirichletPair,coverGradientAt_sum s G p hG,inner_sum]


-- @@ L647-653 verbatim
lemma coverDirichletPair_norm_le (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    ‖coverDirichletPair F G p‖≤(coverEnergyDensity F p+coverEnergyDensity G p)/2 := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (coverGradientAt F p) (coverGradientAt G p)
  have hs := sq_nonneg (‖coverGradientAt F p‖-‖coverGradientAt G p‖)
  rw [←coverGradientAt_norm_sq F p hF,←coverGradientAt_norm_sq G p hG]
  exact le_trans hh (by nlinarith)


-- @@ L655-659 verbatim
lemma kernelDirichletPairDensity_eq_cover (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f h (integralOrbitProjection globalKubotaKernel w)=
      coverDirichletPair (kernelTestField f) (kernelTestField h) (hyperbolicEuclideanCoordinates w) := by
  rw [kernelDirichletPairDensity_coordinate]
  rfl


-- @@ L661-661 verbatim
end CubicEisenstein


-- @@ L663-663 verbatim
end


-- @@ L665-665 verbatim
end OAI
