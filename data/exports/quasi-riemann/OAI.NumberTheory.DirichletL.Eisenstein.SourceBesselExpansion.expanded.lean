import OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums


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
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L82-82 verbatim
section

-- @@ L83-83 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L85-116 verbatim
lemma opposite_height_fourier_average (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
      cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
    cuspWeightedFourierPhase ρ h w
  have hg:Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*unramifiedCubicGaussSeries s (9*h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ) : oppositeEisenstein z v hv0 s*(ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ρ v*(oppositeEisenstein z v hv0 s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by ring
    simp_rw [he]
    rw [integral_const_mul,oppositeEisenstein_fourier v hv0 s hs h]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring


-- @@ L118-147 verbatim
lemma oppositeHeight_cross_identity (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    Set.EqOn (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*
      cuspWhittakerHeightFactor s h) domain := fun s hs=>
    (translatedHeightFamily_analyticAt a b ha ρ h oppositeSource s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspIntervalWhittakerHeightFactor a b ρ s h) domain := fun s hs=>
    (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedHeightFamily_initial a b ha ρ h oppositeSource s hs.1 hs.2,
      opposite_height_fourier_average a b ha ρ h s (by linarith [hs.1]),
      translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      opposite_cusp_fourier_average s (by linarith [hs.1])]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev


-- @@ L149-177 verbatim
theorem translatedHeightFourier_opposite_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hfixed := (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hvar := (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hl:=((translatedHeightFamily_residue_limit a b ha ρ h oppositeSource).mul hfixed).comp upperVertical_tendsto_cubic_punctured
  have hr:=((translatedCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)).mul hvar).comp
    upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedHeightFamily a b ha ρ h oppositeSource ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeHeight_cross_identity a b ha ρ h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      translatedCuspFourier h oppositeSource cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hev
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq,translatedCuspFourier_unramified_residue]
  ring


-- @@ L179-179 verbatim
end


-- @@ L181-181 verbatim
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT

-- @@ L182-182 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L184-218 verbatim
lemma rational_height_fourier_right_T (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip a b,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspWeightedFourierPhase ρ h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  change (∫w in cuspPeriodStrip a b,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha f hf.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha f hf),
    cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hslice : (∫z in periodDomain,f (cuspCoordinateLift (v,z)))=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫z in periodDomain,g (cuspCoordinateLift (v,z)) := by
    simp only [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    simpa only [mul_assoc] using period_integral_fourier_translation
      (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0)*ρ v)
      (fun m z=>congrArg (fun q:ℂ=>q*ρ v) (hyperbolicEisenstein_rational_periodic r m s hs z v hv0)) h (n:ℂ)
  dsimp only
  rw [hslice]
  ring


-- @@ L220-260 verbatim
lemma translatedHeightFourier_residue_scaled_of_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume) :
    translatedHeightFourier a b ha ρ h M cubicEisensteinResidue=
      c*translatedHeightFourier a b ha ρ h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedHeightFamily a b ha ρ h M
  let g : ℂ→ℂ := fun s=>c*translatedHeightFamily a b ha ρ h N s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedHeightFamily_analyticAt a b ha ρ h M s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedHeightFamily_analyticAt a b ha ρ h N s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedHeightFamily_initial a b ha ρ h M s hs.1 hs.2,
      translatedHeightFamily_initial a b ha ρ h N s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedHeightFamily_residue_limit a b ha ρ h M).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedHeightFamily_residue_limit a b ha ρ h N).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv


-- @@ L262-265 verbatim
lemma translatedHeightFourier_one (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h 1 F=kernelCuspHeightFourier a b ha ρ h F := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]


-- @@ L267-291 verbatim
lemma translatedHeightFourier_bruhat (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (e:Fin 2) (sector:Fin 3⊕(Fin 3×Fin 3)) :
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep (e,sector))) cubicEisensteinResidue=
      match sector with
      | Sum.inl _=>kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue := by
  cases sector with
  | inl index =>
    rw [←one_mul (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue),←translatedHeightFourier_one a b ha ρ h]
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_height_fourier_right_T a b ha ρ ModularGroup.S ab.2.val h s (by linarith)


-- @@ L293-307 verbatim
theorem kernelSourceProjection_height_fourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedHeightFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue)))=_
  ring


-- @@ L309-309 verbatim
end


-- @@ L311-311 verbatim
section

-- @@ L312-312 verbatim
open Filter MeasureTheory

-- @@ L313-313 verbatim
open scoped BigOperators Classical Topology


-- @@ L315-315 verbatim
section

-- @@ L316-316 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L318-328 verbatim
lemma cuspIntervalWhittakerHeightFactor_zero_center (a b:ℝ) (_ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) 0=
      (3*(Real.pi:ℂ))*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero (4/3) (by norm_num)]
  have he : -(4/3:ℂ)-1=-(7/3:ℂ) := by ring
  rw [he]
  ring


-- @@ L330-338 verbatim
lemma kernelCuspHeightFourier_principal_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds,cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    simp only [principalArithmeticResidue,ite_true]
    ring
  · simpa only [principalArithmeticResidue,ite_eq_right hh] using kernelCuspHeightFourier_residue_factor a b ha ρ h hh


-- @@ L340-344 verbatim
lemma principalArithmeticResidue_not_horizontal (h:Eis) (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    principalArithmeticResidue h=0 := by
  have h0:h≠0 := by intro he;subst h;simp [cuspFrequency] at hh
  rw [principalArithmeticResidue,ite_eq_right h0,nonzeroScatteringResidue,
    kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh,zero_div]


-- @@ L346-355 verbatim
theorem kernelSourceProjection_height_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  rw [kernelSourceProjection_height_fourier,kernelCuspHeightFourier_principal_residue,
    translatedHeightFourier_opposite_residue,sourceRayPhaseSum_eq,sourceArithmeticResidue]
  split_ifs with hh
  · field_simp [cusp_volume_ne_zero]

  · rw [principalArithmeticResidue_not_horizontal h hh]
    ring


-- @@ L357-357 verbatim
def sourceResidualFourierCoefficient (h:Eis) : ℂ := cubicBesselNormalizer h*sourceArithmeticResidue h


-- @@ L359-361 verbatim
def sourceResidualFullModeAmplitude (v:ℝ) (h:Eis) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else sourceResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)


-- @@ L363-367 verbatim
lemma sourceResidualFullModeAmplitude_zero_density (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  simpa [sourceResidualFullModeAmplitude,cubicResidualFullModeAmplitude] using
    cubicResidualFullModeAmplitude_zero_density v hv


-- @@ L369-374 verbatim
lemma sourceResidualFullModeAmplitude_nonzero_density (v:ℝ) (hv:0<v) (h:Eis) (hh:h≠0) :
    sourceResidualFullModeAmplitude v h/(v:ℂ)^3=sourceResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [sourceResidualFullModeAmplitude,ite_eq_right hh]
  have hv0:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp


-- @@ L376-383 verbatim
lemma kernelSourceProjection_height_bessel (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (hh:h≠0) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFourierCoefficient h*
        ∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [kernelSourceProjection_height_residue,cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,
    sourceResidualFourierCoefficient]
  ring


-- @@ L385-413 verbatim
theorem kernelSourceProjection_height_full (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  by_cases hh:h=0
  · subst h
    rw [kernelSourceProjection_height_residue,sourceArithmeticResidue_zero,
      cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelSourceProjection_height_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3))=
        sourceResidualFourierCoefficient h*∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring


-- @@ L415-415 verbatim
end


-- @@ L417-417 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L419-434 verbatim
lemma sourceResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖(kernelSourceProjection cubicEisensteinResidue)‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelSourceProjection_height_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h (kernelSourceProjection cubicEisensteinResidue)
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound


-- @@ L436-460 verbatim
lemma sourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := sourceResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (sourceResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp


-- @@ L462-464 verbatim
def sourceBesselCoefficients : SubexponentialBesselCoefficients where
  value := sourceResidualFourierCoefficient
  growth := sourceResidualFourierCoefficient_subexponential


-- @@ L466-467 verbatim
def sourceBesselFunction : HyperbolicSpace→ℂ :=
  sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)


-- @@ L469-470 verbatim
lemma sourceBesselFunction_continuous : Continuous sourceBesselFunction :=
  sourceBesselCoefficients.fullFunction_continuous _


-- @@ L472-479 verbatim
lemma sourceBesselFunction_fourier (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,sourceBesselFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [sourceBesselFunction,sourceBesselCoefficients.fullFunction_fourier]
  by_cases hh:h=0
  · simp [sourceResidualFullModeAmplitude,hh]
  · simp only [ite_eq_right hh,SubexponentialBesselCoefficients.amplitude,sourceResidualFullModeAmplitude]
    rfl


-- @@ L481-484 verbatim
lemma sourceBesselFunction_period (v:ℝ) (hv:0<v) (z:ℂ) (n:ActualEisensteinCubic.O) :
    sourceBesselFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      sourceBesselFunction (upperPoint z v hv) :=
  sourceBesselCoefficients.fullFunction_period _ v hv z n


-- @@ L486-488 verbatim
lemma sourceBesselFunction_height_memLp (v:ℝ) (hv:0<v) :
    MemLp (fun z:ℂ=>sourceBesselFunction (cuspCoordinateLift (v,z))) 2 (volume.restrict periodDomain) :=
  sourceBesselCoefficients.fullFunction_height_memLp _ v hv


-- @@ L490-490 verbatim
end


-- @@ L492-492 verbatim
open Filter MeasureTheory

-- @@ L493-493 verbatim
open scoped BigOperators Classical Topology


-- @@ L495-495 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L497-515 verbatim
lemma sourceResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => sourceResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (sourceResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm


-- @@ L517-527 verbatim
lemma projectedResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h (kernelSourceProjection cubicEisensteinResidue))
    ((sourceResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h (kernelSourceProjection cubicEisensteinResidue),
    kernelSourceProjection_height_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)


-- @@ L529-534 verbatim
lemma projectedResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => projectedResidue_slice_coefficient_ae a b ha h)


-- @@ L536-549 verbatim
lemma projectedResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        (kernelSourceProjection cubicEisensteinResidue) (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  filter_upwards [projectedResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he


-- @@ L551-564 verbatim
theorem projectedResidue_cell_slices_ae (a b:ℝ) (ha:0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z:ℂ=>kernelSourceProjection cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain] (fun z=>sourceBesselFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [projectedResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha (kernelSourceProjection cubicEisensteinResidue),
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos:0<v:=ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (sourceBesselFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using sourceBesselFunction_fourier v hpos h


-- @@ L566-575 verbatim
theorem sourceBesselFunction_represents_projection :
    (fun w=>kernelSourceProjection cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceBesselFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable (kernelSourceProjection cubicEisensteinResidue)).measurable.comp
      (measurable_integralOrbitProjection _)) sourceBesselFunction_continuous.measurable
  · intro v hv z n
    exact congrArg (kernelSourceProjection cubicEisensteinResidue) (kernelProjection_upper_period v hv z n)
  · exact sourceBesselFunction_period
  · exact projectedResidue_cell_slices_ae


-- @@ L577-582 verbatim
theorem cubicSourceResidualFunction_eq_bessel : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous


-- @@ L584-589 verbatim
theorem cubicSourceResidualFunction_fourier_full (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier v hv h


-- @@ L591-599 verbatim
theorem cubicSourceResidualFunction_bessel (v:ℝ) (hv:0<v) (z:ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv)=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+
      ∑'h:ActualEisensteinCubic.O,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    sourceBesselCoefficients.series_bessel v hv z]
  rfl


-- @@ L601-604 verbatim
theorem sourceResidual_series_uniform (a b:ℝ) (ha:0<a) (hab:a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑ h ∈ t, sourceBesselCoefficients.term h p)
      sourceBesselCoefficients.series atTop {p : ℝ × ℂ | p.1 ∈ Set.Icc a b} :=
  sourceBesselCoefficients.series_uniform a b ha hab


-- @@ L606-617 verbatim
theorem sourceResidual_bessel_normal (a b:ℝ) (ha:0<a) (hab:a≤b) :
    ∃g : ActualEisensteinCubic.O→ℝ, Summable g ∧ ∀(h:ActualEisensteinCubic.O)(v:ℝ),v∈Set.Icc a b→∀z:ℂ,
      ‖(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z)‖≤g h := by
  obtain ⟨C,hC,hbound⟩:=sourceBesselCoefficients.slab_bound a b ha hab
  refine ⟨fun h=>C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C,?_⟩
  intro h v hv z
  have he:=hbound h (v,z) hv
  rw [sourceBesselCoefficients.term_eq_amplitude v (ha.trans_le hv.1) h z] at he
  exact he


-- @@ L619-619 verbatim
end CubicEisenstein


-- @@ L621-621 verbatim
end


-- @@ L623-623 verbatim
end OAI
