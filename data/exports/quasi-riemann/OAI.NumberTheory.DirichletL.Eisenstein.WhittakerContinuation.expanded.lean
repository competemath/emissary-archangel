import OAI.NumberTheory.DirichletL.Eisenstein.ScatteringCoefficients


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
open scoped BigOperators Classical Topology

-- @@ L81-81 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L83-83 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L85-90 verbatim
lemma cuspWhittakerHeightFactor_analyticAt (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWhittakerHeightFactor w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWhittakerAverage_differentiableAt (cuspFrequency h) w hw


-- @@ L92-98 verbatim
lemma kernelCuspFourierFamily_analyticAt_nonreal (h : ActualEisensteinCubic.O) (a b : ℝ)
    (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspFourierFamily h a b ha hab) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspFourier h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact a b ha hab s hs hi) rfl


-- @@ L100-102 verbatim
def continuedNonzeroScattering (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)


-- @@ L104-106 verbatim
def nonzeroScatteringResidue (h : ActualEisensteinCubic.O) : ℂ :=
  kernelCuspFourier h cubicEisensteinResidue /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)


-- @@ L108-111 verbatim
lemma continuedNonzeroScattering_meromorphicAt_center (h : ActualEisensteinCubic.O) :
    MeromorphicAt (continuedNonzeroScattering h) (4/3:ℂ) := by
  exact (kernelCuspFourierFamily_meromorphicAt h 2 3 (by norm_num) (by norm_num)).div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num))).meromorphicAt)


-- @@ L113-118 verbatim
lemma continuedNonzeroScattering_meromorphicOn_upper (h : ActualEisensteinCubic.O) :
    MeromorphicOn (continuedNonzeroScattering h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  intro s hs
  exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
    s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h s hs.1)).meromorphicAt)


-- @@ L120-135 verbatim
lemma continuedNonzeroScattering_residue_limit (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*continuedNonzeroScattering h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) := by
  have hden : Tendsto (fun s : ℂ => ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)) := (continuousAt_const.mul
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt).tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hlimit := (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).div hden
    (mul_ne_zero cusp_volume_ne_zero (cuspWhittakerHeightFactor_center_ne_zero h))
  change Tendsto (fun s : ℂ =>
      ((s-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s)/
        (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) at hlimit
  convert hlimit using 1
  funext s
  exact (mul_div_assoc _ _ _).symm


-- @@ L137-144 verbatim
lemma continuedNonzeroScattering_initial (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 4<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
    (by norm_num) (by norm_num) s (by linarith)
    (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)]
  field_simp [cusp_volume_ne_zero,hH]


-- @@ L146-156 verbatim
lemma cuspWhittakerHeightFactor_ne_zero_near_five (h : ActualEisensteinCubic.O) :
    ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re ∧ cuspWhittakerHeightFactor s h≠0 := by
  have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
  have hH : cuspWhittakerHeightFactor (5:ℂ) h≠0 := by
    intro he
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hre : ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hre.and ((cuspWhittakerHeightFactor_analyticAt h 5 (by norm_num)).continuousAt.eventually_ne hH)


-- @@ L158-186 verbatim
lemma kernelCuspFourierFamily_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h)
      {s : ℂ | 2<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 2<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (2:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)) domain := by
    intro s hs
    exact kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hright : AnalyticOnNhd ℂ
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (analyticAt_const.mul (scatteringCoefficient_analyticOnNhd h s hs.1)).mul
      (cuspWhittakerHeightFactor_analyticAt h s (by linarith [hs.1]))
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
      (by norm_num) (by norm_num) s (by linarith [hs.1])
      (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent


-- @@ L188-193 verbatim
lemma continuedNonzeroScattering_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 2<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_eq_upper h hh ⟨hs,hi⟩]
  field_simp [cusp_volume_ne_zero,hH]


-- @@ L195-211 verbatim
lemma continuedNonzeroScattering_initial_open (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ∃U : Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s : ℂ | 4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedNonzeroScattering h) (fun s => scatteringCoefficient s h) U := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five h)
  let z : ℂ := 5+(ε/2:ℝ)*Complex.I
  have hz : dist z (5:ℂ)<ε := by
    have hdist : dist z (5:ℂ)=ε/2 := by
      simp [z,dist_eq_norm,hε.le]
    rw [hdist]
    linarith
  have hzim : 0<z.im := by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s : ℂ | 0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedNonzeroScattering_initial h hh s (hball hs.1).1 hs.2 (hball hs.1).2


-- @@ L213-213 verbatim
end


-- @@ L215-215 verbatim
open Filter MeasureTheory

-- @@ L216-216 verbatim
open scoped BigOperators Classical Topology


-- @@ L218-225 verbatim
lemma weightedWhittakerIntegrand_integrable (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s p) whittakerProductVolume := by
  apply ((whittaker_bound_integrable s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq s)).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl) (norm_nonneg _) (norm_nonneg _))


-- @@ L227-253 verbatim
lemma weightedWhittakerProduct_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w p)
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w p)
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq w)).aestronglyMeasurable))
    (weightedWhittakerIntegrand_integrable ρ freq s hs)
    ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrandDeriv_continuous freq s)).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ => (whittakerIntegrand_hasDerivAt freq w p).const_mul (ρ p.1)))
  exact h.2.differentiableAt


-- @@ L255-270 verbatim
lemma weightedWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := weightedWhittakerIntegrand_integrable ρ freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [whittakerIntegrand_eq freq s v hv.1 z]
        ring)
    _ = _ := integral_const_mul _ _


-- @@ L272-279 verbatim
theorem cuspWeightedWhittakerAverage_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (weightedWhittakerProduct_eq_average ρ freq w hw).symm
  exact (weightedWhittakerProduct_differentiableAt ρ freq s hs).congr_of_eventuallyEq he


-- @@ L281-281 verbatim
section

-- @@ L282-282 verbatim
open Filter MeasureTheory

-- @@ L283-283 verbatim
open scoped BigOperators Classical Topology ENNReal


-- @@ L285-318 verbatim
theorem kernelCompact_projection_measure_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃N : ℕ,Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (N:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  choose e he heq using kernelQuotient_localHomeomorph
  have hcover : K⊆⋃w : HyperbolicSpace,(e w).source := by
    intro w _
    exact Set.mem_iUnion.mpr ⟨w,he w⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun w => (e w).source) (fun w => (e w).open_source) hcover
  have hinj (w : HyperbolicSpace) :
      Set.InjOn (integralOrbitProjection globalKubotaKernel) (e w).source := by
    rw [heq w]
    exact (e w).injOn
  refine ⟨t.card,Measure.le_iff.mpr ?_⟩
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.smul_apply]
  change hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ K)≤
    (t.card:ℝ≥0∞)*integralQuotientVolume globalKubotaKernel B
  calc
    _ ≤ hyperbolicVolume (⋃w∈t,(integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) := by
      apply measure_mono
      rintro w ⟨hw,hK⟩
      obtain ⟨v,hv,hwv⟩ := Set.mem_iUnion₂.mp (ht hK)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,hw,hwv⟩
    _ ≤ ∑w∈t,hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑_w∈t,integralQuotientVolume globalKubotaKernel B := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := kernelProjection_measurePreserving_on (e w).source (e w).open_source.measurableSet (hinj w)
      rw [←Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),
        ←Measure.map_apply (measurable_integralOrbitProjection _) hB,hm.map_eq]
      exact Measure.restrict_le_self B
    _ = _ := by simp [nsmul_eq_mul]


-- @@ L320-320 verbatim
section DominatedComplexL2

-- @@ L321-321 verbatim
variable {α : Type*} [MeasurableSpace α] {«μ» ν : Measure α} {c : ℝ≥0∞}


-- @@ L323-334 verbatim
def dominatedComplexL2 (hc : c≠⊤) (h : ν≤c•«μ») : Lp ℂ 2 «μ»→L[ℂ]Lp ℂ 2 ν where
  toFun := Lp.LpToLpOfMeasureLeSMul hc h
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hc h)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z•f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul hc h f),
      (Measure.absolutelyContinuous_of_le_smul h).ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,Pi.smul_apply] at *
    rw [h1,h3,h2,h4]
  cont := (Lp.LpToLpOfMeasureLeSMul hc h).continuous


-- @@ L336-338 verbatim
lemma dominatedComplexL2_ae (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    dominatedComplexL2 hc h f=ᵐ[ν]f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f


-- @@ L340-346 verbatim
lemma dominatedComplexL2_norm_le (hc : c≠⊤) (h : ν≤c•«μ») (f : Lp ℂ 2 «μ») :
    ‖dominatedComplexL2 hc h f‖≤c.toReal^((1:ℝ)/2)*‖f‖ := by
  have hb := (Lp.LpToLpOfMeasureLeSMul hc h : Lp ℂ 2 «μ»→L[ℝ]Lp ℂ 2 ν).le_opNorm f
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc h
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hn


-- @@ L348-348 verbatim
end DominatedComplexL2


-- @@ L350-351 verbatim
def kernelCompactMultiplicity (K : Set HyperbolicSpace) (hK : IsCompact K) : ℕ :=
  (kernelCompact_projection_measure_bound K hK).choose


-- @@ L353-356 verbatim
lemma kernelCompactMultiplicity_spec (K : Set HyperbolicSpace) (hK : IsCompact K) :
    Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (kernelCompactMultiplicity K hK:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel :=
  (kernelCompact_projection_measure_bound K hK).choose_spec


-- @@ L358-363 verbatim
def kernelCompactPullbackCLM (K : Set HyperbolicSpace) (hK : IsCompact K) :
    KernelQuotientL2→L[ℂ]Lp ℂ 2 (hyperbolicVolume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _,rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤)
        (kernelCompactMultiplicity_spec K hK))


-- @@ L365-375 verbatim
theorem kernelCompactPullbackCLM_ae (K : Set HyperbolicSpace) (hK : IsCompact K)
    (F : KernelQuotientL2) :
    kernelCompactPullbackCLM K hK F=ᵐ[hyperbolicVolume.restrict K]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict K)
      (Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)) :=
    ⟨measurable_integralOrbitProjection _,rfl⟩
  have he := dominatedComplexL2_ae
    (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤) (kernelCompactMultiplicity_spec K hK) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)


-- @@ L377-386 verbatim
lemma whittaker_bound_integrable_finite («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) («μ».prod volume) := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) «μ» := integrable_const _
  simpa only [one_mul] using hv.mul_prod hk


-- @@ L388-398 verbatim
lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))


-- @@ L400-430 verbatim
lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt


-- @@ L432-446 verbatim
lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]


-- @@ L448-473 verbatim
lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _


-- @@ L475-484 verbatim
theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm


-- @@ L486-486 verbatim
end


-- @@ L488-488 verbatim
open Filter MeasureTheory

-- @@ L489-489 verbatim
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

-- @@ L490-490 verbatim
open Finset AddChar MulChar EisensteinEmbedding


-- @@ L492-492 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L494-495 verbatim
def cuspWeightedFourierPhase (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*cuspFourierPhase h w


-- @@ L497-499 verbatim
lemma cuspWeightedFourierPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Continuous (cuspWeightedFourierPhase ρ h) :=
  (ρ.continuous.comp hyperbolicHeight_continuous).mul (cuspFourierPhase_continuous h)


-- @@ L501-504 verbatim
lemma cuspWeightedFourierPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) :
    ‖cuspWeightedFourierPhase ρ h w‖≤‖ρ‖ := by
  rw [cuspWeightedFourierPhase,norm_mul,cuspFourierPhase_norm,mul_one]
  exact ρ.norm_coe_le_norm _


-- @@ L506-510 verbatim
lemma cuspWeightedFourierTest_memLp (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)


-- @@ L512-513 verbatim
def cuspWeightedFourierTestL2 (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspWeightedFourierTest_memLp ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))


-- @@ L515-516 verbatim
def kernelCuspWeightedFourier (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspWeightedFourierTestL2 ρ h)).comp kernelCuspPullback


-- @@ L518-526 verbatim
lemma kernelCuspWeightedFourier_integral (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspWeightedFourierTestL2 ρ h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspWeightedFourierTest_memLp ρ h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspWeightedFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]


-- @@ L528-539 verbatim
lemma kernelCuspWeightedFourier_restrict (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspWeightedFourier ρ h F := by
  rw [kernelCuspWeightedFourier_integral,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))


-- @@ L541-544 verbatim
def kernelCuspWeightedFourierFamily (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspWeightedFourier ρ h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num) s)


-- @@ L546-550 verbatim
lemma kernelCuspWeightedFourierFamily_meromorphicAt (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MeromorphicAt (kernelCuspWeightedFourierFamily ρ h) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspWeightedFourier ρ h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num))


-- @@ L552-558 verbatim
lemma kernelCuspWeightedFourierFamily_analyticAt_nonreal (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspWeightedFourierFamily ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspWeightedFourier ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact 2 3 (by norm_num) (by norm_num) s hs hi) rfl


-- @@ L560-566 verbatim
lemma kernelCuspWeightedFourierFamily_residue_limit (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspWeightedFourierFamily ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspWeightedFourier ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspWeightedFourier ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspWeightedFourier_restrict,
    kernelCuspWeightedFourierFamily] using hh


-- @@ L568-581 verbatim
lemma kernelCuspWeightedFourierFamily_initial (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspWeightedFourierFamily,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (cubicEisensteinLocalFamily_initial_ae kernelCuspAverageCompact kernelCuspAverageCompact_isCompact s hs hi)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]


-- @@ L583-584 verbatim
def cuspWeightedWhittakerHeightFactor (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))


-- @@ L586-624 verbatim
lemma hyperbolicEisenstein_cusp_weighted_fourier_nonzero (ρ : BoundedContinuousFunction ℝ ℂ)
    (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  have hexp : ∀v∈Set.Icc (5:ℝ) 6,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,ite_eq_right hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc (5:ℝ) 6,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _


-- @@ L626-631 verbatim
lemma kernelCuspWeightedFourierFamily_initial_factor (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  rw [kernelCuspWeightedFourierFamily_initial ρ h s hs hi,
    hyperbolicEisenstein_cusp_weighted_fourier_nonzero ρ s (by linarith) h hh]


-- @@ L633-633 verbatim
end CubicEisenstein


-- @@ L635-635 verbatim
end


-- @@ L637-637 verbatim
end OAI
