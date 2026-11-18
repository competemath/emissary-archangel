import OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting
import OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants


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


-- @@ L74-74 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L75-75 verbatim
namespace CanonicalQuadraticSieve

-- @@ L76-76 verbatim
open ActualEisensteinCubic IdealCoprimeSieveOperator


-- @@ L78-114 verbatim
theorem poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : 259*η≤ρ := by
    have hh : η≤ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1≤M*X := by nlinarith
  have hshape : 0≤poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape


-- @@ L116-116 verbatim
end CanonicalQuadraticSieve


-- @@ L118-118 verbatim
open Filter MeasureTheory

-- @@ L119-119 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise


-- @@ L121-121 verbatim
namespace CubicEisenstein


-- @@ L123-130 verbatim
lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'


-- @@ L132-133 verbatim
lemma matrixCross_eq_gram (g : SL(2,ℂ)) : matrixCross g=matrixGram g 0 1 := by
  simp only [matrixCross,matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]


-- @@ L135-140 verbatim
lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  change matrixGram (upperSection z v hv) 0 1=_
  rw [←matrixCross_eq_gram]
  have hh := matrixCross_upperSection (1:SL(2,ℂ)) z v hv
  simpa [Matrix.one_apply] using hh


-- @@ L142-143 verbatim
def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)


-- @@ L145-148 verbatim
lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)


-- @@ L150-153 verbatim
@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')


-- @@ L155-156 verbatim
def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩


-- @@ L158-159 verbatim
lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _


-- @@ L161-165 verbatim
lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)


-- @@ L167-172 verbatim
lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)


-- @@ L174-180 verbatim
def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous


-- @@ L182-192 verbatim
lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩


-- @@ L194-194 verbatim
open Filter MeasureTheory

-- @@ L195-195 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal


-- @@ L197-199 verbatim
def spatialHeightSplit : EuclideanSpatial ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)


-- @@ L201-201 verbatim
lemma spatialHeightSplit_fst (p : EuclideanSpatial) : (spatialHeightSplit p).1=p 2 := rfl

-- @@ L202-202 verbatim
lemma spatialHeightSplit_snd_zero (p : EuclideanSpatial) : (spatialHeightSplit p).2 0=p 0 := rfl

-- @@ L203-203 verbatim
lemma spatialHeightSplit_snd_one (p : EuclideanSpatial) : (spatialHeightSplit p).2 1=p 1 := rfl


-- @@ L205-207 verbatim
lemma spatialHeightSplit_preserves_volume : MeasurePreserving spatialHeightSplit volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))


-- @@ L209-209 verbatim
def horizontalUnitBox : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1) 1)

-- @@ L210-211 verbatim
lemma horizontalUnitBox_measurable : MeasurableSet horizontalUnitBox :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)

-- @@ L212-214 verbatim
lemma horizontalUnitBox_volume : volume horizontalUnitBox=4 := by
  rw [horizontalUnitBox,volume_pi_pi]
  norm_num


-- @@ L216-217 verbatim
def euclideanCuspBox (a : ℝ) : Set EuclideanSpatial :=
  spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox)

-- @@ L218-219 verbatim
lemma euclideanCuspBox_measurable (a : ℝ) : MeasurableSet (euclideanCuspBox a) :=
  spatialHeightSplit.measurable (measurableSet_Ioi.prod horizontalUnitBox_measurable)

-- @@ L220-222 verbatim
lemma euclideanCuspBox_positive (a : ℝ) (ha : 0≤a) : euclideanCuspBox a ⊆ euclideanUpperHalf := by
  intro p hp
  exact ha.trans_lt hp.1


-- @@ L224-241 verbatim
theorem euclideanCuspBox_volume (a : ℝ) (ha : 0<a) :
    hyperbolicEuclideanVolume (euclideanCuspBox a)=4*ENNReal.ofReal (1/(2*a^2)) := by
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (euclideanCuspBox_measurable a),
    Measure.restrict_restrict (euclideanCuspBox_measurable a),
    Set.inter_eq_left.mpr (euclideanCuspBox_positive a ha.le)]
  change (∫⁻p in spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox),
    ENNReal.ofReal (((spatialHeightSplit p).1^3)⁻¹))=_
  rw [spatialHeightSplit_preserves_volume.setLIntegral_comp_preimage
    (f := fun q : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal ((q.1^3)⁻¹))
    (measurableSet_Ioi.prod horizontalUnitBox_measurable) (by fun_prop)]
  change (∫⁻q : ℝ × (Fin 2 → ℝ) in Set.Ioi a ×ˢ horizontalUnitBox,
    ENNReal.ofReal ((q.1^3)⁻¹) ∂((volume : Measure ℝ).prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    horizontalUnitBox_volume]
  rw [lintegral_mul_const _ (by fun_prop),cusp_height_volume a ha]
  exact mul_comm _ _


-- @@ L243-243 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L245-246 verbatim
instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩

-- @@ L247-250 verbatim
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he


-- @@ L252-253 verbatim
def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}


-- @@ L255-257 verbatim
lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet


-- @@ L259-276 verbatim
lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  rw [Set.mem_preimage,euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh


-- @@ L278-280 verbatim
lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)


-- @@ L282-310 verbatim
theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha


-- @@ L312-315 verbatim
lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp


-- @@ L317-319 verbatim
theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩


-- @@ L321-323 verbatim
instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree


-- @@ L325-325 verbatim
end CubicEisenstein


-- @@ L327-327 verbatim
namespace CanonicalQuadraticSieve


-- @@ L329-329 verbatim
section


-- @@ L331-339 verbatim
theorem improved_threshold_ge_column (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N≤M := by
  have hp : 1≤2-1/α := by
    have hh : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα
    linarith
  calc
    N = N^(1:ℝ) := (Real.rpow_one N).symm
    _ ≤ N^(2-1/α) := Real.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ M := hM


-- @@ L341-346 verbatim
theorem improved_threshold_power (α N M : ℝ) (hα : 0<α) (hN : 0<N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)≤M^α := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hM hα.le
  rw [←Real.rpow_mul hN.le] at hh
  have he : (2-1/α)*α=2*α-1 := by field_simp
  rwa [he] at hh


-- @@ L348-355 verbatim
theorem improved_threshold_main (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)*M^(1-α)≤M := by
  have hNM := improved_threshold_ge_column α N M hα hN hM
  have hM0 : 0<M := by linarith
  have hh := improved_threshold_power α N M (by linarith) (by linarith) hM
  calc
    _ ≤ M^α*M^(1-α) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hM0.le _)
    _ = M := by rw [←Real.rpow_add hM0]; simp


-- @@ L357-360 verbatim
theorem improved_threshold_shape (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : M+N+N^(2*α-1)*M^(1-α)≤3*M := by
  linarith [improved_threshold_main α N M hα hN hM,
    improved_threshold_ge_column α N M hα hN hM]


-- @@ L362-369 verbatim
theorem improved_threshold_reciprocal (α N M : ℝ) (_hα : 0<α) (hN : 0<N) (hM0 : 0<M)
    (hM : N^(2-1/α)≤M) : N^2/M≤N^(1/α) := by
  apply (div_le_iff₀ hM0).mpr
  have he : N^2=N^(2-1/α)*N^(1/α) := by
    rw [←Real.rpow_add hN]
    convert (Real.rpow_two N).symm using 1 ; ring_nf
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hN.le (1/α))


-- @@ L371-388 verbatim
theorem improved_threshold_low (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C^α*(M*N)^(η*α)*N := by
  have hk : selectedPoissonK C M N η≤C*(M*N)^η*N^(1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0≤selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N)^η*N^(1/α))^α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤C*(M*N)^η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0≤M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]


-- @@ L390-402 verbatim
theorem sieveNorm_large_rows (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hlarge : N^2≤M) :
    sieveNorm M N≤5*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤2*N := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤N)
    linarith
  have hsq : (⌈N⌉₊:ℝ)^2≤4*M := by
    calc
      _ ≤ (2*N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4*N^2 := by ring
      _ ≤ 4*M := by linarith
  have hh := sieveNorm_initial M N hM hN
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  nlinarith


-- @@ L404-455 verbatim
theorem hasSieveExponent_of_threshold_band (β : ℝ) (_hβ1 : 1≤β) (hβ2 : β≤2)
    (hband : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^β≤M → M≤N^2 → sieveNorm M N≤C*(M*N)^ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0<ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hpow : 1≤(M*N)^ε := Real.one_le_rpow hMN hε.le
  have hNb : 0≤N^β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N^2≤M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N)^ε*(M+N^β) := by gcongr <;> linarith
  · let R := max M (N^β)
    have hNβsq : N^β≤N^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1≤R := hM.trans (le_max_left _ _)
    have hRM : M≤R := le_max_left _ _
    have hRN : N^β≤R := le_max_right _ _
    have hRsq : R≤N^2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1≤N^2 := one_le_pow₀ hN
    have hM3 : M≤M^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ)≤3 by decide)
    have hRN2 : R≤M*N^2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N≤(M*N)^3 := by
      calc
        _ ≤ (M*N^2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N^3 := by ring
        _ ≤ M^3*N^3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N)^(ε/3)≤(M*N)^ε := by
      calc
        _ ≤ ((M*N)^3)^(ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0≤M*N)]
          congr 1
          ring
    have hRadd : R≤M+N^β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))


-- @@ L457-457 verbatim
open ActualEisensteinCubic CompletedGauss


-- @@ L459-541 verbatim
theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1≤β) (hβ2 : β≤2)
    (hshell : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M X : ℝ,
      1≤M → 1≤X → X^β≤M → ∀a : idealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a≤C*(M*X)^ρ*M*∑J,‖a J‖^2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0<ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0<lengthScale := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8^(ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hprod : 0<M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ)^j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ)^j.val) (a' j) ≤
        (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
    let X := (2:ℝ)^j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0≤β := by linarith
    have hXpow : X^β≤4*M := by
      calc
        _ ≤ (2*N)^β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2^β*N^β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N^β := by
          have ht : (2:ℝ)^β≤4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ)≤2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X)^(ε/2)≤8^(ε/2)*(M*N)^(ε/2) := by
      calc
        _ ≤ (8*(M*N))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M≤4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8^(ε/2)*(M*N)^(ε/2))*(4*M)*∑J,‖a' j J‖^2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖^2)=∑J,‖a J‖^2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ)≤lengthScale*(M*N)^(ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N^(ε/2)≤lengthScale*(M*N)^(ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a≤_
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N)^(ε/2))*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by gcongr
    _ = _ := by
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2)=(M*N)^ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8^(ε/2)*lengthScale)*((M*N)^(ε/2)*(M*N)^(ε/2))*M*(∑J,‖a J‖^2) := by ring
        _ = _ := by rw [hp]


-- @@ L543-543 verbatim
end


-- @@ L545-545 verbatim
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy


-- @@ L547-547 verbatim
def fixedBadNorm : ℝ := Ideal.absNorm (∏P∈fixedBadPrimes,P)

-- @@ L548-548 verbatim
def fixedCutoffBase : ℝ := max 4 fixedBadNorm


-- @@ L550-561 verbatim
theorem fixedBadNorm_one_le : 1≤fixedBadNorm := by
  have h1 : Admissible (1 : Ideal O) := by
    refine ⟨one_ne_zero, isUnit_one.squarefree, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  have he := commonMaskIdeal_eq_fixed_mul (1 : Ideal O) h1
  rw [mul_one] at he
  have hn : (∏P∈fixedBadPrimes,P)≠0 := by
    rw [←he]
    exact (commonMaskIdeal_squarefree 1).ne_zero
  unfold fixedBadNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))


-- @@ L563-564 verbatim
theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩


-- @@ L566-663 verbatim
theorem HasSieveExponent.annular_selected_bound {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring


-- @@ L665-665 verbatim
end CanonicalQuadraticSieve


-- @@ L667-667 verbatim
end


-- @@ L669-669 verbatim
end OAI
