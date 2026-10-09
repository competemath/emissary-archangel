import OAI.MeasureTheory.SelfSimilar.Clipping


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uι


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open scoped BigOperators ENNReal

-- @@ L9-9 verbatim
open MeasureTheory

-- @@ L10-10 verbatim
open MeasureTheory Metric Set Filter

-- @@ L11-11 verbatim
open scoped Topology ENNReal

-- @@ L12-12 verbatim
open MeasureTheory Filter Set ProbabilityTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
open MeasureTheory Metric Set Filter

-- @@ L15-15 verbatim
open scoped ENNReal Topology

-- @@ L16-16 verbatim
open MeasureTheory Filter Set

-- @@ L17-17 verbatim
open scoped Topology BigOperators

-- @@ L18-18 verbatim
namespace EntropyRateDimension.Coding

-- @@ L19-19 verbatim
open MeasureTheory Metric Set Filter

-- @@ L20-20 verbatim
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux

-- @@ L21-21 verbatim
open scoped Topology BigOperators

-- @@ L22-22 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L23-23 verbatim
local instance : MeasurableSpace ι := ⊤

-- @@ L24-24 verbatim
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩


-- @@ L26-27 verbatim
noncomputable def clippedCorr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corr S n ω))

-- @@ L28-29 verbatim
noncomputable def clippedLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corrLimit S ω))


-- @@ L31-32 verbatim
theorem clippedCorr_measurable (S : System ι) (n : ℕ) : Measurable (clippedCorr S n) :=
  measurable_const.max ((envelope_measurable S).min (corr_measurable S n))

-- @@ L33-34 verbatim
theorem clippedLimit_measurable (S : System ι) : Measurable (clippedLimit S) :=
  measurable_const.max ((envelope_measurable S).min (corrLimit_measurable S))


-- @@ L36-39 verbatim
omit [Nonempty ι] in
theorem clip_bound {E x : ℝ} (hE : 0 ≤ E) : |max 0 (min E x)| ≤ E := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le hE (min_le_left _ _)


-- @@ L41-43 verbatim
omit [Nonempty ι] in
theorem clippedCorr_bound (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    |clippedCorr S n ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)

-- @@ L44-46 verbatim
omit [Nonempty ι] in
theorem clippedLimit_bound (S : System ι) (ω : ℕ → ι) :
    |clippedLimit S ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)


-- @@ L48-51 verbatim
theorem ae_clipped_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => clippedCorr S n ω) atTop (𝓝 (clippedLimit S ω)) := by
  filter_upwards [ae_corr_limit S] with ω hω
  exact tendsto_const_nhds.max (tendsto_const_nhds.min hω)


-- @@ L53-74 verbatim
theorem ae_corr_triangle (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) / (n : ℝ))
      atTop (𝓝 (∫ ω, clippedLimit S ω ∂addressMeasure S)) := by
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have ht := ae_tendsto_triangle hT (clippedCorr_measurable S) (clippedLimit_measurable S)
    (envelope_measurable S) (clippedCorr_bound S) (clippedLimit_bound S)
    (envelope_integrable S) (ae_clipped_limit S)
  have ha : ∀ᵐ ω ∂addressMeasure S, ∀ j : ℕ, ∀ n : ℕ, 0 < n →
      0 ≤ corr S n (shift^[j] ω) ∧ corr S n (shift^[j] ω) ≤ envelope S (shift^[j] ω) := by
    apply ae_all_iff.mpr
    intro j
    exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae (ae_corr_bounds S)
  filter_upwards [ht,ha] with ω hω hbound
  convert hω using 1
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : 0 < n-j := by have := Finset.mem_range.mp hj; omega
  obtain ⟨h0,h1⟩ := hbound j (n-j) hjn
  simp only [clippedCorr,min_eq_right h1,max_eq_right h0]


-- @@ L76-76 verbatim
noncomputable def weightObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log (S.weight (ω 0))

-- @@ L77-77 verbatim
noncomputable def contractionObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log |S.ratio (ω 0)|


-- @@ L79-80 verbatim
noncomputable def prefixInfo (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.information (law S) (point S ω) |slope S ω n|


-- @@ L82-91 verbatim
theorem prefixInfo_succ (S : System ι) (n : ℕ) (ω : ℕ → ι)
    (hω : point S (shift ω) ∈ (law S).support) :
    prefixInfo S (n+1) ω = prefixInfo S n (shift ω) + weightObs S ω - corr S (n+1) ω := by
  have he := BallRatios.information_component S (law S) (law_selfSimilar S) (ω 0)
    hω (abs_slope_pos S (shift ω) n)
  have hs : |slope S ω (n+1)| = |S.ratio (ω 0)| * |slope S (shift ω) n| := by
    rw [slope_shift,abs_mul]
  unfold prefixInfo weightObs corr
  rw [point_shift S ω,hs]
  exact he


-- @@ L93-100 verbatim
omit [Nonempty ι] in
theorem triangle_succ (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    (∑ j ∈ Finset.range (n+1), corr S (n+1-j) (shift^[j] ω)) =
      corr S (n+1) ω + ∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] (shift ω)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right,Function.iterate_succ_apply,Function.iterate_zero_apply,
    Nat.sub_zero]
  ring


-- @@ L102-116 verbatim
theorem prefixInfo_telescope (S : System ι) (ω : ℕ → ι)
    (hω : ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support) (n : ℕ) :
    prefixInfo S n ω = birkhoffSum shift (weightObs S) n ω -
      (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) +
      BallRatios.information (law S) (point S (shift^[n] ω)) 1 := by
  induction n generalizing ω with
  | zero => simp [prefixInfo,slope_zero,birkhoffSum]
  | succ n ih =>
    have htail : ∀ j : ℕ, point S (shift^[j] (shift ω)) ∈ (law S).support := by
      intro j
      simpa only [Function.iterate_succ_apply] using hω (j+1)
    rw [prefixInfo_succ S n ω (by simpa using hω 1),ih (shift ω) htail,
      triangle_succ,birkhoffSum_succ_apply']
    simp only [Function.iterate_succ_apply]
    ring


-- @@ L118-126 verbatim
omit [Nonempty ι] in
theorem head_integrable (S : System ι) (f : ι → ℝ) :
    Integrable (fun ω : ℕ → ι => f (ω 0)) (addressMeasure S) := by
  classical
  apply Integrable.of_bound ((measurable_of_finite f).comp (measurable_pi_apply 0)).aestronglyMeasurable
    (∑ i, |f i|)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ (ω 0))


-- @@ L128-139 verbatim
omit [Nonempty ι] in
theorem head_integral (S : System ι) (f : ι → ℝ) :
    (∫ ω, f (ω 0) ∂addressMeasure S) = ∑ i, S.weight i * f i := by
  have he : (addressMeasure S).map (fun ω => ω 0) = symbolMeasure S :=
    Measure.infinitePi_map_eval _ _
  have hm := measurable_of_finite f
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable,he]
  unfold symbolMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (show Integrable f (Measure.dirac i) from Integrable.of_finite).smul_measure (by simp))]
  simp only [integral_smul_measure,integral_dirac,smul_eq_mul,
    ENNReal.toReal_ofReal (S.weight_nonneg _)]


-- @@ L141-148 verbatim
theorem ae_point_support (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support := by
  apply ae_all_iff.mpr
  intro j
  have ha : ∀ᵐ ω ∂addressMeasure S, point S ω ∈ (law S).support :=
    ae_of_ae_map (point_measurable S).aemeasurable (law S).support_mem_ae
  exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae ha


-- @@ L150-153 verbatim
theorem law_support_compact (S : System ι) : IsCompact (law S).support := by
  obtain ⟨B,_,hB⟩ := S.selfSimilar_compact (law S) (law_selfSimilar S)
  exact isCompact_Icc.of_isClosed_subset (law S).isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc hB)


-- @@ L155-156 verbatim
noncomputable def infoRate (S : System ι) : ℝ :=
  (∫ ω, weightObs S ω ∂addressMeasure S) - (∫ ω, clippedLimit S ω ∂addressMeasure S)


-- @@ L158-177 verbatim
theorem ae_prefixInfo_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / (n : ℝ)) atTop (𝓝 (infoRate S)) := by
  obtain ⟨C,hC,hCb⟩ := BallRatios.information_one_bound (law S) (law_support_compact S)
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have hb := ae_tendsto_average hT
    ((measurable_of_finite (fun i => -Real.log (S.weight i))).comp (measurable_pi_apply 0))
    (head_integrable S (fun i => -Real.log (S.weight i)))
  filter_upwards [hb,ae_corr_triangle S,ae_point_support S] with ω hweight hcorr hsupp
  have hend : Tendsto (fun n => BallRatios.information (law S)
      (point S (shift^[n] ω)) 1 / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => div_nonneg (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))
      (fun n => div_le_div_of_nonneg_right (hCb _ (hsupp n)) (Nat.cast_nonneg n))
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hweight.sub hcorr).add hend
  convert hh using 1
  · funext n
    rw [prefixInfo_telescope S ω hsupp,add_div,sub_div]
    rfl
  · simp only [infoRate,weightObs,add_zero,Function.comp_def]


-- @@ L179-179 verbatim
end EntropyRateDimension.Coding


-- @@ L181-181 verbatim
end


-- @@ L183-183 verbatim
end OAI
