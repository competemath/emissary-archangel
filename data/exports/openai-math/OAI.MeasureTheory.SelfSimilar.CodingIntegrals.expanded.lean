import OAI.MeasureTheory.SelfSimilar.BallIntegrability


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
namespace EntropyRateDimension.Coding

-- @@ L17-17 verbatim
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli

-- @@ L18-18 verbatim
open scoped Topology BigOperators ENNReal

-- @@ L19-19 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

-- @@ L20-20 verbatim
local instance : MeasurableSpace ι := ⊤

-- @@ L21-21 verbatim
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩


-- @@ L23-25 verbatim
theorem head_point_measurable (S : System ι) :
    Measurable (fun ω : ℕ → ι => (ω 0,point S ω)) :=
  (measurable_pi_apply 0).prodMk (point_measurable S)


-- @@ L27-53 verbatim
theorem head_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S ω)) =
      ∑ i, (Measure.dirac i).prod (S.component (law S) i) := by
  classical
  let f : ι × ℝ → ι × ℝ := fun z => (z.1,S.affine z.1 z.2)
  have hf : Measurable f := by
    apply measurable_fst.prodMk
    exact (((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd).add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = fun ω => (ω 0,point S ω) := by
    funext ω
    exact Prod.ext rfl (point_shift S ω).symm
  rw [he] at hh
  rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.prod_smul_left,Measure.map_smul _ hf.aemeasurable,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left,System.component,Measure.prod_smul_right,
    Measure.dirac_prod,Measure.map_map measurable_prodMk_left (S.affine_continuous i).measurable]
  rfl


-- @@ L55-63 verbatim
theorem ae_head_point (S : System ι) {P : ι → ℝ → Prop}
    (hP : ∀ i, ∀ᵐ x ∂S.component (law S) i, P i x) :
    ∀ᵐ ω ∂addressMeasure S, P (ω 0) (point S ω) := by
  have hh : ∀ᵐ z ∂(addressMeasure S).map (fun ω => (ω 0,point S ω)), P z.1 z.2 := by
    rw [head_point_law,ae_finsetSum_measure_iff]
    intro i _
    rw [Measure.dirac_prod,(measurableEmbedding_prodMk_left i).ae_map_iff]
    exact hP i
  exact ae_of_ae_map (head_point_measurable S).aemeasurable hh


-- @@ L65-77 verbatim
theorem integrable_head_point (S : System ι) {f : ι → ℝ → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) (S.component (law S) i)) :
    Integrable (fun ω => f (ω 0) (point S ω)) (addressMeasure S) := by
  have hm : Measurable (fun z : ι × ℝ => f z.1 z.2) :=
    measurable_from_prod_countable_right hfm
  have hi : Integrable (fun z : ι × ℝ => f z.1 z.2)
      ((addressMeasure S).map (fun ω => (ω 0,point S ω))) := by
    rw [head_point_law,integrable_finsetSum_measure]
    intro i _
    rw [Measure.dirac_prod,integrable_map_measure hm.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    exact hf i
  exact hi.comp_measurable (head_point_measurable S)


-- @@ L79-80 verbatim
noncomputable def envelope (S : System ι) (ω : ℕ → ι) : ℝ :=
  BallRatios.logEnvelope (law S) (S.component (law S) (ω 0)) (point S ω)


-- @@ L82-86 verbatim
theorem envelope_joint_measurable (S : System ι) : Measurable (fun z : ι × ℝ =>
    BallRatios.logEnvelope (law S) (S.component (law S) z.1) z.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logEnvelope_measurable (law S) (S.component (law S) i)


-- @@ L88-91 verbatim
theorem envelope_measurable (S : System ι) : Measurable (envelope S) := by
  unfold envelope
  have hh := (envelope_joint_measurable S).comp (head_point_measurable S)
  exact hh


-- @@ L93-95 verbatim
omit [Nonempty ι] in
theorem envelope_nonneg (S : System ι) (ω : ℕ → ι) : 0 ≤ envelope S ω :=
  BallRatios.logEnvelope_nonneg _ _ _


-- @@ L97-99 verbatim
theorem envelope_integrable (S : System ι) : Integrable (envelope S) (addressMeasure S) :=
  integrable_head_point S (fun i => BallRatios.logEnvelope_measurable _ (S.component (law S) i))
    (fun i => BallRatios.logEnvelope_integrable _ (S.component (law S) i))


-- @@ L101-102 verbatim
noncomputable def corr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.logRatio (law S) (S.component (law S) (ω 0)) (point S ω) |slope S ω n|


-- @@ L104-105 verbatim
noncomputable def corrLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  Real.log ((law S).rnDeriv (S.component (law S) (ω 0)) (point S ω)).toReal


-- @@ L107-111 verbatim
theorem corr_joint_measurable (S : System ι) : Measurable (fun z : ι × (ℝ × ℝ) =>
    BallRatios.logRatio (law S) (S.component (law S) z.1) z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logRatio_measurable (law S) (S.component (law S) i)


-- @@ L113-117 verbatim
theorem corr_measurable (S : System ι) (n : ℕ) : Measurable (corr S n) := by
  unfold corr
  have hh := (corr_joint_measurable S).comp ((measurable_pi_apply 0).prodMk
    ((point_measurable S).prodMk (slope_measurable S n).abs))
  exact hh


-- @@ L119-125 verbatim
theorem corrLimit_measurable (S : System ι) : Measurable (corrLimit S) := by
  have hm : Measurable (fun z : ι × ℝ =>
      Real.log ((law S).rnDeriv (S.component (law S) z.1) z.2).toReal) := by
    apply measurable_from_prod_countable_right
    intro i
    exact ((law S).measurable_rnDeriv (S.component (law S) i)).ennreal_toReal.log
  exact hm.comp (head_point_measurable S)


-- @@ L127-132 verbatim
theorem ae_corr_bounds (S : System ι) : ∀ᵐ ω ∂addressMeasure S, ∀ n : ℕ, 0 < n →
    0 ≤ corr S n ω ∧ corr S n ω ≤ envelope S ω := by
  filter_upwards [ae_head_point S (fun i => BallRatios.logRatio_bounds _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  intro n hn
  exact hω _ (abs_slope_pos S ω n) (abs_slope_lt_one S ω hn)


-- @@ L134-140 verbatim
theorem ae_corr_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => corr S n ω) atTop (𝓝 (corrLimit S ω)) := by
  filter_upwards [ae_head_point S (fun i => BallRatios.ae_logRatio_limit _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  apply hω.2.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
    Eventually.of_forall (abs_slope_pos S ω)⟩


-- @@ L142-142 verbatim
end EntropyRateDimension.Coding


-- @@ L144-144 verbatim
end


-- @@ L146-146 verbatim
end OAI
