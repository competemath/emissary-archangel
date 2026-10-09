import OAI.MeasureTheory.SelfSimilar.Bernoulli


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
namespace EntropyRateDimension

-- @@ L15-15 verbatim
namespace Coding

-- @@ L16-16 verbatim
open Filter Set

-- @@ L17-17 verbatim
open scoped Topology


-- @@ L19-19 verbatim
variable {ι : Type uι} [Fintype ι] [Nonempty ι]


-- @@ L21-21 verbatim
def shift (ω : ℕ → ι) (n : ℕ) : ι := ω (n+1)


-- @@ L23-24 verbatim
def slope (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, S.ratio (ω j)


-- @@ L26-27 verbatim
def term (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  slope S ω n * S.offset (ω n)


-- @@ L29-29 verbatim
noncomputable def point (S : System ι) (ω : ℕ → ι) : ℝ := ∑' n, term S ω n


-- @@ L31-32 verbatim
omit [Nonempty ι] in
theorem slope_zero (S : System ι) (ω : ℕ → ι) : slope S ω 0 = 1 := by simp [slope]


-- @@ L34-37 verbatim
omit [Nonempty ι] in
theorem slope_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = slope S ω n * S.ratio (ω n) := by
  simp [slope, Finset.prod_range_succ]


-- @@ L39-43 verbatim
omit [Nonempty ι] in
theorem slope_shift (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = S.ratio (ω 0) * slope S (shift ω) n := by
  simp only [slope, Finset.prod_range_succ', shift]
  ring


-- @@ L45-53 verbatim
omit [Nonempty ι] in
theorem abs_slope_le (S : System ι) (ω : ℕ → ι) {c : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c) (n : ℕ) :
    |slope S ω n| ≤ c^n := by
  induction n with
  | zero => simp [slope_zero]
  | succ n ih =>
    rw [slope_succ, abs_mul, pow_succ]
    exact mul_le_mul ih (hr _) (abs_nonneg _) (pow_nonneg hc _)


-- @@ L55-60 verbatim
omit [Nonempty ι] in
theorem abs_term_le (S : System ι) (ω : ℕ → ι) {c T : ℝ}
    (hc : 0 ≤ c) (_hT : 0 ≤ T) (hr : ∀ i, |S.ratio i| ≤ c)
    (ht : ∀ i, |S.offset i| ≤ T) (n : ℕ) : |term S ω n| ≤ c^n*T := by
  rw [term, abs_mul]
  exact mul_le_mul (abs_slope_le S ω hc hr n) (ht _) (abs_nonneg _) (pow_nonneg hc n)


-- @@ L62-66 verbatim
theorem term_summable (S : System ι) (ω : ℕ → ι) : Summable (term S ω) := by
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hc.le hc1).mul_right T)
  intro n
  simpa only [Real.norm_eq_abs] using abs_term_le S ω hc.le hT hr ht n


-- @@ L68-77 verbatim
theorem point_shift (S : System ι) (ω : ℕ → ι) :
    point S ω = S.affine (ω 0) (point S (shift ω)) := by
  rw [point, (term_summable S ω).tsum_eq_zero_add]
  have he : (fun n => term S ω (n+1)) = fun n => S.ratio (ω 0)*term S (shift ω) n := by
    funext n
    simp only [term, slope_shift, shift]
    ring
  rw [he, tsum_mul_left]
  simp only [term, slope_zero, one_mul, System.affine, point]
  ring


-- @@ L79-79 verbatim
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]


-- @@ L81-85 verbatim
omit [Nonempty ι] in
theorem slope_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => slope S ω n) := by
  apply Finset.measurable_prod
  intro j hj
  exact (measurable_of_finite _).comp (measurable_pi_apply j)


-- @@ L87-89 verbatim
omit [Nonempty ι] in
theorem term_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => term S ω n) :=
  (slope_measurable S n).mul ((measurable_of_finite _).comp (measurable_pi_apply n))


-- @@ L91-96 verbatim
theorem point_measurable (S : System ι) : Measurable (point S) := by
  apply measurable_of_tendsto_metrizable
    (fun n => Finset.measurable_sum (s := Finset.range n) (fun j _ => term_measurable S j))
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (term_summable S ω).hasSum.tendsto_sum_nat


-- @@ L98-99 verbatim
noncomputable def symbolMeasure (S : System ι) : Measure ι :=
  ∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i


-- @@ L101-106 verbatim
instance symbolMeasure_probability (S : System ι) : IsProbabilityMeasure (symbolMeasure S) where
  measure_univ := by
    simp only [symbolMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum]
    simp


-- @@ L108-109 verbatim
noncomputable def addressMeasure (S : System ι) : Measure (ℕ → ι) :=
  Measure.infinitePi fun _ : ℕ => symbolMeasure S


-- @@ L111-112 verbatim
instance addressMeasure_probability (S : System ι) : IsProbabilityMeasure (addressMeasure S) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => symbolMeasure S))


-- @@ L114-114 verbatim
noncomputable def law (S : System ι) : Measure ℝ := (addressMeasure S).map (point S)


-- @@ L116-117 verbatim
instance law_probability (S : System ι) : IsProbabilityMeasure (law S) :=
  (Measure.isProbabilityMeasure_map_iff (point_measurable S).aemeasurable).2 inferInstance


-- @@ L119-127 verbatim
theorem head_tail_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S (shift ω))) =
      (symbolMeasure S).prod (law S) := by
  have h := congrArg (Measure.map (Prod.map id (point S)))
    (Bernoulli.head_tail_law (symbolMeasure S))
  rw [Measure.map_map (measurable_id.prodMap (point_measurable S))
      ((measurable_pi_apply 0).prodMk Bernoulli.shift_measurable)] at h
  rw [← Measure.map_prod_map _ _ measurable_id (point_measurable S), Measure.map_id] at h
  exact h


-- @@ L129-152 verbatim
theorem law_selfSimilar (S : System ι) : S.SelfSimilar (law S) := by
  classical
  let f : ι × ℝ → ℝ := fun z => S.affine z.1 z.2
  have hf : Measurable f := by
    exact ((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd |>.add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp Bernoulli.shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = point S :=
    funext fun ω => (point_shift S ω).symm
  rw [he] at hh
  change law S = _ at hh
  change law S = _
  conv_lhs => rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul _ hf.aemeasurable, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl


-- @@ L154-154 verbatim
end Coding

-- @@ L155-155 verbatim
end EntropyRateDimension


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
