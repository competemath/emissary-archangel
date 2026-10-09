import OAI.Geometry.HarmonicGrowth.Curvature


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Filter MeasureTheory

-- @@ L7-7 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L8-8 verbatim
open Matrix

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Matrix

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Filter Matrix

-- @@ L13-13 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L14-14 verbatim
open Filter MeasureTheory

-- @@ L15-15 verbatim
open scoped Topology ContDiff


-- @@ L17-17 verbatim
namespace HarmonicCounterexample.Scale


-- @@ L19-21 verbatim
/-- The fixed cutoff is independent of all pulse data. It is zero already
on (-infty,5/2] and one on [7/2,infty), as allowed by geometry.tex. -/
def cutoff (t : ℝ) : ℝ := Real.smoothTransition (t - 5/2)


-- @@ L23-23 verbatim
def weight (t : ℝ) : ℝ := cutoff t * (1+t)^(-5/4:ℝ)


-- @@ L25-25 verbatim
def primitive (t : ℝ) : ℝ := ∫ u in (2:ℝ)..t, weight u


-- @@ L27-27 verbatim
def total : ℝ := primitive 4 + 4 * (5:ℝ)^(-1/4:ℝ)


-- @@ L29-29 verbatim
def profile (μ t : ℝ) : ℝ := Real.exp (-μ * primitive t)


-- @@ L31-31 verbatim
def slope (μ t : ℝ) : ℝ := -μ * weight t


-- @@ L33-34 verbatim
lemma cutoff_smooth : ContDiff ℝ ∞ cutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)


-- @@ L36-37 verbatim
lemma cutoff_zero {t : ℝ} (ht : t ≤ 5/2) : cutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)


-- @@ L39-40 verbatim
lemma cutoff_one {t : ℝ} (ht : 7/2 ≤ t) : cutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)


-- @@ L42-42 verbatim
lemma cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := Real.smoothTransition.nonneg _

-- @@ L43-43 verbatim
lemma cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := Real.smoothTransition.le_one _

-- @@ L44-45 verbatim
lemma cutoff_mono : Monotone cutoff :=
  fun _ _ h => Real.smoothTransition.monotone (sub_le_sub_right h _)


-- @@ L47-48 verbatim
lemma weight_zero {t : ℝ} (ht : t ≤ 5/2) : weight t = 0 := by
  rw [weight, cutoff_zero ht, zero_mul]


-- @@ L50-51 verbatim
lemma weight_tail {t : ℝ} (ht : 4 ≤ t) : weight t = (1+t)^(-5/4:ℝ) := by
  rw [weight, cutoff_one (by linarith), one_mul]


-- @@ L53-63 verbatim
lemma weight_smooth : ContDiff ℝ ∞ weight := by
  apply contDiff_iff_contDiffAt.2
  intro t
  by_cases ht : t < 5/2
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact weight_zero hu.le
  · apply cutoff_smooth.contDiffAt.mul
    apply (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne
    change 1+t ≠ 0
    linarith


-- @@ L65-68 verbatim
lemma weight_nonneg (t : ℝ) : 0 ≤ weight t := by
  by_cases ht : t ≤ 5/2
  · rw [weight_zero ht]
  · exact mul_nonneg (cutoff_nonneg t) (Real.rpow_nonneg (by linarith) _)


-- @@ L70-75 verbatim
lemma weight_le_one (t : ℝ) : weight t ≤ 1 := by
  by_cases ht : t ≤ 5/2
  · rw [weight_zero ht]; norm_num
  · apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith : 0 ≤ 1+t) _)
      (cutoff_le_one t)).trans
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)


-- @@ L77-80 verbatim
lemma primitive_hasDerivAt (t : ℝ) : HasDerivAt primitive (weight t) t :=
  intervalIntegral.integral_hasDerivAt_right (weight_smooth.continuous.intervalIntegrable 2 t)
    weight_smooth.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    weight_smooth.continuous.continuousAt


-- @@ L82-87 verbatim
lemma primitive_smooth : ContDiff ℝ ∞ primitive := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun t => (primitive_hasDerivAt t).differentiableAt, ?_⟩
  have hd : deriv primitive = weight := funext fun t => (primitive_hasDerivAt t).deriv
  rw [hd]
  exact weight_smooth


-- @@ L89-95 verbatim
lemma primitive_zero {t : ℝ} (ht : t ≤ 2) : primitive t = 0 := by
  unfold primitive
  calc
    _ = ∫ u in (2:ℝ)..t, (0:ℝ) := intervalIntegral.integral_congr (fun u hu => by
      rw [Set.uIcc_of_ge ht] at hu
      exact weight_zero (by linarith [hu.2]))
    _ = 0 := by simp


-- @@ L97-100 verbatim
lemma primitive_nonneg (t : ℝ) : 0 ≤ primitive t := by
  rcases le_total t 2 with ht | ht
  · rw [primitive_zero ht]
  · exact intervalIntegral.integral_nonneg ht (fun u _ => weight_nonneg u)


-- @@ L102-124 verbatim
lemma primitive_tail {t : ℝ} (ht : 4 ≤ t) :
    primitive t = total - 4 * (1+t)^(-1/4:ℝ) := by
  have hi : (∫ u in (4:ℝ)..t, weight u) =
      -4*(1+t)^(-1/4:ℝ) - (-4*(1+4)^(-1/4:ℝ)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le ht] at hu
      have hpos : 0 < 1+u := by linarith [hu.1]
      have hd := ((hasDerivAt_const u (1:ℝ)).add (hasDerivAt_id u)).rpow_const
        (p := (-1/4:ℝ)) (Or.inl hpos.ne')
      have hs := hd.const_mul (-4:ℝ)
      convert! hs using 1
      norm_num [weight_tail hu.1]
      ring
    · exact weight_smooth.continuous.intervalIntegrable 4 t
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (weight_smooth.continuous.intervalIntegrable 2 4)
    (weight_smooth.continuous.intervalIntegrable 4 t)
  rw [hi] at ha
  change primitive 4 + _ = primitive t at ha
  rw [← ha, total]
  norm_num
  ring


-- @@ L126-130 verbatim
lemma total_pos : 0 < total := by
  have h := primitive_nonneg 4
  have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 5) (-1/4:ℝ)
  unfold total
  positivity


-- @@ L132-142 verbatim
lemma primitive_le_total (t : ℝ) : primitive t ≤ total := by
  by_cases ht : 4 ≤ t
  · rw [primitive_tail ht]
    have hp := Real.rpow_nonneg (by linarith : 0 ≤ 1+t) (-1/4:ℝ)
    linarith
  · have hm : Monotone primitive :=
      monotone_of_hasDerivAt_nonneg (fun t => primitive_hasDerivAt t) (fun t => weight_nonneg t)
    have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 5) (-1/4:ℝ)
    have h := hm (le_of_not_ge ht)
    unfold total
    linarith


-- @@ L144-154 verbatim
lemma primitive_limit : Tendsto primitive atTop (𝓝 total) := by
  have hp : Tendsto (fun t : ℝ => (1+t)^(-1/4:ℝ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => 1+t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp ht
  have hl := (tendsto_const_nhds (x := total)).sub
    ((tendsto_const_nhds (x := (4:ℝ))).mul hp)
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (4:ℝ)] with t ht
  exact (primitive_tail ht).symm


-- @@ L156-157 verbatim
lemma profile_smooth (μ : ℝ) : ContDiff ℝ ∞ (profile μ) :=
  (contDiff_const.mul primitive_smooth).exp


-- @@ L159-159 verbatim
lemma profile_pos (μ t : ℝ) : 0 < profile μ t := Real.exp_pos _


-- @@ L161-163 verbatim
lemma profile_le_one {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) : profile μ t ≤ 1 := by
  apply Real.exp_le_one_iff.2
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hμ) (primitive_nonneg t)


-- @@ L165-168 verbatim
lemma profile_lower {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) :
    Real.exp (-μ * total) ≤ profile μ t := by
  apply Real.exp_le_exp.2
  exact mul_le_mul_of_nonpos_left (primitive_le_total t) (neg_nonpos.2 hμ)


-- @@ L170-171 verbatim
lemma profile_initial {μ t : ℝ} (ht : t ≤ 2) : profile μ t = 1 := by
  simp [profile, primitive_zero ht]


-- @@ L173-176 verbatim
lemma profile_limit (μ : ℝ) :
    Tendsto (profile μ) atTop (𝓝 (Real.exp (-μ * total))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := -μ)).mul primitive_limit)


-- @@ L178-180 verbatim
lemma profile_hasDerivAt (μ t : ℝ) :
    HasDerivAt (profile μ) (profile μ t * slope μ t) t := by
  convert! ((primitive_hasDerivAt t).const_mul (-μ)).exp using 1


-- @@ L182-183 verbatim
lemma profile_logSlope (μ t : ℝ) : deriv (profile μ) t / profile μ t = slope μ t := by
  rw [(profile_hasDerivAt μ t).deriv, mul_div_cancel_left₀ _ (profile_pos μ t).ne']


-- @@ L185-186 verbatim
lemma slope_nonpos {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) : slope μ t ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hμ) (weight_nonneg t)


-- @@ L188-192 verbatim
lemma slope_lower {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (t : ℝ) :
    -(1/4:ℝ) ≤ slope μ t := by
  have h := mul_le_mul_of_nonneg_left (weight_le_one t) hμ
  unfold slope
  nlinarith


-- @@ L194-194 verbatim
end HarmonicCounterexample.Scale


-- @@ L196-196 verbatim
end


-- @@ L198-198 verbatim
noncomputable section

-- @@ L199-199 verbatim
open Filter MeasureTheory

-- @@ L200-200 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L201-201 verbatim
open Matrix

-- @@ L202-202 verbatim
open scoped BigOperators

-- @@ L203-203 verbatim
open Matrix

-- @@ L204-204 verbatim
open scoped BigOperators

-- @@ L205-205 verbatim
open Filter Matrix

-- @@ L206-206 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L207-207 verbatim
open Filter MeasureTheory

-- @@ L208-208 verbatim
open scoped Topology ContDiff


-- @@ L210-210 verbatim
namespace HarmonicCounterexample.Scale


-- @@ L212-224 verbatim
lemma weight_deriv {t : ℝ} (ht : 2 < t) :
    deriv weight t = deriv cutoff t * (1+t)^(-5/4:ℝ) +
      cutoff t * ((-5/4:ℝ) * (1+t)^(-5/4:ℝ) / (1+t)) := by
  have hp : 0 < 1+t := by linarith
  have hd := (cutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt.mul
    (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).rpow_const
      (p := (-5/4:ℝ)) (Or.inl hp.ne'))
  have he := hd.deriv
  change deriv weight t = _ at he
  rw [he]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [Real.rpow_sub_one hp.ne']
  ring


-- @@ L226-227 verbatim
lemma slope_deriv (μ t : ℝ) : deriv (slope μ) t = -μ * deriv weight t := by
  exact ((weight_smooth.differentiable (by simp)).differentiableAt.hasDerivAt.const_mul (-μ)).deriv


-- @@ L229-243 verbatim
lemma slope_deriv_bound {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 2 < t) :
    deriv (slope μ) t ≤ -(5:ℝ) / (4*(1+t)) * slope μ t := by
  rw [slope_deriv, weight_deriv ht]
  have hp : 0 ≤ (1+t)^(-5/4:ℝ) := Real.rpow_nonneg (by linarith) _
  have hc : 0 ≤ deriv cutoff t := cutoff_mono.deriv_nonneg
  have hh : 0 ≤ μ * (deriv cutoff t * (1+t)^(-5/4:ℝ)) := by positivity
  unfold slope weight
  have he : -μ * (deriv cutoff t * (1+t)^(-5/4:ℝ) +
      cutoff t * ((-5/4:ℝ) * (1+t)^(-5/4:ℝ) / (1+t))) =
      -(5:ℝ) / (4*(1+t)) * (-μ * (cutoff t * (1+t)^(-5/4:ℝ))) -
      μ * (deriv cutoff t * (1+t)^(-5/4:ℝ)) := by
        field_simp
        ring
  rw [he]
  linarith


-- @@ L245-249 verbatim
lemma slope_initial_deriv {t : ℝ} (ht : t ≤ 2) (μ : ℝ) : deriv (slope μ) t = 0 := by
  have he : slope μ =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [eventually_lt_nhds (show t < 5/2 by linarith)] with u hu
    simp only [slope, weight_zero hu.le, mul_zero]
  rw [he.deriv_eq, deriv_const]


-- @@ L251-269 verbatim
/-- The exact concavity estimate used on the whole initial round region,
not merely the limiting tail. -/
theorem radial_concavity {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (t : ℝ) :
    slope μ t + deriv (slope μ) t + slope μ t ^ 2 ≤ 0 := by
  by_cases ht : t ≤ 2
  · rw [slope_initial_deriv ht, slope, weight_zero (by linarith)]
    norm_num
  · have ht' : 2 < t := lt_of_not_ge ht
    have hb := slope_lower hμ hμ1 t
    have hb0 := slope_nonpos hμ t
    have hd := slope_deriv_bound hμ ht'
    have hden : 0 < 4*(1+t) := by linarith
    have hquot : (5:ℝ)/(4*(1+t)) ≤ 5/12 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<12)).2
      nlinarith
    have hfac : 0 ≤ 1 - (5:ℝ)/(4*(1+t)) + slope μ t := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hb0 hfac
    simp only [neg_div] at hd
    nlinarith


-- @@ L271-276 verbatim
lemma log_profile_tail {μ t : ℝ} (ht : 4 ≤ t) :
    Real.log (profile μ t / Real.exp (-μ * total)) =
      4*μ*(1+t)^(-1/4:ℝ) := by
  rw [Real.log_div (profile_pos μ t).ne' (Real.exp_pos _).ne', profile,
    Real.log_exp, Real.log_exp, primitive_tail ht]
  ring


-- @@ L278-279 verbatim
lemma slope_tail {μ t : ℝ} (ht : 4 ≤ t) :
    slope μ t = -μ*(1+t)^(-5/4:ℝ) := by rw [slope, weight_tail ht]


-- @@ L281-285 verbatim
lemma profile_antitone {μ : ℝ} (hμ : 0 ≤ μ) : Antitone (profile μ) := by
  apply antitone_of_deriv_nonpos ((profile_smooth μ).differentiable (by simp))
  intro t
  rw [(profile_hasDerivAt μ t).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (profile_pos μ t).le (slope_nonpos hμ t)


-- @@ L287-304 verbatim
/-- Every requested subunit endpoint sufficiently close to one is attained
by the same fixed cutoff, before any control family is specified. -/
theorem choose_scale {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hclose : Real.exp (-total/4) ≤ a) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1/4 ∧
      Tendsto (profile μ) atTop (𝓝 a) ∧ Real.exp (-μ*total) = a := by
  let μ := -Real.log a / total
  have hμ : 0 < μ := div_pos (neg_pos.2 (Real.log_neg ha ha1)) total_pos
  have he : -μ * total = Real.log a := by
    dsimp [μ]
    field_simp [total_pos.ne']
  have he' : Real.exp (-μ*total) = a := by rw [he, Real.exp_log ha]
  have hlog : -total/4 ≤ Real.log a := by
    rw [← Real.exp_le_exp, Real.exp_log ha]
    exact hclose
  have hm : μ ≤ 1/4 := (div_le_iff₀ total_pos).2 (by linarith)
  refine ⟨μ, hμ, hm, ?_, he'⟩
  simpa only [he'] using profile_limit μ


-- @@ L306-306 verbatim
end HarmonicCounterexample.Scale


-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
noncomputable section

-- @@ L311-311 verbatim
open Filter MeasureTheory

-- @@ L312-312 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L313-313 verbatim
open Matrix

-- @@ L314-314 verbatim
open scoped BigOperators

-- @@ L315-315 verbatim
open Matrix

-- @@ L316-316 verbatim
open scoped BigOperators

-- @@ L317-317 verbatim
open Filter Matrix

-- @@ L318-318 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L319-319 verbatim
open Filter MeasureTheory

-- @@ L320-320 verbatim
open scoped Topology ContDiff


-- @@ L322-322 verbatim
namespace HarmonicCounterexample.Scale


-- @@ L324-338 verbatim
lemma radial_tail_margin {μ t : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (ht : 4 ≤ t) :
    slope μ t + deriv (slope μ) t + slope μ t ^ 2 ≤
      -(μ/2)*(1+t)^(-5/4:ℝ) := by
  have hb := slope_lower hμ hμ1 t
  have hb0 := slope_nonpos hμ t
  have hd := slope_deriv_bound hμ (by linarith : 2 < t)
  have hden : 0 < 4*(1+t) := by linarith
  have hquot : (5:ℝ)/(4*(1+t)) ≤ 1/4 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<4)).2
    linarith
  have hfac : (1:ℝ)/2 ≤ 1-(5:ℝ)/(4*(1+t))+slope μ t := by linarith
  have hm := mul_le_mul_of_nonpos_left hfac hb0
  have he := slope_tail (μ := μ) ht
  simp only [neg_div] at hd
  nlinarith


-- @@ L340-348 verbatim
lemma slope_limit (μ : ℝ) : Tendsto (slope μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1+t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5/4)).comp ht
  have hh := hp.const_mul (-μ)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (4:ℝ)] with t ht
  simpa only [Function.comp_def, neg_div] using (slope_tail (μ := μ) ht).symm


-- @@ L350-363 verbatim
lemma slope_deriv_tail {μ t : ℝ} (ht : 4 ≤ t) :
    deriv (slope μ) t = (5*μ/4)*(1+t)^(-5/4:ℝ)/(1+t) := by
  have he : slope μ =ᶠ[𝓝 t] fun u => -μ*(1+u)^(-5/4:ℝ) := by
    filter_upwards [eventually_gt_nhds (show 7/2 < t by linarith)] with u hu
    simp only [slope, weight, cutoff_one hu.le, one_mul]
  rw [he.deriv_eq]
  have hp : 0 < 1+t := by linarith
  have hd := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).rpow_const
    (p := (-5/4:ℝ)) (Or.inl hp.ne')).const_mul (-μ)
  change HasDerivAt (fun u => -μ*(1+u)^(-5/4:ℝ)) _ t at hd
  rw [hd.deriv]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [Real.rpow_sub_one hp.ne']
  ring


-- @@ L365-375 verbatim
lemma slope_deriv_limit (μ : ℝ) : Tendsto (deriv (slope μ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1+t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5/4)).comp ht
  have hi := tendsto_inv_atTop_zero.comp ht
  have hh := (hp.const_mul (5*μ/4)).mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (4:ℝ)] with t ht
  simpa only [Function.comp_def, neg_div, div_eq_mul_inv, neg_mul] using
    (slope_deriv_tail (μ := μ) ht).symm


-- @@ L377-377 verbatim
end HarmonicCounterexample.Scale


-- @@ L379-379 verbatim
end


-- @@ L381-381 verbatim
noncomputable section

-- @@ L382-382 verbatim
open Filter MeasureTheory

-- @@ L383-383 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L384-384 verbatim
open Matrix

-- @@ L385-385 verbatim
open scoped BigOperators

-- @@ L386-386 verbatim
open Matrix

-- @@ L387-387 verbatim
open scoped BigOperators

-- @@ L388-388 verbatim
open Filter Matrix

-- @@ L389-389 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L390-390 verbatim
open Filter MeasureTheory

-- @@ L391-391 verbatim
open scoped Topology ContDiff

-- @@ L392-392 verbatim
open Filter

-- @@ L393-393 verbatim
open scoped BigOperators Topology


-- @@ L395-395 verbatim
namespace HarmonicCounterexample.Schedule


-- @@ L397-398 verbatim
/-- Source period j is indexed here by j-1; no period lengths are changed. -/
def pulse (j : ℕ) : ℝ := (j + 1 : ℝ) ^ 6

-- @@ L399-399 verbatim
def dwell (j : ℕ) : ℝ := (j + 1 : ℝ) ^ 7

-- @@ L400-400 verbatim
def time (j : ℕ) : ℝ := 10 + ∑ i ∈ Finset.range j, (dwell i + 4 * pulse i)

-- @@ L401-401 verbatim
def dwellSum (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, dwell i


-- @@ L403-403 verbatim
theorem time_zero : time 0 = 10 := by simp [time]

-- @@ L404-406 verbatim
theorem time_succ (j : ℕ) : time (j + 1) = time j + dwell j + 4 * pulse j := by
  simp [time, Finset.sum_range_succ]
  ring


-- @@ L408-417 verbatim
theorem sum_pow_seven (n : ℕ) :
    ∑ j ∈ Finset.range n, (j + 1 : ℝ) ^ 7 =
      (n : ℝ) ^ 8 / 8 + (n : ℝ) ^ 7 / 2 + 7 * (n : ℝ) ^ 6 / 12 -
      7 * (n : ℝ) ^ 4 / 24 + (n : ℝ) ^ 2 / 12 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


-- @@ L419-428 verbatim
theorem sum_pow_six (n : ℕ) :
    ∑ j ∈ Finset.range n, (j + 1 : ℝ) ^ 6 =
      (n : ℝ) ^ 7 / 7 + (n : ℝ) ^ 6 / 2 + (n : ℝ) ^ 5 / 2 -
      (n : ℝ) ^ 3 / 6 + (n : ℝ) / 42 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


-- @@ L430-433 verbatim
theorem dwellSum_formula (n : ℕ) :
    dwellSum n = (n : ℝ) ^ 8 / 8 + (n : ℝ) ^ 7 / 2 + 7 * (n : ℝ) ^ 6 / 12 -
      7 * (n : ℝ) ^ 4 / 24 + (n : ℝ) ^ 2 / 12 :=
  sum_pow_seven n


-- @@ L435-441 verbatim
theorem time_formula (n : ℕ) :
    time n = (n : ℝ) ^ 8 / 8 + 15 * (n : ℝ) ^ 7 / 14 + 31 * (n : ℝ) ^ 6 / 12 +
      2 * (n : ℝ) ^ 5 - 7 * (n : ℝ) ^ 4 / 24 - 2 * (n : ℝ) ^ 3 / 3 +
      (n : ℝ) ^ 2 / 12 + 2 * (n : ℝ) / 21 + 10 := by
  simp only [time, dwell, pulse, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_pow_seven, sum_pow_six]
  ring


-- @@ L443-445 verbatim
theorem time_pos (n : ℕ) : 0 < time n := by
  apply add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 10)
  exact Finset.sum_nonneg fun i _ => by dsimp [dwell, pulse]; positivity


-- @@ L447-448 verbatim
theorem dwellSum_nonneg (n : ℕ) : 0 ≤ dwellSum n := by
  exact Finset.sum_nonneg fun i _ => by dsimp [dwell]; positivity


-- @@ L450-451 verbatim
theorem tendsto_inv_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop


-- @@ L453-464 verbatim
theorem dwellSum_scaled :
    Tendsto (fun n => dwellSum n / (n : ℝ) ^ 8) atTop (𝓝 (1 / 8 : ℝ)) := by
  have h := ((((tendsto_const_nhds (x := (1 / 8 : ℝ))).add (tendsto_inv_nat.div_const 2)).add
    ((tendsto_inv_nat.pow 2).const_mul (7 / 12))).sub
    ((tendsto_inv_nat.pow 4).const_mul (7 / 24))).add
    ((tendsto_inv_nat.pow 6).div_const 12)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [dwellSum_formula]
  field_simp


-- @@ L466-481 verbatim
theorem time_scaled :
    Tendsto (fun n => time n / (n : ℝ) ^ 8) atTop (𝓝 (1 / 8 : ℝ)) := by
  have h := ((((((((tendsto_const_nhds (x := (1 / 8 : ℝ))).add (tendsto_inv_nat.const_mul (15 / 14))).add
    ((tendsto_inv_nat.pow 2).const_mul (31 / 12))).add
    ((tendsto_inv_nat.pow 3).const_mul 2)).sub
    ((tendsto_inv_nat.pow 4).const_mul (7 / 24))).sub
    ((tendsto_inv_nat.pow 5).const_mul (2 / 3))).add
    ((tendsto_inv_nat.pow 6).div_const 12)).add
    ((tendsto_inv_nat.pow 7).const_mul (2 / 21))).add
    ((tendsto_inv_nat.pow 8).const_mul 10)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [time_formula]
  field_simp


-- @@ L483-491 verbatim
theorem dwell_scaled :
    Tendsto (fun n => dwell n / (n : ℝ) ^ 8) atTop (𝓝 0) := by
  have h := ((tendsto_inv_nat.const_add 1).pow 7).mul tendsto_inv_nat
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  dsimp [dwell]
  field_simp


-- @@ L493-501 verbatim
theorem pulse_scaled :
    Tendsto (fun n => pulse n / (n : ℝ) ^ 8) atTop (𝓝 0) := by
  have h := ((tendsto_inv_nat.const_add 1).pow 6).mul (tendsto_inv_nat.pow 2)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  dsimp [pulse]
  field_simp


-- @@ L503-514 verbatim
lemma cancel_scale_limit {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto (fun n => f n / (n : ℝ) ^ 8) atTop (𝓝 a)) :
    Tendsto (fun n => f n / time n) atTop (𝓝 (8 * a)) := by
  have h := hf.div time_scaled (by norm_num : (1 / 8 : ℝ) ≠ 0)
  norm_num only [div_div, div_one] at h
  convert h.congr' (show (fun n => (f n / (n : ℝ) ^ 8) /
    (time n / (n : ℝ) ^ 8)) =ᶠ[atTop] (fun n => f n / time n) from ?_) using 1
  · congr 1
    ring
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp


-- @@ L516-518 verbatim
theorem dwellSum_time :
    Tendsto (fun n => dwellSum n / time n) atTop (𝓝 (1 : ℝ)) := by
  simpa using cancel_scale_limit dwellSum_scaled


-- @@ L520-522 verbatim
theorem dwell_time :
    Tendsto (fun n => dwell n / time n) atTop (𝓝 (0 : ℝ)) := by
  simpa using cancel_scale_limit dwell_scaled


-- @@ L524-526 verbatim
theorem pulse_time :
    Tendsto (fun n => pulse n / time n) atTop (𝓝 (0 : ℝ)) := by
  simpa using cancel_scale_limit pulse_scaled


-- @@ L528-535 verbatim
theorem duration_time :
    Tendsto (fun n => (time (n+1) - time n) / time n) atTop (𝓝 (0 : ℝ)) := by
  have h := dwell_time.add (pulse_time.const_mul 4)
  convert h using 1
  · ext n
    rw [time_succ]
    ring
  · norm_num


-- @@ L537-543 verbatim
theorem time_strictMono : StrictMono time := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [time_succ]
  have hpos : 0 < dwell n := by dsimp [dwell]; positivity
  have hp : 0 ≤ pulse n := by dsimp [pulse]; positivity
  linarith


-- @@ L545-552 verbatim
theorem time_atTop : Tendsto time atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 8) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 8 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 8) hpow time_scaled
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp


-- @@ L554-561 verbatim
theorem dwellSum_atTop : Tendsto dwellSum atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ 8) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 8 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 8) hpow dwellSum_scaled
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp


-- @@ L563-563 verbatim
end HarmonicCounterexample.Schedule


-- @@ L565-565 verbatim
end


-- @@ L567-567 verbatim
noncomputable section

-- @@ L568-568 verbatim
open Filter MeasureTheory

-- @@ L569-569 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L570-570 verbatim
open Matrix

-- @@ L571-571 verbatim
open scoped BigOperators

-- @@ L572-572 verbatim
open Matrix

-- @@ L573-573 verbatim
open scoped BigOperators

-- @@ L574-574 verbatim
open Filter Matrix

-- @@ L575-575 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L576-576 verbatim
open Filter MeasureTheory

-- @@ L577-577 verbatim
open scoped Topology ContDiff

-- @@ L578-578 verbatim
open Filter

-- @@ L579-579 verbatim
open scoped BigOperators Topology


-- @@ L581-581 verbatim
namespace HarmonicCounterexample.Pulses

-- @@ L582-582 verbatim
open Schedule

-- @@ L583-583 verbatim
open scoped ContDiff


-- @@ L585-586 verbatim
/-- A globally smooth, fixed ramp, constant on neighborhoods of both endpoints. -/
def ramp (t : ℝ) : ℝ := Real.smoothTransition (2*t-1/2)


-- @@ L588-589 verbatim
lemma ramp_smooth : ContDiff ℝ ∞ ramp :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

-- @@ L590-591 verbatim
lemma ramp_zero {t : ℝ} (ht : t ≤ 1/4) : ramp t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

-- @@ L592-593 verbatim
lemma ramp_one {t : ℝ} (ht : 3/4 ≤ t) : ramp t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

-- @@ L594-595 verbatim
lemma ramp_range (t : ℝ) : 0 ≤ ramp t ∧ ramp t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

-- @@ L596-597 verbatim
lemma ramp_mono : Monotone ramp := fun _ _ h =>
  Real.smoothTransition.monotone (by linarith)


-- @@ L599-599 verbatim
lemma pulse_pos (j : ℕ) : 0 < pulse j := by unfold pulse; positivity

-- @@ L600-600 verbatim
lemma dwell_pos (j : ℕ) : 0 < dwell j := by unfold dwell; positivity


-- @@ L602-615 verbatim
/-- Smoothness of this series is LOCAL FINITENESS, not an unproved convergence
claim or an exchange of derivatives and a general infinite sum. -/
theorem smooth_escaping_sum {f : ℕ → ℝ → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hz : ∀ j t, t ≤ time j → f j t = 0) :
    ContDiff ℝ ∞ (fun t => ∑' j, f j t) := by
  apply contDiff_iff_contDiffAt.2
  intro t
  obtain ⟨N, hN⟩ := eventually_atTop.1 (time_atTop.eventually_gt_atTop (t+1))
  apply (ContDiffAt.sum (s := Finset.range N) (fun j _ => (hf j).contDiffAt)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show t < t+1 by linarith)] with u hu
  apply tsum_eq_sum
  intro j hj
  have hj' : N ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  exact hz j u (by linarith [hN j hj'])


-- @@ L617-620 verbatim
/-- The upward and downward ramps, with the exact dwell and rest schedule. -/
def window (j : ℕ) (t : ℝ) : ℝ :=
  ramp ((t-time j-pulse j)/pulse j) -
    ramp ((t-time j-2*pulse j-dwell j)/pulse j)


-- @@ L622-624 verbatim
lemma window_smooth (j : ℕ) : ContDiff ℝ ∞ (window j) := by
  apply (ramp_smooth.comp ?_).sub (ramp_smooth.comp ?_) <;>
    fun_prop


-- @@ L626-634 verbatim
lemma window_zero_before {j : ℕ} {t : ℝ} (ht : t ≤ time j + pulse j) :
    window j t = 0 := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [window, ramp_zero, ramp_zero, sub_self]
  · apply (div_le_iff₀ hp).2
    linarith
  · apply (div_le_iff₀ hp).2
    linarith


-- @@ L636-644 verbatim
lemma window_zero_after {j : ℕ} {t : ℝ}
    (ht : time j + 3*pulse j + dwell j ≤ t) : window j t = 0 := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [window, ramp_one, ramp_one, sub_self]
  · apply (le_div_iff₀ hp).2
    linarith
  · apply (le_div_iff₀ hp).2
    linarith


-- @@ L646-654 verbatim
lemma window_one {j : ℕ} {t : ℝ}
    (hlo : time j + 2*pulse j ≤ t)
    (hhi : t ≤ time j + 2*pulse j + dwell j) : window j t = 1 := by
  have hp := pulse_pos j
  rw [window, ramp_one, ramp_zero, sub_zero]
  · apply (div_le_iff₀ hp).2
    linarith
  · apply (le_div_iff₀ hp).2
    linarith


-- @@ L656-664 verbatim
lemma window_range (j : ℕ) (t : ℝ) : 0 ≤ window j t ∧ window j t ≤ 1 := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  have hm := ramp_mono (show (t-time j-2*pulse j-dwell j)/pulse j ≤
      (t-time j-pulse j)/pulse j from (div_le_div_iff_of_pos_right hp).2 (by linarith))
  have ha := ramp_range ((t-time j-pulse j)/pulse j)
  have hb := ramp_range ((t-time j-2*pulse j-dwell j)/pulse j)
  unfold window
  constructor <;> linarith


-- @@ L666-668 verbatim
/-- Controls are arbitrary across periods; only each individual scalar bump is smooth. -/
def increment (z : ℕ → ℝ → ℝ) (qstar : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (pulse j)⁻¹ * z j ((t-time j)/pulse j) + (qstar-1)*window j t


-- @@ L670-671 verbatim
def profile (z : ℕ → ℝ → ℝ) (qstar : ℝ) (j0 : ℕ) (t : ℝ) : ℝ :=
  1 + ∑' j : ℕ, if j0 ≤ j then increment z qstar j t else 0


-- @@ L673-677 verbatim
lemma increment_smooth {z : ℕ → ℝ → ℝ} (hz : ∀ j, ContDiff ℝ ∞ (z j))
    (qstar : ℝ) (j : ℕ) : ContDiff ℝ ∞ (increment z qstar j) := by
  exact (contDiff_const.mul ((hz j).comp
    ((contDiff_id.sub contDiff_const).div_const _))).add
    (contDiff_const.mul (window_smooth j))


-- @@ L679-685 verbatim
lemma increment_zero_before {z : ℕ → ℝ → ℝ}
    (hz : ∀ j u, u ≤ 0 → z j u = 0) {qstar t : ℝ} {j : ℕ}
    (ht : t ≤ time j) : increment z qstar j t = 0 := by
  have hp := pulse_pos j
  rw [increment, hz j _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) hp.le),
    window_zero_before (by linarith)]
  ring


-- @@ L687-695 verbatim
lemma increment_zero_after {z : ℕ → ℝ → ℝ}
    (hz : ∀ j u, 1 ≤ u → z j u = 0) {qstar t : ℝ} {j : ℕ}
    (ht : time (j+1) ≤ t) : increment z qstar j t = 0 := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [time_succ] at ht
  rw [increment, hz j _ ((le_div_iff₀ hp).2 (by linarith)),
    window_zero_after (by linarith)]
  ring


-- @@ L697-709 verbatim
lemma profile_smooth {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    (hz : ∀ j u, u ≤ 0 → z j u = 0) (qstar : ℝ) (j0 : ℕ) :
    ContDiff ℝ ∞ (profile z qstar j0) := by
  apply contDiff_const.add
  apply smooth_escaping_sum
  · intro j
    split_ifs
    · exact increment_smooth hs _ _
    · exact contDiff_const
  · intro j t ht
    split_ifs
    · exact increment_zero_before hz ht
    · rfl


-- @@ L711-720 verbatim
lemma profile_initial {z : ℕ → ℝ → ℝ}
    (hz : ∀ j u, u ≤ 0 → z j u = 0) {qstar t : ℝ} {j0 : ℕ}
    (ht : t ≤ time j0) : profile z qstar j0 t = 1 := by
  unfold profile
  have he : (fun j : ℕ => if j0 ≤ j then increment z qstar j t else 0) = fun _ => 0 := by
    funext j
    split_ifs with hj
    · exact increment_zero_before hz (ht.trans (time_strictMono.monotone hj))
    · rfl
  rw [he, tsum_zero, add_zero]


-- @@ L722-734 verbatim
lemma profile_period {z : ℕ → ℝ → ℝ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j ≤ t) (hhi : t ≤ time (j+1)) :
    profile z qstar j0 t = 1 + increment z qstar j t := by
  unfold profile
  rw [tsum_eq_single j, ite_eq_left hj]
  intro i hi
  split_ifs
  · rcases lt_or_gt_of_ne hi with hij | hij
    · exact increment_zero_after hz1 ((time_strictMono.monotone hij).trans hlo)
    · exact increment_zero_before hz0 (hhi.trans (time_strictMono.monotone hij))
  · rfl


-- @@ L736-736 verbatim
end HarmonicCounterexample.Pulses


-- @@ L738-738 verbatim
end


-- @@ L740-740 verbatim
noncomputable section

-- @@ L741-741 verbatim
open Filter MeasureTheory

-- @@ L742-742 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L743-743 verbatim
open Matrix

-- @@ L744-744 verbatim
open scoped BigOperators

-- @@ L745-745 verbatim
open Matrix

-- @@ L746-746 verbatim
open scoped BigOperators

-- @@ L747-747 verbatim
open Filter Matrix

-- @@ L748-748 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L749-749 verbatim
open Filter MeasureTheory

-- @@ L750-750 verbatim
open scoped Topology ContDiff

-- @@ L751-751 verbatim
open Filter

-- @@ L752-752 verbatim
open scoped BigOperators Topology

-- @@ L753-753 verbatim
open Filter

-- @@ L754-754 verbatim
open scoped Topology


-- @@ L756-756 verbatim
namespace HarmonicCounterexample.GlobalGrowth


-- @@ L758-777 verbatim
/-- Every late real time lies between consecutive entries of an unbounded grid.
No interpolation or endpoint-only growth convention is used. -/
lemma grid_bracket {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    (N : ℕ) {t : ℝ} (ht : τ N ≤ t) :
    ∃ j ≥ N, τ j ≤ t ∧ t ≤ τ (j+1) := by
  have hshift : Tendsto (fun j => τ (j + N)) atTop atTop :=
    hτ.comp (Filter.tendsto_add_atTop_nat N)
  have hex : ∃ j : ℕ, t < τ (j+N) :=
    (hshift.eventually (eventually_gt_atTop t)).exists
  have hk : Nat.find hex ≠ 0 := by
    intro heq
    have h := Nat.find_spec hex
    simp only [heq, zero_add] at h
    exact h.not_ge ht
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
  refine ⟨j + N, Nat.le_add_left _ _, ?_, ?_⟩
  · have h := Nat.find_min hex (show j < Nat.find hex by omega)
    exact le_of_not_gt h
  · have h := (Nat.find_spec hex).le
    simpa only [hj, Nat.succ_eq_add_one, Nat.add_right_comm] using h


-- @@ L779-802 verbatim
/-- The full real-time bridge in the proof of the main theorem. A bounded
Riccati matrix controls each period, and sublinear period lengths prevent
hidden growth between endpoints. -/
theorem all_time_log_bound {τ : ℕ → ℝ} {w : ℝ → ℝ} {d α C : ℝ}
    (hτ : Tendsto τ atTop atTop) (hpos : ∀ j, 0 < τ j)
    (hend : Tendsto (fun j => w (τ j) / τ j) atTop (𝓝 d))
    (hduration : Tendsto (fun j => (τ (j+1) - τ j) / τ j) atTop (𝓝 0))
    (hlocal : ∀ᶠ j in atTop, ∀ t ∈ Set.Icc (τ j) (τ (j+1)),
      w t ≤ w (τ j) + C * (τ (j+1) - τ j))
    (hd : 0 ≤ d) (hα : d < α) :
    ∀ᶠ t in atTop, w t ≤ α * t := by
  have hlim := hend.add (hduration.const_mul C)
  simp only [mul_zero, add_zero] at hlim
  have hevent := hlim.eventually (eventually_lt_nhds hα)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hevent.and hlocal)
  filter_upwards [eventually_ge_atTop (τ N)] with t ht
  obtain ⟨j, hjN, hjt, htj⟩ := grid_bracket hτ N ht
  have hj := hN j hjN
  have hdiv : (w (τ j) + C * (τ (j+1) - τ j)) / τ j < α := by
    simpa only [add_div, mul_div_assoc] using hj.1
  calc
    w t ≤ w (τ j) + C * (τ (j+1) - τ j) := hj.2 t ⟨hjt, htj⟩
    _ ≤ α * τ j := ((div_lt_iff₀ (hpos j)).1 hdiv).le
    _ ≤ α * t := mul_le_mul_of_nonneg_left hjt (hd.trans hα.le)


-- @@ L804-820 verbatim
/-- Passing from logarithmic time to radius is an actual bound on every
sufficiently large radius, not just on the discrete schedule. -/
theorem radial_power_bound {y : ℝ → ℝ} {α : ℝ}
    (hy : ∀ t, 0 ≤ y t)
    (hlog : ∀ᶠ t in atTop, Real.log (y t) ≤ α * t) :
    ∀ᶠ r in atTop, y (Real.log r) ≤ r ^ α := by
  have h := Real.tendsto_log_atTop.eventually hlog
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hrpos
  by_cases hz : y (Real.log r) = 0
  · rw [hz]
    exact Real.rpow_nonneg hrpos.le _
  · have hypos : 0 < y (Real.log r) := lt_of_le_of_ne (hy _) (Ne.symm hz)
    calc
      y (Real.log r) = Real.exp (Real.log (y (Real.log r))) :=
        (Real.exp_log hypos).symm
      _ ≤ Real.exp (α * Real.log r) := Real.exp_le_exp.2 hr
      _ = r ^ α := by rw [Real.rpow_def_of_pos hrpos, mul_comm]


-- @@ L822-822 verbatim
end HarmonicCounterexample.GlobalGrowth


-- @@ L824-824 verbatim
end


-- @@ L826-826 verbatim
noncomputable section

-- @@ L827-827 verbatim
open Filter MeasureTheory

-- @@ L828-828 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L829-829 verbatim
open Matrix

-- @@ L830-830 verbatim
open scoped BigOperators

-- @@ L831-831 verbatim
open Matrix

-- @@ L832-832 verbatim
open scoped BigOperators

-- @@ L833-833 verbatim
open Filter Matrix

-- @@ L834-834 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L835-835 verbatim
open Filter MeasureTheory

-- @@ L836-836 verbatim
open scoped Topology ContDiff

-- @@ L837-837 verbatim
open Filter

-- @@ L838-838 verbatim
open scoped BigOperators Topology

-- @@ L839-839 verbatim
open Filter

-- @@ L840-840 verbatim
open scoped Topology


-- @@ L842-842 verbatim
namespace HarmonicCounterexample.Pulses

-- @@ L843-843 verbatim
open Schedule GlobalGrowth


-- @@ L845-861 verbatim
lemma profile_bounds_on_period {z : ℕ → ℝ → ℝ} {M qstar t : ℝ} {j0 j : ℕ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    (hbound : ∀ j u, |z j u| ≤ M) (hq : 1 ≤ qstar)
    (hj : j0 ≤ j) (hlo : time j ≤ t) (hhi : t ≤ time (j+1)) :
    1 - M / pulse j ≤ profile z qstar j0 t ∧
      profile z qstar j0 t ≤ qstar + M / pulse j := by
  rw [profile_period hz0 hz1 hj hlo hhi]
  have hp := pulse_pos j
  have hz := abs_le.1 (hbound j ((t-time j)/pulse j))
  have hw := window_range j t
  have hq0 : 0 ≤ qstar-1 := by linarith
  have hzw := mul_le_mul_of_nonneg_left hz.2 (inv_nonneg.2 hp.le)
  have hzv := mul_le_mul_of_nonneg_left hz.1 (inv_nonneg.2 hp.le)
  have hw0 := mul_nonneg hq0 hw.1
  have hw1 := mul_le_mul_of_nonneg_left hw.2 hq0
  unfold increment
  constructor <;> nlinarith [show M / pulse j = (pulse j)⁻¹ * M by ring]


-- @@ L863-882 verbatim
/-- Uniform positivity is obtained by delaying the pulses, with NO dependence
on the subsequently chosen sequence of parameters. -/
theorem choose_positive_start {z : ℕ → ℝ → ℝ} {M qstar : ℝ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    (hbound : ∀ j u, |z j u| ≤ M) (hq : 1 ≤ qstar) :
    ∃ j0 : ℕ, ∀ t, 1/2 ≤ profile z qstar j0 t ∧
      profile z qstar j0 t ≤ qstar + 1/2 := by
  have hp : Tendsto pulse atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp
      (tendsto_atTop_mono (fun j : ℕ =>
        show (j:ℝ) ≤ (j:ℝ)+1 by linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨j0, hj0⟩ := eventually_atTop.1 (hp.eventually (eventually_ge_atTop (2*M)))
  refine ⟨j0, fun t => ?_⟩
  by_cases ht : t ≤ time j0
  · rw [profile_initial hz0 ht]
    constructor <;> linarith
  · obtain ⟨j, hj, hlow, hhigh⟩ := grid_bracket time_atTop j0 (le_of_not_ge ht)
    have hb := profile_bounds_on_period hz0 hz1 hbound hq hj hlow hhigh
    have hr : M / pulse j ≤ 1/2 := (div_le_iff₀ (pulse_pos j)).2 (by linarith [hj0 j hj])
    constructor <;> linarith


-- @@ L884-892 verbatim
lemma profile_pulse {z : ℕ → ℝ → ℝ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j ≤ t) (hhi : t ≤ time j + pulse j) :
    profile z qstar j0 t = 1 + (pulse j)⁻¹ * z j ((t-time j)/pulse j) := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [profile_period hz0 hz1 hj hlo (by rw [time_succ]; linarith),
    increment, window_zero_before hhi, mul_zero, add_zero]


-- @@ L894-904 verbatim
lemma profile_dwell {z : ℕ → ℝ → ℝ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j + 2*pulse j ≤ t)
    (hhi : t ≤ time j + 2*pulse j + dwell j) :
    profile z qstar j0 t = qstar := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [profile_period hz0 hz1 hj (by linarith) (by rw [time_succ]; linarith),
    increment, hz1 j _ ((le_div_iff₀ hp).2 (by linarith)), window_one hlo hhi]
  ring


-- @@ L906-915 verbatim
lemma profile_rest {z : ℕ → ℝ → ℝ}
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j + 3*pulse j + dwell j ≤ t) (hhi : t ≤ time (j+1)) :
    profile z qstar j0 t = 1 := by
  have hp := pulse_pos j
  have hl := dwell_pos j
  rw [profile_period hz0 hz1 hj (by linarith) hhi,
    increment, hz1 j _ ((le_div_iff₀ hp).2 (by linarith)), window_zero_after hlo]
  ring


-- @@ L917-917 verbatim
end HarmonicCounterexample.Pulses


-- @@ L919-919 verbatim
end


-- @@ L921-921 verbatim
noncomputable section

-- @@ L922-922 verbatim
open Filter MeasureTheory

-- @@ L923-923 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L924-924 verbatim
open Matrix

-- @@ L925-925 verbatim
open scoped BigOperators

-- @@ L926-926 verbatim
open Matrix

-- @@ L927-927 verbatim
open scoped BigOperators

-- @@ L928-928 verbatim
open Filter Matrix

-- @@ L929-929 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L930-930 verbatim
open Filter MeasureTheory

-- @@ L931-931 verbatim
open scoped Topology ContDiff

-- @@ L932-932 verbatim
open Filter

-- @@ L933-933 verbatim
open scoped BigOperators Topology

-- @@ L934-934 verbatim
open Filter

-- @@ L935-935 verbatim
open scoped Topology


-- @@ L937-937 verbatim
namespace HarmonicCounterexample.Pulses

-- @@ L938-938 verbatim
open Schedule

-- @@ L939-939 verbatim
open scoped ContDiff


-- @@ L941-948 verbatim
lemma deriv_eqOn_Icc {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (he : Set.EqOn f g (Set.Icc a b)) :
    Set.EqOn (deriv f) (deriv g) (Set.Icc a b) := by
  intro t ht
  have hu := uniqueDiffOn_Icc hab t ht
  rw [← (hf t).derivWithin hu, ← (hg t).derivWithin hu]
  exact derivWithin_congr he (he ht)


-- @@ L950-957 verbatim
lemma deriv_two_eqOn_Icc {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (he : Set.EqOn f g (Set.Icc a b)) :
    Set.EqOn (deriv (deriv f)) (deriv (deriv g)) (Set.Icc a b) := by
  apply deriv_eqOn_Icc hab
    ((contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp))
    ((contDiff_infty_iff_deriv.1 hg).2.differentiable (by simp))
  exact deriv_eqOn_Icc hab (hf.differentiable (by simp)) (hg.differentiable (by simp)) he


-- @@ L959-962 verbatim
lemma affine_composition_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a b t : ℝ) :
    deriv (fun u => f ((u-a)/b)) t = deriv f ((t-a)/b) / b := by
  simpa only [Function.comp_def, div_eq_mul_inv, one_mul, id_eq] using ((hf _).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const a).div_const b)).deriv


-- @@ L964-967 verbatim
lemma affine_composition_hasDerivAt {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a b t : ℝ) :
    HasDerivAt (fun u => f ((u-a)/b)) (deriv f ((t-a)/b) / b) t := by
  simpa only [Function.comp_def, div_eq_mul_inv, one_mul, id_eq] using
    (hf _).hasDerivAt.comp t (((hasDerivAt_id t).sub_const a).div_const b)


-- @@ L969-984 verbatim
lemma window_deriv (j : ℕ) (t : ℝ) :
    deriv (window j) t = (deriv ramp ((t-time j-pulse j)/pulse j) -
      deriv ramp ((t-time j-2*pulse j-dwell j)/pulse j)) / pulse j := by
  have hf := ramp_smooth.differentiable (by simp)
  have h1 := affine_composition_hasDerivAt hf (time j+pulse j) (pulse j) t
  have h2 := affine_composition_hasDerivAt hf (time j+2*pulse j+dwell j) (pulse j) t
  have hh : HasDerivAt (window j)
      (deriv ramp ((t-time j-pulse j)/pulse j) / pulse j -
        deriv ramp ((t-time j-2*pulse j-dwell j)/pulse j) / pulse j) t := by
    have hh := h1.sub h2
    change HasDerivAt (fun u => ramp ((u-(time j+pulse j))/pulse j) -
      ramp ((u-(time j+2*pulse j+dwell j))/pulse j)) _ _ at hh
    simp only [sub_add_eq_sub_sub] at hh
    exact hh
  rw [hh.deriv]
  ring


-- @@ L986-1006 verbatim
lemma window_deriv_two (j : ℕ) (t : ℝ) :
    deriv (deriv (window j)) t = (deriv (deriv ramp) ((t-time j-pulse j)/pulse j) -
      deriv (deriv ramp) ((t-time j-2*pulse j-dwell j)/pulse j)) / pulse j ^ 2 := by
  have hf := (contDiff_infty_iff_deriv.1 ramp_smooth).2.differentiable (by simp)
  have h1 := affine_composition_hasDerivAt hf (time j+pulse j) (pulse j) t
  have h2 := affine_composition_hasDerivAt hf (time j+2*pulse j+dwell j) (pulse j) t
  have he : deriv (window j) = fun u => (deriv ramp ((u-(time j+pulse j))/pulse j) -
      deriv ramp ((u-(time j+2*pulse j+dwell j))/pulse j)) / pulse j := by
    funext u
    rw [window_deriv]
    congr 2 <;> congr 1 <;> ring
  rw [he]
  have hh := ((h1.sub h2).div_const (pulse j)).deriv
  simp only [Pi.sub_apply, sub_add_eq_sub_sub] at hh
  rw [show (fun u => (deriv ramp ((u-(time j+pulse j))/pulse j) -
      deriv ramp ((u-(time j+2*pulse j+dwell j))/pulse j)) / pulse j) =
      (fun u => (deriv ramp ((u-time j-pulse j)/pulse j) -
      deriv ramp ((u-time j-2*pulse j-dwell j)/pulse j)) / pulse j) by
        simp only [sub_add_eq_sub_sub]]
  rw [hh]
  ring


-- @@ L1008-1019 verbatim
lemma increment_deriv {z : ℕ → ℝ → ℝ} (hz : ∀ j, ContDiff ℝ ∞ (z j))
    (qstar : ℝ) (j : ℕ) (t : ℝ) :
    deriv (increment z qstar j) t =
      deriv (z j) ((t-time j)/pulse j) / pulse j ^ 2 +
        (qstar-1)*deriv (window j) t := by
  have h1 := affine_composition_hasDerivAt ((hz j).differentiable (by simp))
    (time j) (pulse j) t
  have h2 := ((window_smooth j).differentiable (by simp) t).hasDerivAt
  have hh := (h1.const_mul (pulse j)⁻¹).add (h2.const_mul (qstar-1))
  change HasDerivAt (increment z qstar j) _ _ at hh
  rw [hh.deriv]
  ring


-- @@ L1021-1038 verbatim
lemma increment_deriv_two {z : ℕ → ℝ → ℝ} (hz : ∀ j, ContDiff ℝ ∞ (z j))
    (qstar : ℝ) (j : ℕ) (t : ℝ) :
    deriv (deriv (increment z qstar j)) t =
      deriv (deriv (z j)) ((t-time j)/pulse j) / pulse j ^ 3 +
        (qstar-1)*deriv (deriv (window j)) t := by
  have h1 := affine_composition_hasDerivAt
    ((contDiff_infty_iff_deriv.1 (hz j)).2.differentiable (by simp))
      (time j) (pulse j) t
  have h2 := ((contDiff_infty_iff_deriv.1 (window_smooth j)).2.differentiable (by simp) t).hasDerivAt
  have he : deriv (increment z qstar j) = fun u =>
      deriv (z j) ((u-time j)/pulse j) / pulse j ^ 2 + (qstar-1)*deriv (window j) u := by
    funext u; exact increment_deriv hz qstar j u
  rw [he]
  have hh := (h1.div_const (pulse j ^ 2)).add (h2.const_mul (qstar-1))
  change HasDerivAt (fun u => deriv (z j) ((u-time j)/pulse j) / pulse j ^ 2 +
    (qstar-1)*deriv (window j) u) _ _ at hh
  rw [hh.deriv]
  ring


-- @@ L1040-1049 verbatim
lemma profile_deriv_period {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (ht : t ∈ Set.Icc (time j) (time (j+1))) :
    deriv (profile z qstar j0) t = deriv (increment z qstar j) t := by
  have he : Set.EqOn (profile z qstar j0) (fun t => 1+increment z qstar j t)
      (Set.Icc (time j) (time (j+1))) := fun t ht => profile_period hz0 hz1 hj ht.1 ht.2
  have hd := deriv_eqOn_Icc (time_strictMono (Nat.lt_succ_self j))
    ((profile_smooth hs hz0 qstar j0).differentiable (by simp))
    ((contDiff_const.add (increment_smooth hs qstar j)).differentiable (by simp)) he ht
  simpa using hd


-- @@ L1051-1059 verbatim
lemma profile_deriv_two_period {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j) (ht : t ∈ Set.Icc (time j) (time (j+1))) :
    deriv (deriv (profile z qstar j0)) t = deriv (deriv (increment z qstar j)) t := by
  have he : Set.EqOn (deriv (profile z qstar j0)) (deriv (increment z qstar j))
      (Set.Icc (time j) (time (j+1))) := fun _ ht => profile_deriv_period hs hz0 hz1 hj ht
  exact deriv_eqOn_Icc (time_strictMono (Nat.lt_succ_self j))
    ((contDiff_infty_iff_deriv.1 (profile_smooth hs hz0 qstar j0)).2.differentiable (by simp))
    ((contDiff_infty_iff_deriv.1 (increment_smooth hs qstar j)).2.differentiable (by simp)) he ht


-- @@ L1061-1061 verbatim
end HarmonicCounterexample.Pulses


-- @@ L1063-1063 verbatim
end


-- @@ L1065-1065 verbatim
noncomputable section

-- @@ L1066-1066 verbatim
open Filter MeasureTheory

-- @@ L1067-1067 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1068-1068 verbatim
open Matrix

-- @@ L1069-1069 verbatim
open scoped BigOperators

-- @@ L1070-1070 verbatim
open Matrix

-- @@ L1071-1071 verbatim
open scoped BigOperators

-- @@ L1072-1072 verbatim
open Filter Matrix

-- @@ L1073-1073 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1074-1074 verbatim
open Filter MeasureTheory

-- @@ L1075-1075 verbatim
open scoped Topology ContDiff

-- @@ L1076-1076 verbatim
open Filter

-- @@ L1077-1077 verbatim
open scoped BigOperators Topology

-- @@ L1078-1078 verbatim
open Filter

-- @@ L1079-1079 verbatim
open scoped Topology


-- @@ L1081-1081 verbatim
namespace HarmonicCounterexample.Pulses

-- @@ L1082-1082 verbatim
open Schedule

-- @@ L1083-1083 verbatim
open scoped ContDiff


-- @@ L1085-1093 verbatim
lemma bounded_of_zero_outside {f : ℝ → ℝ} (hf : Continuous f)
    (hz : ∀ t, t ∉ Set.Icc (0:ℝ) 1 → f t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · exact (hC (Set.mem_image_of_mem _ ht)).trans (le_max_left _ _)
  · rw [hz t ht, abs_zero]
    exact le_max_right _ _


-- @@ L1095-1104 verbatim
lemma ramp_locally_constant {t : ℝ} (ht : t ∉ Set.Icc (0:ℝ) 1) :
    ∃ c : ℝ, ramp =ᶠ[𝓝 t] fun _ => c := by
  by_cases h : t < 0
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_lt_nhds (show t < 1/4 by linarith)] with u hu
    exact ramp_zero hu.le
  · have h' : 1 < t := by simp only [Set.mem_Icc, not_and_or, not_le] at ht; rcases ht with ht | ht <;> linarith
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_nhds (show 3/4 < t by linarith)] with u hu
    exact ramp_one hu.le


-- @@ L1106-1114 verbatim
lemma ramp_derivatives_bounded :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      (∀ t, |deriv ramp t| ≤ B1) ∧ (∀ t, |deriv (deriv ramp) t| ≤ B2) := by
  obtain ⟨B1, hB1, hb1⟩ := bounded_of_zero_outside (ramp_smooth.continuous_deriv (by simp))
    (fun t ht => by obtain ⟨c, hc⟩ := ramp_locally_constant ht; rw [hc.deriv_eq, deriv_const])
  obtain ⟨B2, hB2, hb2⟩ := bounded_of_zero_outside
    ((contDiff_infty_iff_deriv.1 ramp_smooth).2.continuous_deriv (by simp))
    (fun t ht => by obtain ⟨c, hc⟩ := ramp_locally_constant ht; rw [hc.deriv.deriv_eq]; simp)
  exact ⟨B1, B2, hB1, hB2, hb1, hb2⟩


-- @@ L1116-1120 verbatim
lemma pulse_one_le (j : ℕ) : 1 ≤ pulse j := by
  unfold pulse
  apply one_le_pow₀
  have h : (0:ℝ) ≤ j := Nat.cast_nonneg _
  linarith


-- @@ L1122-1129 verbatim
lemma window_deriv_bound {B : ℝ} (hB : ∀ t, |deriv ramp t| ≤ B) (j : ℕ) (t : ℝ) :
    |deriv (window j) t| ≤ 2*B/pulse j := by
  rw [window_deriv, abs_div, abs_of_pos (pulse_pos j)]
  apply div_le_div_of_nonneg_right _ (pulse_pos j).le
  exact (abs_sub _ _).trans (by
    have ha := hB ((t-time j-pulse j)/pulse j)
    have hb := hB ((t-time j-2*pulse j-dwell j)/pulse j)
    linarith)


-- @@ L1131-1138 verbatim
lemma window_deriv_two_bound {B : ℝ} (hB : ∀ t, |deriv (deriv ramp) t| ≤ B)
    (j : ℕ) (t : ℝ) : |deriv (deriv (window j)) t| ≤ 2*B/pulse j^2 := by
  rw [window_deriv_two, abs_div, abs_of_nonneg (sq_nonneg (pulse j))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (abs_sub _ _).trans (by
    have ha := hB ((t-time j-pulse j)/pulse j)
    have hb := hB ((t-time j-2*pulse j-dwell j)/pulse j)
    linarith)


-- @@ L1140-1158 verbatim
lemma increment_deriv_bound {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    {M B : ℝ} (hM : ∀ j t, |deriv (z j) t| ≤ M) (hB : ∀ t, |deriv ramp t| ≤ B)
    (qstar : ℝ) (j : ℕ) (t : ℝ) :
    |deriv (increment z qstar j) t| ≤ (M + 2*|qstar-1| *B) / pulse j := by
  have hm : 0 ≤ M := (abs_nonneg _).trans (hM j 0)
  have hp := pulse_pos j
  rw [increment_deriv hs]
  calc
    _ ≤ |deriv (z j) ((t-time j)/pulse j) / pulse j^2| +
        |(qstar-1)*deriv (window j) t| := abs_add_le _ _
    _ ≤ M/pulse j^2 + |qstar-1| *(2*B/pulse j) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (pulse j)), abs_mul]
      exact add_le_add (div_le_div_of_nonneg_right (hM j _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_left (window_deriv_bound hB j t) (abs_nonneg _))
    _ ≤ M/pulse j + |qstar-1| *(2*B/pulse j) := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_left hm hp
      nlinarith [pulse_one_le j]
    _ = _ := by ring


-- @@ L1160-1178 verbatim
lemma increment_deriv_two_bound {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    {M B : ℝ} (hM : ∀ j t, |deriv (deriv (z j)) t| ≤ M)
    (hB : ∀ t, |deriv (deriv ramp) t| ≤ B) (qstar : ℝ) (j : ℕ) (t : ℝ) :
    |deriv (deriv (increment z qstar j)) t| ≤ (M + 2*|qstar-1| *B) / pulse j^2 := by
  have hm : 0 ≤ M := (abs_nonneg _).trans (hM j 0)
  have hp := pulse_pos j
  rw [increment_deriv_two hs]
  calc
    _ ≤ |deriv (deriv (z j)) ((t-time j)/pulse j) / pulse j^3| +
        |(qstar-1)*deriv (deriv (window j)) t| := abs_add_le _ _
    _ ≤ M/pulse j^3 + |qstar-1| *(2*B/pulse j^2) := by
      rw [abs_div, abs_of_pos (pow_pos hp 3), abs_mul]
      exact add_le_add (div_le_div_of_nonneg_right (hM j _) (pow_nonneg hp.le _))
        (mul_le_mul_of_nonneg_left (window_deriv_two_bound hB j t) (abs_nonneg _))
    _ ≤ M/pulse j^2 + |qstar-1| *(2*B/pulse j^2) := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_left hm (sq_pos_of_pos hp)
      nlinarith [pulse_one_le j, sq_nonneg (pulse j-1)]
    _ = _ := by ring


-- @@ L1180-1197 verbatim
/-- The time derivatives are controlled uniformly on each CLOSED period, including
both joining points. Constants depend on the fixed pulse family, never its history. -/
theorem profile_derivative_bounds {z : ℕ → ℝ → ℝ} (hs : ∀ j, ContDiff ℝ ∞ (z j))
    (hz0 : ∀ j u, u ≤ 0 → z j u = 0) (hz1 : ∀ j u, 1 ≤ u → z j u = 0)
    {M1 M2 : ℝ} (hM1 : ∀ j t, |deriv (z j) t| ≤ M1)
    (hM2 : ∀ j t, |deriv (deriv (z j)) t| ≤ M2) (qstar : ℝ) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ j0 j, j0 ≤ j →
      ∀ t ∈ Set.Icc (time j) (time (j+1)),
        |deriv (profile z qstar j0) t| ≤ C1/pulse j ∧
        |deriv (deriv (profile z qstar j0)) t| ≤ C2/pulse j^2 := by
  obtain ⟨B1, B2, hB1, hB2, hb1, hb2⟩ := ramp_derivatives_bounded
  refine ⟨M1+2*|qstar-1| *B1, M2+2*|qstar-1| *B2, ?_, ?_, ?_⟩
  · exact add_nonneg ((abs_nonneg _).trans (hM1 0 0)) (by positivity)
  · exact add_nonneg ((abs_nonneg _).trans (hM2 0 0)) (by positivity)
  · intro j0 j hj t ht
    rw [profile_deriv_period hs hz0 hz1 hj ht, profile_deriv_two_period hs hz0 hz1 hj ht]
    exact ⟨increment_deriv_bound hs hM1 hb1 qstar j t,
      increment_deriv_two_bound hs hM2 hb2 qstar j t⟩


-- @@ L1199-1199 verbatim
end HarmonicCounterexample.Pulses


-- @@ L1201-1201 verbatim
end


-- @@ L1203-1203 verbatim
noncomputable section

-- @@ L1204-1204 verbatim
open Filter MeasureTheory

-- @@ L1205-1205 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1206-1206 verbatim
open Matrix

-- @@ L1207-1207 verbatim
open scoped BigOperators

-- @@ L1208-1208 verbatim
open Matrix

-- @@ L1209-1209 verbatim
open scoped BigOperators

-- @@ L1210-1210 verbatim
open Filter Matrix

-- @@ L1211-1211 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1212-1212 verbatim
open Filter MeasureTheory

-- @@ L1213-1213 verbatim
open scoped Topology ContDiff

-- @@ L1214-1214 verbatim
open Filter

-- @@ L1215-1215 verbatim
open scoped BigOperators Topology

-- @@ L1216-1216 verbatim
open Filter

-- @@ L1217-1217 verbatim
open scoped Topology


-- @@ L1219-1219 verbatim
namespace HarmonicCounterexample.Pulses

-- @@ L1220-1220 verbatim
open Schedule

-- @@ L1221-1221 verbatim
open scoped ContDiff


-- @@ L1223-1224 verbatim
/-- Half the logarithmic derivative of the volume-normalized Berger anisotropy. -/
def logSlope (q : ℝ → ℝ) (t : ℝ) : ℝ := deriv q t / (2*q t)


-- @@ L1226-1229 verbatim
lemma logSlope_smooth {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (hp : ∀ t, 0 < q t) :
    ContDiff ℝ ∞ (logSlope q) := by
  exact (contDiff_infty_iff_deriv.1 hq).2.div (contDiff_const.mul hq)
    (fun t => mul_ne_zero (by norm_num) (hp t).ne')


-- @@ L1231-1238 verbatim
lemma logSlope_deriv {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) {t : ℝ} (hp : q t ≠ 0) :
    deriv (logSlope q) t = deriv (deriv q) t/(2*q t) - (deriv q t)^2/(2*(q t)^2) := by
  have hq1 := (hq.differentiable (by simp) t).hasDerivAt
  have hq2 := ((contDiff_infty_iff_deriv.1 hq).2.differentiable (by simp) t).hasDerivAt
  have hh := hq2.div (hq1.const_mul 2) (mul_ne_zero (by norm_num) hp)
  change HasDerivAt (logSlope q) _ t at hh
  rw [hh.deriv]
  field_simp


-- @@ L1240-1244 verbatim
lemma logSlope_bound {q : ℝ → ℝ} {t P C : ℝ} (hq : 1/2 ≤ q t)
    (hd : |deriv q t| ≤ C/P) : |logSlope q t| ≤ C/P := by
  have hq0 : 0 < q t := by linarith
  rw [logSlope, abs_div, abs_of_pos (mul_pos (by norm_num) hq0)]
  exact (div_le_self (abs_nonneg _) (by linarith : 1 ≤ 2*q t)).trans hd


-- @@ L1246-1267 verbatim
lemma logSlope_deriv_bound {q : ℝ → ℝ} (hs : ContDiff ℝ ∞ q)
    {t P C1 C2 : ℝ} (hq : 1/2 ≤ q t)
    (hd1 : |deriv q t| ≤ C1/P) (hd2 : |deriv (deriv q) t| ≤ C2/P^2) :
    |deriv (logSlope q) t| ≤ (C2+2*C1^2)/P^2 := by
  have hq0 : 0 < q t := by linarith
  have hsq : (deriv q t)^2 ≤ (C1/P)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (deriv q t)) ((abs_nonneg _).trans hd1)).2 hd1
    simpa only [sq_abs] using hh
  have hfirst : |deriv (deriv q) t/(2*q t)| ≤ C2/P^2 := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hq0)]
    exact (div_le_self (abs_nonneg _) (by linarith : 1 ≤ 2*q t)).trans hd2
  have hsecond : |(deriv q t)^2/(2*(q t)^2)| ≤ 2*(C1/P)^2 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
    calc
      _ ≤ (deriv q t)^2/(1/2) := div_le_div_of_nonneg_left (sq_nonneg _)
        (by norm_num) (by nlinarith [sq_nonneg (q t-1/2)])
      _ ≤ 2*(C1/P)^2 := by nlinarith
  rw [logSlope_deriv hs hq0.ne']
  calc
    _ ≤ |deriv (deriv q) t/(2*q t)| + |(deriv q t)^2/(2*(q t)^2)| := abs_sub _ _
    _ ≤ C2/P^2+2*(C1/P)^2 := add_le_add hfirst hsecond
    _ = _ := by ring


-- @@ L1269-1269 verbatim
end HarmonicCounterexample.Pulses


-- @@ L1271-1271 verbatim
end


-- @@ L1273-1273 verbatim
noncomputable section

-- @@ L1274-1274 verbatim
open Filter MeasureTheory

-- @@ L1275-1275 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1276-1276 verbatim
open Matrix

-- @@ L1277-1277 verbatim
open scoped BigOperators

-- @@ L1278-1278 verbatim
open Matrix

-- @@ L1279-1279 verbatim
open scoped BigOperators

-- @@ L1280-1280 verbatim
open Filter Matrix

-- @@ L1281-1281 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1282-1282 verbatim
open Filter MeasureTheory

-- @@ L1283-1283 verbatim
open scoped Topology ContDiff

-- @@ L1284-1284 verbatim
open Filter

-- @@ L1285-1285 verbatim
open scoped BigOperators Topology

-- @@ L1286-1286 verbatim
open Filter

-- @@ L1287-1287 verbatim
open scoped Topology


-- @@ L1289-1289 verbatim
namespace HarmonicCounterexample.Schedule


-- @@ L1291-1310 verbatim
lemma time_succ_upper (j : ℕ) : time (j+1) ≤ 15*(j+1:ℝ)^8 := by
  have hj : (1:ℝ) ≤ j+1 := by have h := Nat.cast_nonneg (α := ℝ) j; linarith
  have hpow : (1:ℝ) ≤ (j+1:ℝ)^8 := one_le_pow₀ hj
  have hsum : (∑ i ∈ Finset.range (j+1), (dwell i+4*pulse i)) ≤
      (j+1:ℝ)*(5*(j+1:ℝ)^7) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (j+1), 5*(j+1:ℝ)^7 := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : (i+1:ℝ) ≤ j+1 := by exact_mod_cast (Nat.succ_le_iff.2 (Finset.mem_range.1 hi))
        have hp7 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ i+1) hij 7
        have hp6 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ i+1) hij 6
        have hp67 := pow_le_pow_right₀ hj (by omega : 6 ≤ 7)
        dsimp [dwell, pulse]
        nlinarith
      _ = _ := by simp
  unfold time
  have he : (j+1:ℝ)*(5*(j+1:ℝ)^7) = 5*(j+1:ℝ)^8 := by ring
  rw [he] at hsum
  linarith


-- @@ L1312-1327 verbatim
lemma period_weight_bound {j : ℕ} {t : ℝ} (ht : 0 ≤ t) (hjt : t ≤ time (j+1)) :
    (1+t)^(5/4:ℝ) ≤ 32*(j+1:ℝ)^10 := by
  have hx : 0 ≤ (j+1:ℝ) := by positivity
  have h1 : (1:ℝ) ≤ (j+1:ℝ)^8 := one_le_pow₀ (by have h := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hb := time_succ_upper j
  have he : (16*(j+1:ℝ)^8)^(5/4:ℝ) = 32*(j+1:ℝ)^10 := by
    rw [Real.mul_rpow (by norm_num) (pow_nonneg hx _)]
    have h16 : (16:ℝ)^(5/4:ℝ) = 32 := by
      rw [show (16:ℝ) = 2^4 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    have hjp : ((j+1:ℝ)^8)^(5/4:ℝ) = (j+1:ℝ)^10 := by
      rw [← Real.rpow_natCast_mul hx]
      norm_num
    rw [h16, hjp]
  rw [← he]
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)


-- @@ L1329-1329 verbatim
end HarmonicCounterexample.Schedule


-- @@ L1331-1331 verbatim
end


-- @@ L1333-1333 verbatim
noncomputable section

-- @@ L1334-1334 verbatim
open Filter MeasureTheory

-- @@ L1335-1335 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1336-1336 verbatim
open Matrix

-- @@ L1337-1337 verbatim
open scoped BigOperators

-- @@ L1338-1338 verbatim
open Matrix

-- @@ L1339-1339 verbatim
open scoped BigOperators

-- @@ L1340-1340 verbatim
open Filter Matrix

-- @@ L1341-1341 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1342-1342 verbatim
open Filter MeasureTheory

-- @@ L1343-1343 verbatim
open scoped Topology ContDiff

-- @@ L1344-1344 verbatim
open Filter

-- @@ L1345-1345 verbatim
open scoped BigOperators Topology

-- @@ L1346-1346 verbatim
open Filter

-- @@ L1347-1347 verbatim
open scoped Topology


-- @@ L1349-1349 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L1350-1350 verbatim
open Schedule


-- @@ L1352-1370 verbatim
lemma scale_margin_on_period {μ t : ℝ} {j : ℕ}
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (ht : t ∈ Set.Icc (time j) (time (j+1))) :
    Scale.slope μ t + deriv (Scale.slope μ) t + Scale.slope μ t ^ 2 ≤
      -μ/(64*(j+1:ℝ)^10) := by
  have hj : 10 ≤ time j := by
    unfold time
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      add_nonneg (Pulses.dwell_pos i).le (mul_nonneg (by norm_num) (Pulses.pulse_pos i).le))
  have ht0 : 0 < 1+t := by linarith [ht.1]
  have hm := Scale.radial_tail_margin hμ hμ1 (show 4 ≤ t by linarith [ht.1])
  have hw := period_weight_bound (show 0 ≤ t by linarith [ht.1]) ht.2
  have hi : 1/(32*(j+1:ℝ)^10) ≤ (1+t)^(-5/4:ℝ) := by
    rw [show (-5/4:ℝ) = -(5/4:ℝ) by ring, Real.rpow_neg ht0.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos ht0 _) hw
  have hh := mul_le_mul_of_nonpos_left hi (show -(μ/2) ≤ 0 by linarith)
  have he : -(μ/2)*(1/(32*(j+1:ℝ)^10)) = -μ/(64*(j+1:ℝ)^10) := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  exact hm.trans (he ▸ hh)


-- @@ L1372-1387 verbatim
/-- A single late index absorbs the entire radial curvature cost uniformly in
all subsequent controls satisfying the fixed derivative bound. -/
theorem radial_budget_index {m μ C : ℝ} (hm : 1 ≤ m) (hμ : 0 < μ) :
    ∃ J : ℕ, ∀ j ≥ J, 64*C^2 ≤ m*μ*(j+1:ℝ)^2 := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (64*C^2/(m*μ))
  refine ⟨J, fun j hj => ?_⟩
  have hpos : 0 < m*μ := mul_pos (by linarith) hμ
  have hcast : (J:ℝ) ≤ j := by exact_mod_cast hj
  have hlarge : 64*C^2 ≤ m*μ*(j+1:ℝ) := by
    have hdiv : 64*C^2/(m*μ) ≤ j+1 := by linarith
    have hh := (div_le_iff₀ hpos).1 hdiv
    nlinarith only [hh]
  have hpow : (j+1:ℝ) ≤ (j+1:ℝ)^2 := by
    have hn := Nat.cast_nonneg (α := ℝ) j
    nlinarith
  exact hlarge.trans (mul_le_mul_of_nonneg_left hpow hpos.le)


-- @@ L1389-1402 verbatim
theorem radialRicci_of_pulse_budget {m μ C : ℝ} (hm : 1 ≤ m)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1/4) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ (q : ℝ → ℝ) (t : ℝ),
      1/2 ≤ q t → |deriv q t| ≤ C/pulse j →
      t ∈ Set.Icc (time j) (time (j+1)) →
      0 ≤ radialRicciNumerator (m+1)
        (Scale.slope μ t-Pulses.logSlope q t/m) (Pulses.logSlope q t)
        (deriv (Scale.slope μ) t-deriv (Pulses.logSlope q) t/m)
        (deriv (Pulses.logSlope q) t) := by
  obtain ⟨J,hJ⟩ := radial_budget_index (C := C) hm hμ
  refine ⟨J, fun j hj q t hq hd ht => ?_⟩
  apply radial_scalar_budget hm (by positivity : 0 < (j+1:ℝ)) (hJ j hj)
    (scale_margin_on_period hμ.le hμ1 ht)
  exact Pulses.logSlope_bound hq hd


-- @@ L1404-1404 verbatim
end HarmonicCounterexample.Berger


-- @@ L1406-1406 verbatim
end


-- @@ L1408-1408 verbatim
noncomputable section

-- @@ L1409-1409 verbatim
open Filter MeasureTheory

-- @@ L1410-1410 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1411-1411 verbatim
open Matrix

-- @@ L1412-1412 verbatim
open scoped BigOperators

-- @@ L1413-1413 verbatim
open Matrix

-- @@ L1414-1414 verbatim
open scoped BigOperators

-- @@ L1415-1415 verbatim
open Filter Matrix

-- @@ L1416-1416 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1417-1417 verbatim
open Filter MeasureTheory

-- @@ L1418-1418 verbatim
open scoped Topology ContDiff

-- @@ L1419-1419 verbatim
open Filter

-- @@ L1420-1420 verbatim
open scoped BigOperators Topology

-- @@ L1421-1421 verbatim
open Filter

-- @@ L1422-1422 verbatim
open scoped Topology


-- @@ L1424-1424 verbatim
namespace HarmonicCounterexample.Berger


-- @@ L1426-1430 verbatim
/-- The two tangent Ricci eigenvalues as continuous functions of the six scalar
profile jets. The harmless positive clamp is inactive wherever q≥1/2. -/
def tangentH (m : ℝ) (X : Fin 6 → ℝ) : ℝ :=
  horizontalRicciNumerator (m+1) (X 0 ^ 2 * (max (X 1) (1/4))^(-1/m))
    (X 1) (X 2-X 4/m) (X 4) (X 3-X 5/m)

-- @@ L1431-1433 verbatim
def tangentV (m : ℝ) (X : Fin 6 → ℝ) : ℝ :=
  verticalRicciNumerator (m+1) (X 0 ^ 2 * (max (X 1) (1/4))^(-1/m))
    (X 1) (X 2-X 4/m) (X 4) (X 3-X 5/m) (X 5)


-- @@ L1435-1440 verbatim
lemma tangentH_continuous (m : ℝ) : Continuous (tangentH m) := by
  have hp : Continuous (fun X : Fin 6 → ℝ => (max (X 1) (1/4))^(-1/m)) :=
    ((continuous_apply 1).max continuous_const).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))))
  unfold tangentH horizontalRicciNumerator
  fun_prop


-- @@ L1442-1447 verbatim
lemma tangentV_continuous (m : ℝ) : Continuous (tangentV m) := by
  have hp : Continuous (fun X : Fin 6 → ℝ => (max (X 1) (1/4))^(-1/m)) :=
    ((continuous_apply 1).max continuous_const).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))))
  unfold tangentV verticalRicciNumerator
  fun_prop


-- @@ L1449-1449 verbatim
def staticJet (a q : ℝ) : Fin 6 → ℝ := ![a,q,0,0,0,0]


-- @@ L1451-1454 verbatim
lemma staticJet_continuous (a : ℝ) : Continuous (staticJet a) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [staticJet] <;> fun_prop


-- @@ L1456-1460 verbatim
lemma staticH {m a q : ℝ} (hq : 1 ≤ q) :
    tangentH m (staticJet a q) = m+1-2*q-(m-1)*a^2*q^(-1/m) := by
  simp [tangentH, staticJet, horizontalRicciNumerator]
  rw [max_eq_left (by linarith : (4:ℝ)⁻¹ ≤ q)]
  ring


-- @@ L1462-1466 verbatim
lemma staticV {m a q : ℝ} (hq : 1 ≤ q) :
    tangentV m (staticJet a q) = (m-1)*q*(q-a^2*q^(-1/m)) := by
  simp [tangentV, staticJet, verticalRicciNumerator]
  rw [max_eq_left (by linarith : (4:ℝ)⁻¹ ≤ q)]
  ring


-- @@ L1468-1487 verbatim
/-- The strict link margin yields a uniform open neighborhood of positive
horizontal and vertical Ricci jets along the ENTIRE compact Berger segment. -/
theorem tangent_budget_tube {m a qstar : ℝ}
    (hH : ∀ q ∈ Set.Icc 1 qstar, 0 < m+1-2*q-(m-1)*a^2*q^(-1/m))
    (hV : ∀ q ∈ Set.Icc 1 qstar, 0 < (m-1)*q*(q-a^2*q^(-1/m))) :
    ∃ δ > 0, ∀ (X : Fin 6 → ℝ) (q : ℝ), q ∈ Set.Icc 1 qstar →
      dist X (staticJet a q) < δ → 0 < tangentH m X ∧ 0 < tangentV m X := by
  let K := staticJet a '' Set.Icc 1 qstar
  let U := {X | 0 < tangentH m X} ∩ {X | 0 < tangentV m X}
  have hK : IsCompact K := isCompact_Icc.image (staticJet_continuous a)
  have hU : IsOpen U := (isOpen_lt continuous_const (tangentH_continuous m)).inter
    (isOpen_lt continuous_const (tangentV_continuous m))
  have hKU : K ⊆ U := by
    rintro _ ⟨q,hq,rfl⟩
    change 0 < tangentH m (staticJet a q) ∧ 0 < tangentV m (staticJet a q)
    rw [staticH hq.1, staticV hq.1]
    exact ⟨hH q hq, hV q hq⟩
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ,hδ,fun X q hq hd => hsub ?_⟩
  exact Metric.mem_thickening_iff.2 ⟨staticJet a q,⟨q,hq,rfl⟩,hd⟩


-- @@ L1489-1497 verbatim
/-- Positivity of the vertical static margin follows directly from a<1. -/
lemma static_vertical_margin {m a q : ℝ} (hm : 1 < m) (ha : a^2 < 1) (hq : 1 ≤ q) :
    0 < (m-1)*q*(q-a^2*q^(-1/m)) := by
  have hqp : 0 < q := by linarith
  have hexp : -1/m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
  have hr : q^(-1/m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq hexp
  have hprod : a^2*q^(-1/m) < 1 :=
    (mul_le_mul_of_nonneg_left hr (sq_nonneg a)).trans_lt (by simpa using ha)
  exact mul_pos (mul_pos (by linarith) hqp) (by linarith)


-- @@ L1499-1499 verbatim
end HarmonicCounterexample.Berger


-- @@ L1501-1501 verbatim
end


-- @@ L1503-1503 verbatim
noncomputable section

-- @@ L1504-1504 verbatim
open Filter MeasureTheory

-- @@ L1505-1505 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1506-1506 verbatim
open Matrix

-- @@ L1507-1507 verbatim
open scoped BigOperators

-- @@ L1508-1508 verbatim
open Matrix

-- @@ L1509-1509 verbatim
open scoped BigOperators

-- @@ L1510-1510 verbatim
open Filter Matrix

-- @@ L1511-1511 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1512-1512 verbatim
open Filter MeasureTheory

-- @@ L1513-1513 verbatim
open scoped Topology ContDiff

-- @@ L1514-1514 verbatim
open Filter

-- @@ L1515-1515 verbatim
open scoped BigOperators Topology

-- @@ L1516-1516 verbatim
open Filter

-- @@ L1517-1517 verbatim
open scoped Topology


-- @@ L1519-1519 verbatim
namespace HarmonicCounterexample.Berger


-- @@ L1521-1544 verbatim
theorem tangent_budget_coordinates {m a qstar : ℝ}
    (hH : ∀ q ∈ Set.Icc 1 qstar, 0 < m+1-2*q-(m-1)*a^2*q^(-1/m))
    (hV : ∀ q ∈ Set.Icc 1 qstar, 0 < (m-1)*q*(q-a^2*q^(-1/m))) :
    ∃ δ > 0, ∀ (a' q b bd p pd q0 : ℝ), q0 ∈ Set.Icc 1 qstar →
      1/2 ≤ q → |a'-a| < δ → |q-q0| < δ →
      |b| < δ → |bd| < δ → |p| < δ → |pd| < δ →
      0 < horizontalRicciNumerator (m+1) (a'^2*q^(-1/m)) q (b-p/m) p (bd-pd/m) ∧
      0 < verticalRicciNumerator (m+1) (a'^2*q^(-1/m)) q (b-p/m) p (bd-pd/m) pd := by
  obtain ⟨δ,hδ,hh⟩ := tangent_budget_tube hH hV
  refine ⟨δ,hδ,fun a' q b bd p pd q0 hq0 hq ha hdq hb hbd hp hpd => ?_⟩
  have hd : dist ![a',q,b,bd,p,pd] (staticJet a q0) < δ := by
    apply (dist_pi_lt_iff hδ).2
    intro i
    fin_cases i
    · simpa [staticJet, Real.dist_eq] using ha
    · simpa [staticJet, Real.dist_eq] using hdq
    · simpa [staticJet, Real.dist_eq] using hb
    · simpa [staticJet, Real.dist_eq] using hbd
    · simpa [staticJet, Real.dist_eq] using hp
    · simpa [staticJet, Real.dist_eq] using hpd
  have he := hh ![a',q,b,bd,p,pd] q0 hq0 hd
  dsimp [tangentH, tangentV] at he
  rw [max_eq_left (by linarith : (1:ℝ)/4 ≤ q)] at he
  exact he


-- @@ L1546-1555 verbatim
/-- Any anisotropy in an epsilon enlargement of the closed dwell segment is
within epsilon of an actual point of that segment. -/
lemma clamp_segment {qstar q ε : ℝ} (hqstar : 1 ≤ qstar)
    (hlo : 1-ε ≤ q) (hhi : q ≤ qstar+ε) (he : 0 ≤ ε) :
    ∃ q0 ∈ Set.Icc 1 qstar, |q-q0| ≤ ε := by
  by_cases hq : q < 1
  · exact ⟨1,⟨le_rfl,hqstar⟩,by rw [abs_of_nonpos (by linarith : q-1 ≤ 0)]; linarith⟩
  · by_cases hq' : q ≤ qstar
    · exact ⟨q,⟨le_of_not_gt hq,hq'⟩,by simpa using he⟩
    · exact ⟨qstar,⟨hqstar,le_rfl⟩,by rw [abs_of_nonneg (by linarith : 0 ≤ q-qstar)]; linarith⟩


-- @@ L1557-1557 verbatim
end HarmonicCounterexample.Berger


-- @@ L1559-1559 verbatim
end


-- @@ L1561-1561 verbatim
noncomputable section

-- @@ L1562-1562 verbatim
open Filter MeasureTheory

-- @@ L1563-1563 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1564-1564 verbatim
open Matrix

-- @@ L1565-1565 verbatim
open scoped BigOperators

-- @@ L1566-1566 verbatim
open Matrix

-- @@ L1567-1567 verbatim
open scoped BigOperators

-- @@ L1568-1568 verbatim
open Filter Matrix

-- @@ L1569-1569 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1570-1570 verbatim
open Filter MeasureTheory

-- @@ L1571-1571 verbatim
open scoped Topology ContDiff

-- @@ L1572-1572 verbatim
open Filter

-- @@ L1573-1573 verbatim
open scoped BigOperators Topology

-- @@ L1574-1574 verbatim
open Filter

-- @@ L1575-1575 verbatim
open scoped Topology


-- @@ L1577-1577 verbatim
namespace HarmonicCounterexample.Schedule


-- @@ L1579-1582 verbatim
lemma pulse_atTop_limit : Tendsto pulse atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp
    (tendsto_atTop_mono (fun j : ℕ => show (j:ℝ) ≤ (j:ℝ)+1 by linarith)
      tendsto_natCast_atTop_atTop)


-- @@ L1584-1587 verbatim
lemma pulse_reciprocal_limit (C : ℝ) :
    Tendsto (fun j => C/pulse j) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
    (tendsto_inv_atTop_zero.comp pulse_atTop_limit).const_mul C


-- @@ L1589-1592 verbatim
lemma pulse_reciprocal_square_limit (C : ℝ) :
    Tendsto (fun j => C/(pulse j)^2) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, Function.comp_apply, inv_pow, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
    ((tendsto_inv_atTop_zero.comp pulse_atTop_limit).pow 2).const_mul C


-- @@ L1594-1594 verbatim
end HarmonicCounterexample.Schedule


-- @@ L1596-1596 verbatim
end


-- @@ L1598-1598 verbatim
noncomputable section

-- @@ L1599-1599 verbatim
open Filter MeasureTheory

-- @@ L1600-1600 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1601-1601 verbatim
open Matrix

-- @@ L1602-1602 verbatim
open scoped BigOperators

-- @@ L1603-1603 verbatim
open Matrix

-- @@ L1604-1604 verbatim
open scoped BigOperators

-- @@ L1605-1605 verbatim
open Filter Matrix

-- @@ L1606-1606 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1607-1607 verbatim
open Filter MeasureTheory

-- @@ L1608-1608 verbatim
open scoped Topology ContDiff

-- @@ L1609-1609 verbatim
open Filter

-- @@ L1610-1610 verbatim
open scoped BigOperators Topology

-- @@ L1611-1611 verbatim
open Filter

-- @@ L1612-1612 verbatim
open scoped Topology


-- @@ L1614-1614 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L1615-1615 verbatim
open Schedule


-- @@ L1617-1662 verbatim
/-- Uniform tangent curvature budget, independent of the later control sequence.
All hypotheses concerning q are the bounds already proved for the actual pulse
profile; the smallness index is produced from the fixed scale and fixed family. -/
theorem tangentRicci_of_pulse_budget {m a μ qstar M C1 C2 : ℝ}
    (hM : 0 ≤ M) (hqstar : 1 ≤ qstar)
    (ha : Tendsto (Scale.profile μ) atTop (𝓝 a))
    (hH : ∀ q ∈ Set.Icc 1 qstar, 0 < m+1-2*q-(m-1)*a^2*q^(-1/m))
    (hV : ∀ q ∈ Set.Icc 1 qstar, 0 < (m-1)*q*(q-a^2*q^(-1/m))) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ (q : ℝ → ℝ) (t : ℝ),
      ContDiff ℝ ∞ q → 1/2 ≤ q t →
      1-M/pulse j ≤ q t → q t ≤ qstar+M/pulse j →
      |deriv q t| ≤ C1/pulse j → |deriv (deriv q) t| ≤ C2/(pulse j)^2 →
      time j ≤ t →
      0 < horizontalRicciNumerator (m+1)
        ((Scale.profile μ t)^2*(q t)^(-1/m)) (q t)
        (Scale.slope μ t-Pulses.logSlope q t/m) (Pulses.logSlope q t)
        (deriv (Scale.slope μ) t-deriv (Pulses.logSlope q) t/m) ∧
      0 < verticalRicciNumerator (m+1)
        ((Scale.profile μ t)^2*(q t)^(-1/m)) (q t)
        (Scale.slope μ t-Pulses.logSlope q t/m) (Pulses.logSlope q t)
        (deriv (Scale.slope μ) t-deriv (Pulses.logSlope q) t/m)
        (deriv (Pulses.logSlope q) t) := by
  obtain ⟨δ,hδ,hδgood⟩ := tangent_budget_coordinates hH hV
  have hscale : ∀ᶠ t in atTop,
      |Scale.profile μ t-a| < δ ∧ |Scale.slope μ t| < δ ∧ |deriv (Scale.slope μ) t| < δ := by
    have h1 := ha.eventually (Metric.ball_mem_nhds a hδ)
    have h2 := (Scale.slope_limit μ).eventually (Metric.ball_mem_nhds 0 hδ)
    have h3 := (Scale.slope_deriv_limit μ).eventually (Metric.ball_mem_nhds 0 hδ)
    filter_upwards [h1,h2,h3] with t ht1 ht2 ht3
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using And.intro ht1 (And.intro ht2 ht3)
  obtain ⟨T,hT⟩ := eventually_atTop.1 hscale
  have hjlarge : ∀ᶠ j in atTop, T ≤ time j ∧ M/pulse j < δ ∧
      C1/pulse j < δ ∧ (C2+2*C1^2)/(pulse j)^2 < δ := by
    filter_upwards [time_atTop.eventually (eventually_ge_atTop T),
      (pulse_reciprocal_limit M).eventually (eventually_lt_nhds hδ),
      (pulse_reciprocal_limit C1).eventually (eventually_lt_nhds hδ),
      (pulse_reciprocal_square_limit (C2+2*C1^2)).eventually (eventually_lt_nhds hδ)] with j ht h0 h1 h2
    exact ⟨ht,h0,h1,h2⟩
  obtain ⟨J,hJ⟩ := eventually_atTop.1 hjlarge
  refine ⟨J,fun j hj q t hqs hq hlo hhi hd1 hd2 ht => ?_⟩
  rcases hJ j hj with ⟨htime,h0,h1,h2⟩
  obtain ⟨q0,hq0,hqdist⟩ := clamp_segment hqstar hlo hhi (div_nonneg hM (Pulses.pulse_pos j).le)
  rcases hT t (htime.trans ht) with ⟨hat,hbt,hbdt⟩
  exact hδgood _ _ _ _ _ _ _ hq0 hq hat (hqdist.trans_lt h0) hbt hbdt
    ((Pulses.logSlope_bound hq hd1).trans_lt h1)
    ((Pulses.logSlope_deriv_bound hqs hq hd1 hd2).trans_lt h2)


-- @@ L1664-1664 verbatim
end HarmonicCounterexample.Berger


-- @@ L1666-1666 verbatim
end


-- @@ L1668-1668 verbatim
noncomputable section

-- @@ L1669-1669 verbatim
open Filter MeasureTheory

-- @@ L1670-1670 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1671-1671 verbatim
open Matrix

-- @@ L1672-1672 verbatim
open scoped BigOperators

-- @@ L1673-1673 verbatim
open Matrix

-- @@ L1674-1674 verbatim
open scoped BigOperators

-- @@ L1675-1675 verbatim
open Filter Matrix

-- @@ L1676-1676 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1677-1677 verbatim
open Filter MeasureTheory

-- @@ L1678-1678 verbatim
open scoped Topology ContDiff

-- @@ L1679-1679 verbatim
open Filter

-- @@ L1680-1680 verbatim
open scoped BigOperators Topology

-- @@ L1681-1681 verbatim
open Filter

-- @@ L1682-1682 verbatim
open scoped Topology


-- @@ L1684-1684 verbatim
namespace HarmonicCounterexample

-- @@ L1685-1685 verbatim
open Matrix

-- @@ L1686-1686 verbatim
variable {n : ℕ}


-- @@ L1688-1694 verbatim
lemma christoffel_eq_zero_of_locallyConstant (g : SmoothMetric n) {x : Space n} {M : Mat n}
    (hg : ∀ᶠ y in 𝓝 x, g.coeff y = M) (k i j : Fin n) :
    christoffel g x k i j = 0 := by
  have hd (l i j : Fin n) : coordDeriv l (fun y => g.coeff y i j) x = 0 := by
    rw [coordDeriv_congr (hf := hg.mono fun y hy => congrFun (congrFun hy i) j) l]
    exact coordDeriv_const _ _ _
  simp only [christoffel, hd, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]


-- @@ L1696-1703 verbatim
lemma ricci_eq_zero_of_locallyConstant (g : SmoothMetric n) {x : Space n} {M : Mat n}
    (hg : ∀ᶠ y in 𝓝 x, g.coeff y = M) (i j : Fin n) : ricci g x i j = 0 := by
  have hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g y k i j = 0 :=
    hg.eventually_nhds.mono fun y hy k i j => christoffel_eq_zero_of_locallyConstant g hy k i j
  have hd (l k i j : Fin n) : coordDeriv l (fun y => christoffel g y k i j) x = 0 := by
    rw [coordDeriv_congr (hf := hΓ.mono fun y hy => hy k i j) l]
    exact coordDeriv_const _ _ _
  simp only [ricci, hd, hΓ.self_of_nhds, sub_self, Finset.sum_const_zero, mul_zero, add_zero]


-- @@ L1705-1705 verbatim
end HarmonicCounterexample


-- @@ L1707-1707 verbatim
end


-- @@ L1709-1709 verbatim
noncomputable section

-- @@ L1710-1710 verbatim
open Filter MeasureTheory

-- @@ L1711-1711 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1712-1712 verbatim
open Matrix

-- @@ L1713-1713 verbatim
open scoped BigOperators

-- @@ L1714-1714 verbatim
open Matrix

-- @@ L1715-1715 verbatim
open scoped BigOperators

-- @@ L1716-1716 verbatim
open Filter Matrix

-- @@ L1717-1717 verbatim
open scoped BigOperators Topology ContDiff

-- @@ L1718-1718 verbatim
open Filter MeasureTheory

-- @@ L1719-1719 verbatim
open scoped Topology ContDiff

-- @@ L1720-1720 verbatim
open Filter

-- @@ L1721-1721 verbatim
open scoped BigOperators Topology

-- @@ L1722-1722 verbatim
open Filter

-- @@ L1723-1723 verbatim
open scoped Topology


-- @@ L1725-1725 verbatim
namespace HarmonicCounterexample.Cartesian

-- @@ L1726-1726 verbatim
open Matrix Berger

-- @@ L1727-1727 verbatim
variable {n : ℕ}


-- @@ L1729-1741 verbatim
lemma rawCoefficient_locally_fixed (c q : ℝ → ℝ) (J : ℝ → ComplexStructure (Fin n))
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {x : Space n} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, rawCoefficient c q J y = tensor (radialUnit y)
      (hopfUnit (J (logRadius x)) y) (c (logRadius y)) (q (logRadius y)) := by
  have hne : ∀ᶠ y : Space n in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hx
  rcases hJ (logRadius x) with hconst | hround
  · have h := (logRadius_smoothAt hx).continuousAt.eventually hconst
    filter_upwards [hne, h] with y hy hJy
    simp only [rawCoefficient, ite_eq_right hy, hJy]
  · have h := (logRadius_smoothAt hx).continuousAt.eventually hround
    filter_upwards [hne, h] with y hy hqy
    simp [rawCoefficient, hy, hqy, tensor]


-- @@ L1743-1776 verbatim
/-- Genuine global Ricci positivity of the constructed smooth metric from the
three exact scalar eigenvalue inequalities. The origin and all switching gaps
are included; no differentiability of the label function is required. -/
theorem bergerMetric_ricciNonnegative (c q u v : ℝ → ℝ)
    (J : ℝ → ComplexStructure (Fin n))
    (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (hcp : ∀ t, 0 < c t) (hqp : ∀ t, 0 < q t)
    (hJ : ∀ t, (∀ᶠ s in 𝓝 t, J s = J t) ∨ (∀ᶠ s in 𝓝 t, q s = 1))
    {T : ℝ} (hc0 : ∀ t ≤ T, c t = 1) (hq0 : ∀ t ≤ T, q t = 1)
    (hdc : ∀ t, HasDerivAt c (2*c t*u t) t)
    (hdq : ∀ t, HasDerivAt q (2*q t*v t) t)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hR : ∀ t, 0 ≤ radialRicciNumerator n (u t) (v t) (deriv u t) (deriv v t))
    (hH : ∀ t, 0 ≤ horizontalRicciNumerator n (c t) (q t) (u t) (v t) (deriv u t))
    (hV : ∀ t, 0 ≤ verticalRicciNumerator n (c t) (q t) (u t) (v t) (deriv u t) (deriv v t)) :
    RicciNonnegative (bergerMetric c q J hc hq hcp hqp hJ hc0 hq0) := by
  let g := bergerMetric c q J hc hq hcp hqp hJ hc0 hq0
  intro x w
  by_cases hx : x = 0
  · subst x
    have he : ∀ᶠ y : Space n in 𝓝 0, radius y < Real.exp T :=
      (radius_continuous.tendsto 0).eventually (eventually_lt_nhds (by simpa using Real.exp_pos T))
    have hflat : ∀ᶠ y : Space n in 𝓝 0, g.coeff y = 1 :=
      he.mono fun y hy => rawCoefficient_euclidean c q J hc0 hq0 hy
    have hzero := ricci_eq_zero_of_locallyConstant g hflat
    change 0 ≤ ∑ i, ∑ j, ricci g 0 i j*w i*w j
    simp only [hzero, zero_mul, Finset.sum_const_zero, le_refl]
  · have hr (i j : Fin n) := ricci_logProfiles g (J (logRadius x)) hx
      (rawCoefficient_locally_fixed c q J hJ hx) hdc hdq
      (fun t => (hcp t).ne') (fun t => (hqp t).ne')
      (hu (logRadius x)).hasDerivAt (hv (logRadius x)).hasDerivAt i j
    change 0 ≤ ∑ i, ∑ j, ricci g x i j*w i*w j
    simp only [hr]
    exact polarCoefficients_nonnegative (J (logRadius x)) hx (hH _) (hR _) (hV _) w


-- @@ L1778-1778 verbatim
end HarmonicCounterexample.Cartesian


-- @@ L1780-1780 verbatim
end


-- @@ L1782-1782 verbatim
end OAI
