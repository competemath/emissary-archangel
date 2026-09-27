/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FuturePressureBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.ConeAlgebra
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone


-- @@ L14-19 verbatim
/-!
# Actual outgoing histories through the axial drop

All lags below include the ideal incoming history. The scalar averages are
integrals of the constructed schedule, and no cone estimate is assumed.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace NavierStokes.OutgoingEntranceCone


-- @@ L28-28 verbatim
open Set Filter MeasureTheory

-- @@ L29-29 verbatim
open scoped Topology ContDiff

-- @@ L30-30 verbatim
open OutgoingSchedule OutgoingTail NaturalAxisData


-- @@ L32-41 verbatim
theorem integral_exp_mul_real {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, Real.exp (a * t)) = (Real.exp (a * y) - 1) / a := by
  have hd : ∀ t, HasDerivAt (fun x => Real.exp (a * x) / a) (Real.exp (a * t)) t := by
    intro t
    convert! (((hasDerivAt_id t).const_mul a).exp).div_const a using 1
    simp only [id_eq]
    field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 y)
  simpa only [mul_zero, Real.exp_zero, sub_div] using hi


-- @@ L43-45 verbatim
/-- Exponential averaging with the actual incoming history at clock zero. -/
noncomputable def historyAverage (b : ℝ → ℝ) (b₀ y : ℝ) : ℝ :=
  linearLag (fun _ => 1) b b₀ y


-- @@ L47-50 verbatim
theorem historyAverage_formula (b : ℝ → ℝ) (b₀ y : ℝ) :
    historyAverage b b₀ y = Real.exp (-y) *
      (b₀ + ∫ t in (0 : ℝ)..y, Real.exp t * b t) := by
  simp [historyAverage, linearLag, OutgoingSchedule.primitive]


-- @@ L52-53 verbatim
theorem historyAverage_initial (b : ℝ → ℝ) (b₀ : ℝ) : historyAverage b b₀ 0 = b₀ := by
  simp [historyAverage, linearLag_initial]


-- @@ L55-59 verbatim
theorem historyAverage_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b) (b₀ y : ℝ) :
    HasDerivAt (historyAverage b b₀) (b y - historyAverage b b₀ y) y := by
  unfold historyAverage
  simpa only [one_mul] using
    linearLag_hasDerivAt (a := fun _ : ℝ => (1 : ℝ)) continuous_const hb b₀ y


-- @@ L61-63 verbatim
theorem historyAverage_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (b₀ : ℝ) :
    ContDiff ℝ ∞ (historyAverage b b₀) :=
  linearLag_contDiff contDiff_const hb b₀


-- @@ L65-79 verbatim
theorem historyAverage_constant {b : ℝ → ℝ} {b₀ y : ℝ}
    (hb : ∀ t ∈ uIcc (0 : ℝ) y, b t = b₀) : historyAverage b b₀ y = b₀ := by
  rw [historyAverage_formula]
  have hexp : (∫ t in (0 : ℝ)..y, Real.exp t) = Real.exp y - 1 := by
    simpa only [one_mul, div_one] using integral_exp_mul_real (a := 1) one_ne_zero y
  have he : (∫ t in (0 : ℝ)..y, Real.exp t * b t) = (Real.exp y - 1) * b₀ := by
    calc
      _ = ∫ t in (0 : ℝ)..y, Real.exp t * b₀ :=
        intervalIntegral.integral_congr (fun t ht => by rw [hb t ht])
      _ = _ := by rw [intervalIntegral.integral_mul_const, hexp]
  rw [he]
  have hx : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp (-y) * Real.exp y) * b₀ := by ring
    _ = b₀ := by rw [hx, one_mul]


-- @@ L81-87 verbatim
theorem historyAverage_nonneg {b : ℝ → ℝ} {b₀ y : ℝ}
    (h₀ : 0 ≤ b₀) (hy : 0 ≤ y) (hb : ∀ t ∈ Icc (0 : ℝ) y, 0 ≤ b t) :
    0 ≤ historyAverage b b₀ y := by
  rw [historyAverage_formula]
  apply mul_nonneg (Real.exp_pos _).le
  exact add_nonneg h₀ (intervalIntegral.integral_nonneg hy
    (fun t ht => mul_nonneg (Real.exp_pos _).le (hb t ht)))


-- @@ L89-104 verbatim
theorem historyAverage_le {b : ℝ → ℝ} (hbc : Continuous b) {b₀ K y : ℝ}
    (h₀ : b₀ ≤ K) (hy : 0 ≤ y) (hb : ∀ t ∈ Icc (0 : ℝ) y, b t ≤ K) :
    historyAverage b b₀ y ≤ K := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hy
    ((Real.continuous_exp.fun_mul hbc).intervalIntegrable 0 y)
    ((Real.continuous_exp.fun_mul continuous_const).intervalIntegrable 0 y)
    (fun t ht => mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le)
  have hexp : (∫ t in (0 : ℝ)..y, Real.exp t) = Real.exp y - 1 := by
    simpa only [one_mul, div_one] using integral_exp_mul_real (a := 1) one_ne_zero y
  rw [intervalIntegral.integral_mul_const, hexp] at hi
  rw [historyAverage_formula]
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ Real.exp (-y) * (K + (Real.exp y - 1) * K) := by gcongr
    _ = (Real.exp (-y) * Real.exp y) * K := by ring
    _ = K := by rw [he, one_mul]


-- @@ L106-116 verbatim
theorem historyAverage_late {b : ℝ → ℝ} (hbc : Continuous b) {b₀ a y : ℝ}
    (hay : a ≤ y) (hb : ∀ t, a ≤ t → b t = 0) :
    historyAverage b b₀ y = Real.exp (-(y - a)) * historyAverage b b₀ a := by
  have hi := OutgoingPulseBounds.integral_stops (Real.continuous_exp.fun_mul hbc) hay
    (fun t ht => by rw [hb t ht, mul_zero])
  rw [historyAverage_formula, hi, historyAverage_formula]
  have he : Real.exp (-(y - a)) * Real.exp (-a) = Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, he]


-- @@ L118-120 verbatim
/-- The actual average axial coefficient; the incoming value integrates `k=4`. -/
noncomputable def averagedDrop (c : Parameters) : ℝ → ℝ :=
  historyAverage (dropCoefficient c.m) 4


-- @@ L122-124 verbatim
/-- The squared axial history; the incoming value integrates `k²=16`. -/
noncomputable def averagedDropSquare (c : Parameters) : ℝ → ℝ :=
  historyAverage (fun y => dropCoefficient c.m y ^ 2) 16


-- @@ L126-127 verbatim
theorem averagedDrop_contDiff (c : Parameters) : ContDiff ℝ ∞ (averagedDrop c) :=
  historyAverage_contDiff (dropCoefficient_contDiff c.m_pos) 4


-- @@ L129-131 verbatim
theorem averagedDrop_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (averagedDrop c) (dropCoefficient c.m y - averagedDrop c y) y :=
  historyAverage_hasDerivAt (dropCoefficient_contDiff c.m_pos).continuous 4 y


-- @@ L133-137 verbatim
theorem averagedDrop_early (c : Parameters) {y : ℝ} (hy : y ≤ 1) :
    averagedDrop c y = 4 := by
  apply historyAverage_constant
  intro t ht
  exact dropCoefficient_early c.m (ht.2.trans (max_le (by norm_num) hy))


-- @@ L139-143 verbatim
theorem averagedDrop_bounds (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ averagedDrop c y ∧ averagedDrop c y ≤ 4 := by
  exact ⟨historyAverage_nonneg (by norm_num) hy (fun t _ => (dropCoefficient_bounds c.m t).1),
    historyAverage_le (dropCoefficient_contDiff c.m_pos).continuous le_rfl hy
      (fun t _ => (dropCoefficient_bounds c.m t).2)⟩


-- @@ L145-150 verbatim
theorem averagedDropSquare_bounds (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ averagedDropSquare c y ∧ averagedDropSquare c y ≤ 16 := by
  refine ⟨historyAverage_nonneg (by norm_num) hy (fun t _ => sq_nonneg _),
    historyAverage_le ((dropCoefficient_contDiff c.m_pos).pow 2).continuous le_rfl hy ?_⟩
  intro t _
  nlinarith [(dropCoefficient_bounds c.m t).1, (dropCoefficient_bounds c.m t).2]


-- @@ L152-164 verbatim
theorem averagedDrop_is_mass_history (c : Parameters) (amp : ℝ → ℝ) (η : ℝ)
    {y : ℝ} (hy : y ≤ c.pulseStart) :
    massMoment c amp η y / Real.exp y = averagedDrop c y * η := by
  have hi : (∫ t in (0 : ℝ)..y, Real.exp t * axial c amp (t, η)) =
      (∫ t in (0 : ℝ)..y, Real.exp t * dropCoefficient c.m t) * η := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [axial_before_pulse c amp η (ht.2.trans (max_le c.pulseStart_pos.le hy))]
    ring
  rw [massMoment, hi, averagedDrop, historyAverage_formula, Real.exp_neg]
  ring


-- @@ L166-182 verbatim
theorem averagedDrop_small_on_second_ramp (c : Parameters) {y : ℝ}
    (hy : c.dropLength + 1 ≤ y) : averagedDrop c y ≤ 1 / 2 := by
  have he : Real.exp c.m ≤ y := by dsimp [Parameters.dropLength] at hy; linarith
  have hlate := historyAverage_late (dropCoefficient_contDiff c.m_pos).continuous he
    (fun t ht => dropCoefficient_late c.m_pos ht) (b₀ := (4 : ℝ))
  change averagedDrop c y = Real.exp (-(y - Real.exp c.m)) * averagedDrop c (Real.exp c.m) at hlate
  rw [hlate]
  have hbar := (averagedDrop_bounds c (Real.exp_pos c.m).le).2
  have hex : Real.exp (-(y - Real.exp c.m)) ≤ (1 / 8 : ℝ) := by
    rw [Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hlin := Real.add_one_le_exp (y - Real.exp c.m)
    dsimp [Parameters.dropLength] at hy
    norm_num
    linarith
  nlinarith [Real.exp_pos (-(y - Real.exp c.m))]


-- @@ L184-185 verbatim
/-- Shape gradient, given by `2 * η / (1 + η ^ 2)`. -/
noncomputable def shapeGradient (η : ℝ) : ℝ := 2 * η / (1 + η ^ 2)


-- @@ L187-189 verbatim
theorem shapeGradient_contDiff : ContDiff ℝ ∞ shapeGradient :=
  (contDiff_const.mul contDiff_id).div (contDiff_const.add (contDiff_id.pow 2))
    (fun η => by positivity)


-- @@ L191-193 verbatim
theorem parameter_square_le_one {η : ℝ} (hη : |η| ≤ 1) : η ^ 2 ≤ 1 := by
  have h := sq_le_sq₀ (abs_nonneg η) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr hη
  simpa using h


-- @@ L195-205 verbatim
theorem eta_shapeGradient_bounds {η : ℝ} (hη : |η| ≤ 1) :
    η ^ 2 ≤ η * shapeGradient η ∧ η * shapeGradient η ≤ 1 := by
  have hsq := parameter_square_le_one hη
  have hp : 0 < 1 + η ^ 2 := by positivity
  unfold shapeGradient
  rw [← mul_div_assoc]
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith [sq_nonneg η, mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hsq)]
  · apply (div_le_one hp).mpr
    linarith


-- @@ L207-210 verbatim
theorem abs_shapeGradient_le (η : ℝ) : |shapeGradient η| ≤ 2 * |η| := by
  rw [shapeGradient, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (by positivity : 0 < 1 + η ^ 2)]
  exact div_le_self (by positivity) (by linarith [sq_nonneg η])


-- @@ L212-222 verbatim
theorem dropCoefficient_hasDerivAt {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    HasDerivAt (dropCoefficient m)
      (-(4 * deriv sigma (Real.log y / m) / (m * y))) y := by
  have hd := ((sigma_contDiff.differentiable (by simp) (Real.log y / m)).hasDerivAt.comp y
    ((Real.hasDerivAt_log hy.ne').div_const m)).const_sub 1
  have he : dropCoefficient m =ᶠ[𝓝 y] (fun t => 4 * (1 - sigma (Real.log t / m))) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact dropCoefficient_eq hm ht
  convert! (hd.const_mul 4).congr_of_eventuallyEq he using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


-- @@ L224-225 verbatim
/-- Drop speed, given by `4 * stepBound / m`. -/
noncomputable def dropSpeed (m : ℝ) : ℝ := 4 * stepBound / m


-- @@ L227-230 verbatim
theorem dropSpeed_pos {m : ℝ} (hm : 0 < m) : 0 < dropSpeed m := by
  unfold dropSpeed
  have := stepBound_ge_one
  positivity


-- @@ L232-240 verbatim
theorem dropCoefficient_deriv_bound {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    |deriv (dropCoefficient m) y| ≤ dropSpeed m / y := by
  rw [(dropCoefficient_hasDerivAt hm hy).deriv, abs_neg,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (sigma_derivative_nonneg _))
      (mul_pos hm hy).le)]
  unfold dropSpeed
  rw [div_div]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sigma_derivative_le _) (by norm_num)) (mul_pos hm hy).le


-- @@ L242-250 verbatim
theorem exists_small_dropSpeed {e : ℝ} (he : 0 < e) :
    ∃ M : ℝ, 0 < M ∧ ∀ m : ℝ, M ≤ m → dropSpeed m ≤ e := by
  refine ⟨4 * stepBound / e + 1, by have := stepBound_ge_one; positivity, ?_⟩
  intro m hm
  have hM : 0 < 4 * stepBound / e := by have := stepBound_ge_one; positivity
  have hmp : 0 < m := by linarith
  apply (div_le_iff₀ hmp).mpr
  have hh := (div_le_iff₀ he).mp (show 4 * stepBound / e ≤ m by linarith)
  linarith


-- @@ L252-252 verbatim
/-! ## The actual angular source and its ideal incoming lag -/


-- @@ L254-256 verbatim
/-- Transport W, given by `1 - L h η * averagedDrop c y`. -/
noncomputable def transportW (c : Parameters) (h y η : ℝ) : ℝ :=
  1 - L h η * averagedDrop c y


-- @@ L258-260 verbatim
/-- Angular rate, given by `1 + slope c.dropLength c.lam y`. -/
noncomputable def angularRate (c : Parameters) (y : ℝ) : ℝ :=
  1 + slope c.dropLength c.lam y


-- @@ L262-266 verbatim
/-- Angular source as an element of `ℝ`. -/
noncomputable def angularSource (c : Parameters) (h η y : ℝ) : ℝ :=
  -slope c.dropLength c.lam y * transportW c h y η -
    h * (1 - 2 * dropCoefficient c.m y * η ^ 2) +
      (D h + d η * dropCoefficient c.m y) * η * shapeGradient η


-- @@ L268-272 verbatim
/-- Ideal angular source, given by `(3 / 5) * (4 * L h η - 1) - h * (1 - 8 * η ^ 2) + (D h + 4 *
d η) * η * shapeGradient η`. -/
noncomputable def idealAngularSource (h η : ℝ) : ℝ :=
  (3 / 5) * (4 * L h η - 1) - h * (1 - 8 * η ^ 2) +
    (D h + 4 * d η) * η * shapeGradient η


-- @@ L274-275 verbatim
/-- Ideal angular lag, given by `idealAngularSource h η / (8 / 5)`. -/
noncomputable def idealAngularLag (h η : ℝ) : ℝ := idealAngularSource h η / (8 / 5)


-- @@ L277-280 verbatim
/-- Angular lag, given by `linearLag (angularRate c) (angularSource c h η) (idealAngularLag h
η)`. -/
noncomputable def angularLag (c : Parameters) (h η : ℝ) : ℝ → ℝ :=
  linearLag (angularRate c) (angularSource c h η) (idealAngularLag h η)


-- @@ L282-283 verbatim
theorem angularRate_contDiff (c : Parameters) : ContDiff ℝ ∞ (angularRate c) :=
  contDiff_const.add (slope_contDiff _ _)


-- @@ L285-294 verbatim
theorem angularSource_contDiff (c : Parameters) (h η : ℝ) :
    ContDiff ℝ ∞ (angularSource c h η) := by
  unfold angularSource transportW
  have hk := dropCoefficient_contDiff c.m_pos
  have hb := averagedDrop_contDiff c
  exact (((slope_contDiff _ _).neg.mul
    (contDiff_const.sub (contDiff_const.mul hb))).sub
    (contDiff_const.mul (contDiff_const.sub
      ((contDiff_const.mul hk).mul contDiff_const)))).add
    (((contDiff_const.add (contDiff_const.mul hk)).mul contDiff_const).mul contDiff_const)


-- @@ L296-300 verbatim
theorem angularLag_hasDerivAt (c : Parameters) (h η y : ℝ) :
    HasDerivAt (angularLag c h η)
      (angularSource c h η y - angularRate c y * angularLag c h η y) y :=
  linearLag_hasDerivAt (angularRate_contDiff c).continuous
    (angularSource_contDiff c h η).continuous (idealAngularLag h η) y


-- @@ L302-307 verbatim
theorem angularSource_ideal (c : Parameters) (h η : ℝ) {y : ℝ} (hy : y ≤ 0) :
    angularSource c h η y = idealAngularSource h η := by
  simp only [angularSource, transportW, slope_ideal c.dropLength_pos.le hy,
    averagedDrop_early c (show y ≤ 1 by linarith),
    dropCoefficient_early c.m (show y ≤ 1 by linarith), idealAngularSource]
  ring


-- @@ L309-316 verbatim
theorem idealAngularLag_is_incoming_integral (h η : ℝ) :
    (∫ t in Iic (0 : ℝ), Real.exp ((8 / 5 : ℝ) * t) * idealAngularSource h η) =
      idealAngularLag h η := by
  calc
    _ = idealAngularSource h η / (8 / 5) :=
      (OutgoingHistories.exponential_past (idealAngularSource h η) (8 / 5)
        (by norm_num) (fun t _ => mul_comm _ _)).2
    _ = _ := rfl


-- @@ L318-323 verbatim
theorem natural_L_bounds {h η : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 100) (hη : |η| ≤ 1) :
    49 / 50 ≤ L h η ∧ L h η ≤ 1 := by
  have hs := parameter_square_le_one hη
  unfold L
  constructor <;> linarith [mul_nonneg hh (sq_nonneg η),
    mul_nonneg hh (sub_nonneg.mpr hs)]


-- @@ L325-335 verbatim
theorem idealAngularLag_lower {h η : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 100)
    (hη : |η| ≤ 1) : 1 ≤ idealAngularLag h η := by
  have hL := (natural_L_bounds hh hh1 hη).1
  have hJ := (eta_shapeGradient_bounds hη).1
  have hpos : 0 ≤ (D h + 4 * d η) * (η * shapeGradient η) := by
    have hd : 0 ≤ d η := by unfold d; linarith [parameter_square_le_one hη]
    have hD : 0 ≤ D h := by unfold D; linarith
    exact mul_nonneg (by positivity) (le_trans (sq_nonneg η) hJ)
  unfold idealAngularLag idealAngularSource
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8 / 5)).mpr
  linarith [mul_nonneg hh (sq_nonneg η)]


-- @@ L337-341 verbatim
theorem angularRate_bounds (c : Parameters) (y : ℝ) :
    9 / 10 ≤ angularRate c y ∧ angularRate c y ≤ 8 / 5 := by
  unfold angularRate
  have hb := OutgoingPulseBounds.slope_bounds c y
  constructor <;> linarith [c.lam_lt]


-- @@ L343-347 verbatim
theorem slope_nonneg_before_dropEnd (c : Parameters) {y : ℝ}
    (hy : y ≤ c.dropLength + 1) : 0 ≤ slope c.dropLength c.lam y := by
  simp only [OutgoingSchedule.slope, sigma_zero (show y - (c.dropLength + 1) ≤ 0 by linarith),
    mul_zero, sub_zero]
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (sigma_le_one y))


-- @@ L349-352 verbatim
theorem slope_nonpos_after_first_ramp (c : Parameters) {y : ℝ}
    (hy : 1 ≤ y) : slope c.dropLength c.lam y ≤ 0 := by
  simp only [OutgoingSchedule.slope, sigma_one hy, sub_self, mul_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg c.lam_pos.le (sigma_nonneg _))


-- @@ L354-360 verbatim
theorem transportW_bounds (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 100)
    (hy : 0 ≤ y) (hη : |η| ≤ 1) : -3 ≤ transportW c h y η ∧ transportW c h y η ≤ 1 := by
  have hL := natural_L_bounds hh hh1 hη
  have hk := averagedDrop_bounds c hy
  unfold transportW
  constructor <;> linarith [mul_nonneg (by linarith : 0 ≤ L h η) hk.1,
    mul_le_mul hL.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)]


-- @@ L362-369 verbatim
theorem transportW_second_ramp (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : c.dropLength + 1 ≤ y) (hη : |η| ≤ 1) :
    1 / 2 ≤ transportW c h y η := by
  have hL := (natural_L_bounds hh hh1 hη).2
  have hk0 := (averagedDrop_bounds c (y := y) (by linarith [c.dropLength_pos])).1
  have hk := averagedDrop_small_on_second_ramp c hy
  unfold transportW
  linarith [mul_le_mul_of_nonneg_right hL hk0]


-- @@ L371-393 verbatim
theorem angularSource_lower (c : Parameters) {h η y : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (_hy : 0 ≤ y) (hη : |η| ≤ 1) :
    (49 / 100) * η ^ 2 - h ≤ angularSource c h η y := by
  have hlW : 0 ≤ -slope c.dropLength c.lam y * transportW c h y η := by
    by_cases hy1 : y ≤ 1
    · have hW : transportW c h y η ≤ 0 := by
        rw [transportW, averagedDrop_early c hy1]
        linarith [(natural_L_bounds hh hh1 hη).1]
      have hl := slope_nonneg_before_dropEnd c (hy1.trans (by linarith [c.dropLength_pos]))
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hl) hW
    · by_cases hy2 : y ≤ c.dropLength + 1
      · rw [slope_drop (by linarith) hy2, neg_zero, zero_mul]
      · exact mul_nonneg (neg_nonneg.mpr (slope_nonpos_after_first_ramp c (by linarith)))
          (by linarith [transportW_second_ramp c hh hh1 (le_of_not_ge hy2) hη])
  have hk := dropCoefficient_bounds c.m y
  have hd : 0 ≤ d η := by unfold d; linarith [parameter_square_le_one hη]
  have hJ := (eta_shapeGradient_bounds hη).1
  have hD : 49 / 100 ≤ D h := by unfold D; linarith
  have hDJ : (49 / 100) * η ^ 2 ≤ (D h + d η * dropCoefficient c.m y) * (η * shapeGradient η) :=
    mul_le_mul (by linarith [mul_nonneg hd hk.1]) hJ (sq_nonneg η)
      (by linarith [mul_nonneg hd hk.1])
  unfold angularSource
  linarith [mul_nonneg hh (mul_nonneg hk.1 (sq_nonneg η))]


-- @@ L395-397 verbatim
theorem primitive_continuous_of_continuous {r : ℝ → ℝ} (hr : Continuous r) :
    Continuous (OutgoingSchedule.primitive r) :=
  continuous_iff_continuousAt.mpr (fun y => (primitive_hasDerivAt hr y).continuousAt)


-- @@ L399-408 verbatim
theorem integral_integratingFactor_rate {r : ℝ → ℝ} (hr : Continuous r) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * r t) =
      Real.exp (OutgoingSchedule.primitive r y) - 1 := by
  have hd : ∀ t, HasDerivAt (fun x => Real.exp (OutgoingSchedule.primitive r x))
      (Real.exp (OutgoingSchedule.primitive r t) * r t) t := by
    intro t
    exact (primitive_hasDerivAt hr t).exp
  simpa [OutgoingSchedule.primitive] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (((Real.continuous_exp.comp (primitive_continuous_of_continuous hr)).mul
        hr).intervalIntegrable 0 y)


-- @@ L410-433 verbatim
theorem linearLag_constant {r b : ℝ → ℝ} (hr : Continuous r) {q₀ y : ℝ}
    (hb : ∀ t ∈ uIcc (0 : ℝ) y, b t = r t * q₀) : linearLag r b q₀ y = q₀ := by
  have hi : (∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * b t) =
      (Real.exp (OutgoingSchedule.primitive r y) - 1) * q₀ := by
    calc
      _ = ∫ t in (0 : ℝ)..y, (Real.exp (OutgoingSchedule.primitive r t) * r t) * q₀ := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hb t ht]
        ring
      _ = _ := by rw [intervalIntegral.integral_mul_const, integral_integratingFactor_rate hr]
  unfold linearLag
  change Real.exp (-OutgoingSchedule.primitive r y) *
    (q₀ + (∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * b t)) = q₀
  rw [hi]
  have he : Real.exp (-OutgoingSchedule.primitive r y) * Real.exp (OutgoingSchedule.primitive r y)
      = 1 := by
    rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp (-OutgoingSchedule.primitive r y) * Real.exp (OutgoingSchedule.primitive r y)) *
        q₀ := by
        ring
    _ = q₀ := by rw [he, one_mul]


-- @@ L435-442 verbatim
theorem angularLag_ideal (c : Parameters) (h η : ℝ) {y : ℝ} (hy : y ≤ 0) :
    angularLag c h η y = idealAngularLag h η := by
  apply linearLag_constant (angularRate_contDiff c).continuous
  intro t ht
  have ht0 : t ≤ 0 := ht.2.trans (max_le le_rfl hy)
  rw [angularSource_ideal c h η ht0]
  simp only [angularRate, slope_ideal c.dropLength_pos.le ht0, idealAngularLag]
  ring


-- @@ L444-469 verbatim
theorem linearLag_lower_barrier {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ β κ y : ℝ} (hy : 0 ≤ y) (hq : β + κ ≤ q₀)
    (hsource : ∀ t ∈ Icc (0 : ℝ) y, r t * β ≤ b t) :
    β + κ * Real.exp (-OutgoingSchedule.primitive r y) ≤ linearLag r b q₀ y := by
  have hE := Real.continuous_exp.comp (primitive_continuous_of_continuous hr)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hy
    ((hE.fun_mul (hr.fun_mul continuous_const)).intervalIntegrable 0 y)
    ((hE.fun_mul hb).intervalIntegrable 0 y)
    (fun t ht => mul_le_mul_of_nonneg_left (hsource t ht) (Real.exp_pos _).le)
  have heq : (∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * (r t * β)) =
      (Real.exp (OutgoingSchedule.primitive r y) - 1) * β := by
    simp_rw [← mul_assoc]
    rw [intervalIntegral.integral_mul_const, integral_integratingFactor_rate hr]
  simp only [Function.comp_apply] at hi
  rw [heq] at hi
  unfold linearLag
  change _ ≤ Real.exp (-OutgoingSchedule.primitive r y) *
    (q₀ + ∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * b t)
  have hc : Real.exp (-OutgoingSchedule.primitive r y) * Real.exp (OutgoingSchedule.primitive r y)
      = 1 := by
    rw [← Real.exp_add]; simp
  calc
    _ = Real.exp (-OutgoingSchedule.primitive r y) *
        (β + κ + (Real.exp (OutgoingSchedule.primitive r y) - 1) * β) := by
      linarith [congrArg (fun t : ℝ => t * β) hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hq hi) (Real.exp_pos _).le


-- @@ L471-493 verbatim
theorem slope_integral_upper (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    OutgoingSchedule.primitive (slope c.dropLength c.lam) y ≤ 3 / 5 := by
  have hc := (slope_contDiff c.dropLength c.lam).continuous
  have hlocal : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (∫ t in (0 : ℝ)..z, slope c.dropLength c.lam t) ≤ 3 / 5 := by
    intro z hz hz1
    have hi := intervalIntegral.integral_mono_on (μ := volume) hz
      (hc.intervalIntegrable 0 z) (continuous_const.intervalIntegrable 0 z)
      (fun t _ => (OutgoingPulseBounds.slope_bounds c t).2)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
    linarith
  by_cases hy1 : y ≤ 1
  · exact hlocal y hy hy1
  · have h1y : 1 ≤ y := le_of_not_ge hy1
    have hi := intervalIntegral.integral_mono_on (μ := volume) h1y
      (hc.intervalIntegrable 1 y) (continuous_const.intervalIntegrable 1 y)
      (fun t ht => slope_nonpos_after_first_ramp c ht.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hi
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 y)
    have h0 := hlocal 1 (by norm_num) le_rfl
    change (∫ t in (0 : ℝ)..y, slope c.dropLength c.lam t) ≤ 3 / 5
    linarith


-- @@ L495-501 verbatim
theorem angularRate_primitive (c : Parameters) (y : ℝ) :
    OutgoingSchedule.primitive (angularRate c) y =
      y + OutgoingSchedule.primitive (slope c.dropLength c.lam) y := by
  unfold OutgoingSchedule.primitive angularRate
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 y)
    ((slope_contDiff c.dropLength c.lam).continuous.intervalIntegrable 0 y)]
  simp


-- @@ L503-506 verbatim
theorem angularRate_primitive_upper (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    OutgoingSchedule.primitive (angularRate c) y ≤ y + 3 / 5 := by
  rw [angularRate_primitive]
  linarith [slope_integral_upper c hy]


-- @@ L508-515 verbatim
theorem angularSource_barrier (c : Parameters) {h η y : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    angularRate c y * (η ^ 2 / 4 - 2 * h) ≤ angularSource c h η y := by
  have hr := angularRate_bounds c y
  have hs := angularSource_lower c hh hh1 hy hη
  have h₁ := mul_le_mul_of_nonneg_right hr.2 (sq_nonneg η)
  have h₂ := mul_le_mul_of_nonneg_right hr.1 hh
  linarith [sq_nonneg η]


-- @@ L517-529 verbatim
theorem angularLag_barrier (c : Parameters) {h η y : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    η ^ 2 / 4 - 2 * h + (1 / 2) * Real.exp (-(y + 3 / 5)) ≤ angularLag c h η y := by
  have hinit : η ^ 2 / 4 - 2 * h + (1 / 2 : ℝ) ≤ idealAngularLag h η := by
    have hq := idealAngularLag_lower hh hh1 hη
    have hs := parameter_square_le_one hη
    linarith
  have hq := linearLag_lower_barrier (angularRate_contDiff c).continuous
    (angularSource_contDiff c h η).continuous hy hinit
    (fun t ht => angularSource_barrier c hh hh1 ht.1 hη)
  have he := Real.exp_le_exp.mpr (neg_le_neg (angularRate_primitive_upper c hy))
  exact (by linarith : η ^ 2 / 4 - 2 * h + (1 / 2) * Real.exp (-(y + 3 / 5)) ≤
    η ^ 2 / 4 - 2 * h + (1 / 2) * Real.exp (-OutgoingSchedule.primitive (angularRate c) y)).trans hq


-- @@ L531-532 verbatim
/-- Cone floor, given by `Real.exp (-(3 / 5 : ℝ)) / 4`. -/
noncomputable def coneFloor : ℝ := Real.exp (-(3 / 5 : ℝ)) / 4


-- @@ L534-534 verbatim
theorem coneFloor_pos : 0 < coneFloor := div_pos (Real.exp_pos _) (by norm_num)


-- @@ L536-539 verbatim
theorem coneFloor_le_quarter : coneFloor ≤ 1 / 4 := by
  have he : Real.exp (-(3 / 5 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  unfold coneFloor
  linarith


-- @@ L541-557 verbatim
/-- The positive angular lag is derived from its incoming ideal integral and
the true source. The constant is absolute and uniform in `P, λ, h, m`. -/
theorem angularLag_lower (c : Parameters) {h η y T : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hyT : y ≤ T) (hη : |η| ≤ 1)
    (hhT : h ≤ Real.exp (-(T + 3 / 5)) / 8) :
    coneFloor * (η ^ 2 + Real.exp (-y)) ≤ angularLag c h η y := by
  have hq := angularLag_barrier c hh hh1 hy hη
  have hT : Real.exp (-(T + 3 / 5)) ≤ Real.exp (-(y + 3 / 5)) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-(y + 3 / 5)) = Real.exp (-(3 / 5 : ℝ)) * Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hηc := mul_le_mul_of_nonneg_right coneFloor_le_quarter (sq_nonneg η)
  rw [he] at hq hT
  unfold coneFloor at hηc ⊢
  linarith


-- @@ L559-563 verbatim
theorem angularLag_pos (c : Parameters) {h η y T : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hyT : y ≤ T) (hη : |η| ≤ 1)
    (hhT : h ≤ Real.exp (-(T + 3 / 5)) / 8) : 0 < angularLag c h η y :=
  (mul_pos coneFloor_pos (add_pos_of_nonneg_of_pos (sq_nonneg η) (Real.exp_pos _))).trans_le
    (angularLag_lower c hh hh1 hy hyT hη hhT)


-- @@ L565-565 verbatim
/-! ## The actual angular-energy history -/


-- @@ L567-569 verbatim
/-- Clock energy, given by `radialAmplitude c.P c.dropLength c.lam y ^ 2`. -/
noncomputable def clockEnergy (c : Parameters) (y : ℝ) : ℝ :=
  radialAmplitude c.P c.dropLength c.lam y ^ 2


-- @@ L571-573 verbatim
/-- Weighted clock energy, given by `Real.exp y * clockEnergy c y`. -/
noncomputable def weightedClockEnergy (c : Parameters) (y : ℝ) : ℝ :=
  Real.exp y * clockEnergy c y


-- @@ L575-577 verbatim
/-- Averaged clock energy, given by `historyAverage (clockEnergy c) ((5 / 6) * c.P ^ 2)`. -/
noncomputable def averagedClockEnergy (c : Parameters) : ℝ → ℝ :=
  historyAverage (clockEnergy c) ((5 / 6) * c.P ^ 2)


-- @@ L579-581 verbatim
/-- Averaged energy, given by `shape η ^ 2 * averagedClockEnergy c y`. -/
noncomputable def averagedEnergy (c : Parameters) (y η : ℝ) : ℝ :=
  shape η ^ 2 * averagedClockEnergy c y


-- @@ L583-584 verbatim
theorem clockEnergy_contDiff (c : Parameters) : ContDiff ℝ ∞ (clockEnergy c) :=
  (radialAmplitude_contDiff _ _ _).pow 2


-- @@ L586-587 verbatim
theorem clockEnergy_pos (c : Parameters) (y : ℝ) : 0 < clockEnergy c y :=
  sq_pos_of_pos (mul_pos c.P_pos (Real.exp_pos _))


-- @@ L589-590 verbatim
theorem clockEnergy_initial (c : Parameters) : clockEnergy c 0 = c.P ^ 2 := by
  simp [clockEnergy, radialAmplitude, logAmplitude, OutgoingSchedule.primitive]


-- @@ L592-597 verbatim
theorem clockEnergy_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (clockEnergy c)
      ((2 * slope c.dropLength c.lam y - 1) * clockEnergy c y) y := by
  convert! (radialAmplitude_hasDerivAt c.P c.dropLength c.lam y).pow 2 using 1
  simp only [clockEnergy]
  ring


-- @@ L599-604 verbatim
theorem weightedClockEnergy_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (weightedClockEnergy c)
      (2 * slope c.dropLength c.lam y * weightedClockEnergy c y) y := by
  convert! (Real.hasDerivAt_exp y).mul (clockEnergy_hasDerivAt c y) using 1
  simp only [weightedClockEnergy]
  ring


-- @@ L606-615 verbatim
theorem weightedClockEnergy_monotone (c : Parameters) :
    MonotoneOn (weightedClockEnergy c) (Iic (c.dropLength + 1)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
    ((Real.continuous_exp.fun_mul (clockEnergy_contDiff c).continuous).continuousOn)
    (fun y _ => (weightedClockEnergy_hasDerivAt c y).hasDerivWithinAt)
  intro y hy
  have hy' : y ∈ Iic (c.dropLength + 1) := interior_subset hy
  have hs := slope_nonneg_before_dropEnd c hy'
  exact mul_nonneg (mul_nonneg (by norm_num) hs)
    (mul_nonneg (Real.exp_pos y).le (clockEnergy_pos c y).le)


-- @@ L617-624 verbatim
theorem clockEnergy_lower (c : Parameters) {y : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ c.dropLength + 1) : c.P ^ 2 * Real.exp (-y) ≤ clockEnergy c y := by
  have hm := weightedClockEnergy_monotone c
    (show (0 : ℝ) ≤ c.dropLength + 1 by linarith [c.dropLength_pos]) hy' hy
  simp only [weightedClockEnergy, Real.exp_zero, one_mul, clockEnergy_initial] at hm
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-y)).le
  linarith [congrArg (fun t : ℝ => t * clockEnergy c y) he]


-- @@ L626-628 verbatim
theorem averagedClockEnergy_nonneg (c : Parameters) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ averagedClockEnergy c y :=
  historyAverage_nonneg (by positivity) hy (fun t _ => (clockEnergy_pos c t).le)


-- @@ L630-647 verbatim
theorem averagedClockEnergy_upper (c : Parameters) {y : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ c.dropLength + 1) :
    averagedClockEnergy c y ≤ (y + 5 / 6) * clockEnergy c y := by
  have hw := weightedClockEnergy_monotone c
  have hzero := hw (show (0 : ℝ) ≤ c.dropLength + 1 by linarith [c.dropLength_pos]) hy' hy
  simp only [weightedClockEnergy, Real.exp_zero, one_mul, clockEnergy_initial] at hzero
  have hi := intervalIntegral.integral_mono_on (μ := volume) hy
    ((Real.continuous_exp.fun_mul (clockEnergy_contDiff c).continuous).intervalIntegrable 0 y)
    (continuous_const.intervalIntegrable 0 y)
    (fun t ht => hw (ht.2.trans hy') hy' ht.2)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, weightedClockEnergy] at hi
  rw [averagedClockEnergy, historyAverage_formula]
  have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ Real.exp (-y) * ((5 / 6) * (Real.exp y * clockEnergy c y) +
        y * (Real.exp y * clockEnergy c y)) := by gcongr
    _ = (Real.exp (-y) * Real.exp y) * ((y + 5 / 6) * clockEnergy c y) := by ring
    _ = _ := by rw [he, one_mul]


-- @@ L649-654 verbatim
theorem averagedEnergy_upper (c : Parameters) {y : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ c.dropLength + 1) (η : ℝ) :
    averagedEnergy c y η ≤ (y + 5 / 6) * angular c.P c.dropLength c.lam (y, η) ^ 2 := by
  have hb := mul_le_mul_of_nonneg_left (averagedClockEnergy_upper c hy hy') (sq_nonneg (shape η))
  simpa only [averagedEnergy, angular, clockEnergy, mul_pow, mul_comm, mul_left_comm, mul_assoc]
      using hb


-- @@ L656-668 verbatim
theorem angular_square_lower (c : Parameters) {y η : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ c.dropLength + 1) (hη : |η| ≤ 1) :
    (c.P ^ 2 / 4) * Real.exp (-y) ≤ angular c.P c.dropLength c.lam (y, η) ^ 2 := by
  have hs : (1 / 2 : ℝ) ≤ shape η := by
    unfold shape
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 1 + η ^ 2)).mpr
    linarith [parameter_square_le_one hη]
  have hss : (1 / 4 : ℝ) ≤ shape η ^ 2 := by nlinarith [shape_pos η]
  have hm := mul_le_mul (clockEnergy_lower c hy hy') hss (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (clockEnergy_pos c y).le
  simpa only [angular, clockEnergy, mul_pow, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm,
      mul_assoc] using hm


-- @@ L670-676 verbatim
theorem clockEnergy_ideal (c : Parameters) {y : ℝ} (hy : y ≤ 0) :
    clockEnergy c y = c.P ^ 2 * Real.exp ((1 / 5 : ℝ) * y) := by
  simp only [clockEnergy, radialAmplitude, logAmplitude_ideal c.dropLength_pos.le hy, mul_pow,
    ← Real.exp_nat_mul]
  congr 2
  norm_num
  ring


-- @@ L678-699 verbatim
theorem averagedClockEnergy_ideal (c : Parameters) {y : ℝ} (hy : y ≤ 0) :
    averagedClockEnergy c y = (5 / 6) * clockEnergy c y := by
  have hi : (∫ t in (0 : ℝ)..y, Real.exp t * clockEnergy c t) =
      c.P ^ 2 * ((Real.exp ((6 / 5 : ℝ) * y) - 1) / (6 / 5)) := by
    calc
      _ = ∫ t in (0 : ℝ)..y, c.P ^ 2 * Real.exp ((6 / 5 : ℝ) * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [clockEnergy_ideal c (ht.2.trans (max_le le_rfl hy))]
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_mul_real (by norm_num)]
  rw [averagedClockEnergy, historyAverage_formula, hi, clockEnergy_ideal c hy]
  have he : Real.exp (-y) * Real.exp ((6 / 5 : ℝ) * y) = Real.exp ((1 / 5 : ℝ) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (5 / 6) * c.P ^ 2 * (Real.exp (-y) * Real.exp ((6 / 5 : ℝ) * y)) := by ring
    _ = _ := by rw [he]; ring


-- @@ L701-701 verbatim
/-! ## Pressure and the axial lag with the full ideal incoming history -/


-- @@ L703-706 verbatim
/-- Pressure clock, given by `(5 / 2) * c.P ^ 2 + (1 / 2) * OutgoingSchedule.primitive
(clockEnergy c) y`. -/
noncomputable def pressureClock (c : Parameters) (y : ℝ) : ℝ :=
  (5 / 2) * c.P ^ 2 + (1 / 2) * OutgoingSchedule.primitive (clockEnergy c) y


-- @@ L708-711 verbatim
/-- Entrance pressure, given by `SchedulePressure.axisPressure v η + shape η ^ 2 * pressureClock
v.core y`. -/
noncomputable def entrancePressure (v : TailData) (y η : ℝ) : ℝ :=
  SchedulePressure.axisPressure v η + shape η ^ 2 * pressureClock v.core y


-- @@ L713-717 verbatim
/-- Pressure gradient, given by `deriv (SchedulePressure.axisPressure v) η - 2 * shapeGradient η
* shape η ^ 2 * pressureClock v.core y`. -/
noncomputable def pressureGradient (v : TailData) (y η : ℝ) : ℝ :=
  deriv (SchedulePressure.axisPressure v) η -
    2 * shapeGradient η * shape η ^ 2 * pressureClock v.core y


-- @@ L719-727 verbatim
theorem shape_hasDerivAt (η : ℝ) :
    HasDerivAt shape (-shapeGradient η * shape η) η := by
  have hd := ((hasDerivAt_const η (1 : ℝ)).fun_add ((hasDerivAt_id η).fun_pow 2)).fun_inv
    (by positivity : (1 : ℝ) + η ^ 2 ≠ 0)
  convert! hd using 1
  unfold shape shapeGradient
  field_simp
  ring_nf
  simp; ring


-- @@ L729-732 verbatim
theorem shapeSquare_hasDerivAt (η : ℝ) :
    HasDerivAt (fun t => shape t ^ 2) (-2 * shapeGradient η * shape η ^ 2) η := by
  convert! (shape_hasDerivAt η).pow 2 using 1
  ring


-- @@ L734-736 verbatim
theorem pressureClock_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (pressureClock c) ((1 / 2) * clockEnergy c y) y :=
  ((primitive_hasDerivAt (clockEnergy_contDiff c).continuous y).const_mul (1 / 2)).const_add _


-- @@ L738-743 verbatim
theorem entrancePressure_hasDerivAt_eta (v : TailData) (y η : ℝ) :
    HasDerivAt (entrancePressure v y) (pressureGradient v y η) η := by
  have hp := ((SchedulePressure.axisPressure_contDiff v).differentiable (by simp) η).hasDerivAt
  convert! hp.add ((shapeSquare_hasDerivAt η).mul_const (pressureClock v.core y)) using 1
  unfold pressureGradient
  ring


-- @@ L745-751 verbatim
theorem entrancePressure_hasDerivAt_y (v : TailData) (y η : ℝ) :
    HasDerivAt (fun t => entrancePressure v t η)
      ((1 / 2) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) y := by
  convert! ((pressureClock_hasDerivAt v.core y).const_mul (shape η ^ 2)).const_add
    (SchedulePressure.axisPressure v η) using 1
  unfold angular clockEnergy
  ring


-- @@ L753-760 verbatim
theorem pressureGradient_hasDerivAt_y (v : TailData) (y η : ℝ) :
    HasDerivAt (fun t => pressureGradient v t η)
      (-shapeGradient η * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) y := by
  convert! ((pressureClock_hasDerivAt v.core y).const_mul
    (2 * shapeGradient η * shape η ^ 2)).const_sub (deriv (SchedulePressure.axisPressure v) η)
        using 1
  unfold angular clockEnergy
  ring


-- @@ L762-773 verbatim
theorem pressureClock_ideal (c : Parameters) {y : ℝ} (hy : y ≤ 0) :
    pressureClock c y = (5 / 2) * clockEnergy c y := by
  have hi : (∫ t in (0 : ℝ)..y, clockEnergy c t) =
      c.P ^ 2 * ((Real.exp ((1 / 5 : ℝ) * y) - 1) / (1 / 5)) := by
    calc
      _ = ∫ t in (0 : ℝ)..y, c.P ^ 2 * Real.exp ((1 / 5 : ℝ) * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact clockEnergy_ideal c (ht.2.trans (max_le le_rfl hy))
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_mul_real (by norm_num)]
  rw [pressureClock, OutgoingSchedule.primitive, hi, clockEnergy_ideal c hy]
  ring


-- @@ L775-780 verbatim
theorem averagedDropSquare_early (c : Parameters) {y : ℝ} (hy : y ≤ 1) :
    averagedDropSquare c y = 16 := by
  apply historyAverage_constant
  intro t ht
  rw [dropCoefficient_early c.m (ht.2.trans (max_le (by norm_num) hy))]
  norm_num


-- @@ L782-785 verbatim
theorem averagedDropSquare_hasDerivAt (c : Parameters) (y : ℝ) :
    HasDerivAt (averagedDropSquare c)
      (dropCoefficient c.m y ^ 2 - averagedDropSquare c y) y :=
  historyAverage_hasDerivAt ((dropCoefficient_contDiff c.m_pos).pow 2).continuous 16 y


-- @@ L787-793 verbatim
theorem averagedEnergy_hasDerivAt_y (c : Parameters) (y η : ℝ) :
    HasDerivAt (fun t => averagedEnergy c t η)
      (angular c.P c.dropLength c.lam (y, η) ^ 2 - averagedEnergy c y η) y := by
  convert! (historyAverage_hasDerivAt (clockEnergy_contDiff c).continuous
    ((5 / 6) * c.P ^ 2) y).const_mul (shape η ^ 2) using 1
  unfold averagedEnergy averagedClockEnergy angular clockEnergy
  ring


-- @@ L795-799 verbatim
theorem averagedEnergy_hasDerivAt_eta (c : Parameters) (y η : ℝ) :
    HasDerivAt (averagedEnergy c y) (-2 * shapeGradient η * averagedEnergy c y η) η := by
  convert! (shapeSquare_hasDerivAt η).mul_const (averagedClockEnergy c y) using 1
  unfold averagedEnergy
  ring


-- @@ L801-805 verbatim
theorem transportW_hasDerivAt (c : Parameters) (h y η : ℝ) :
    HasDerivAt (fun t => transportW c h t η)
      (-L h η * (dropCoefficient c.m y - averagedDrop c y)) y := by
  convert! ((averagedDrop_hasDerivAt c y).const_mul (L h η)).const_sub 1 using 1
  ring


-- @@ L807-810 verbatim
/-- The part of the axial lag arising from the actual mass and squared-axial histories. -/
noncomputable def geometricAxialLag (c : Parameters) (h y η : ℝ) : ℝ :=
  -transportW c h y η * dropCoefficient c.m y * η +
    (4 * h * η ^ 3 - 2 * d η * η) * averagedDropSquare c y


-- @@ L812-815 verbatim
/-- The pressure and angular-energy part of the integrated axial lag. -/
noncomputable def pressureAxialLag (v : TailData) (y η : ℝ) : ℝ :=
  -(2 * v.h * η + d η * shapeGradient η) * averagedEnergy v.core y η +
    4 * A v.h * η * entrancePressure v y η - d η * pressureGradient v y η


-- @@ L817-819 verbatim
/-- Axial lag, given by `geometricAxialLag v.core v.h y η + pressureAxialLag v y η`. -/
noncomputable def axialLag (v : TailData) (y η : ℝ) : ℝ :=
  geometricAxialLag v.core v.h y η + pressureAxialLag v y η


-- @@ L821-825 verbatim
/-- Geometric axial source as an element of `ℝ`. -/
noncomputable def geometricAxialSource (c : Parameters) (h y η : ℝ) : ℝ :=
  -transportW c h y η * deriv (dropCoefficient c.m) y * η -
    A h * (1 - 2 * dropCoefficient c.m y * η ^ 2) * (dropCoefficient c.m y * η) -
      (D h + d η * dropCoefficient c.m y) * η * dropCoefficient c.m y


-- @@ L827-830 verbatim
/-- Pressure axial source as an element of `ℝ`. -/
noncomputable def pressureAxialSource (v : TailData) (y η : ℝ) : ℝ :=
  -d η * pressureGradient v y η + 4 * A v.h * η * entrancePressure v y η +
    η * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2


-- @@ L832-834 verbatim
/-- Axial source, given by `geometricAxialSource v.core v.h y η + pressureAxialSource v y η`. -/
noncomputable def axialSource (v : TailData) (y η : ℝ) : ℝ :=
  geometricAxialSource v.core v.h y η + pressureAxialSource v y η


-- @@ L836-844 verbatim
theorem geometricAxialLag_hasDerivAt (c : Parameters) (h y η : ℝ) :
    HasDerivAt (fun t => geometricAxialLag c h t η)
      (geometricAxialSource c h y η - geometricAxialLag c h y η) y := by
  have hk := ((dropCoefficient_contDiff c.m_pos).differentiable (by simp) y).hasDerivAt
  have hd := (((transportW_hasDerivAt c h y η).fun_neg.fun_mul hk).mul_const η).fun_add
    ((averagedDropSquare_hasDerivAt c y).const_mul (4 * h * η ^ 3 - 2 * d η * η))
  convert! hd using 1
  unfold geometricAxialSource geometricAxialLag transportW A D L d
  ring


-- @@ L846-855 verbatim
theorem pressureAxialLag_hasDerivAt (v : TailData) (y η : ℝ) :
    HasDerivAt (fun t => pressureAxialLag v t η)
      (pressureAxialSource v y η - pressureAxialLag v y η) y := by
  have hd := (((averagedEnergy_hasDerivAt_y v.core y η).const_mul
    (-(2 * v.h * η + d η * shapeGradient η))).add
    ((entrancePressure_hasDerivAt_y v y η).const_mul (4 * A v.h * η))).sub
      ((pressureGradient_hasDerivAt_y v y η).const_mul (d η))
  convert! hd using 1
  unfold pressureAxialSource pressureAxialLag A
  ring


-- @@ L857-862 verbatim
theorem axialLag_hasDerivAt (v : TailData) (y η : ℝ) :
    HasDerivAt (fun t => axialLag v t η) (axialSource v y η - axialLag v y η) y := by
  convert! (geometricAxialLag_hasDerivAt v.core v.h y η).add
    (pressureAxialLag_hasDerivAt v y η) using 1
  unfold axialSource axialLag
  ring


-- @@ L864-866 verbatim
/-- Normalized energy history `S/X`, including both ideal-prefix integrals. -/
noncomputable def normalizedEnergyHistory (c : Parameters) (y η : ℝ) : ℝ :=
  η ^ 2 * averagedDropSquare c y - (1 / 2) * averagedEnergy c y η


-- @@ L868-874 verbatim
theorem normalizedEnergyHistory_hasDerivAt_eta (c : Parameters) (y η : ℝ) :
    HasDerivAt (normalizedEnergyHistory c y)
      (2 * η * averagedDropSquare c y + shapeGradient η * averagedEnergy c y η) η := by
  convert! (((hasDerivAt_id η).pow 2).mul_const (averagedDropSquare c y)).sub
    ((averagedEnergy_hasDerivAt_eta c y η).const_mul (1 / 2)) using 1
  simp only [id_eq]
  ring


-- @@ L876-887 verbatim
/-- This is precisely the axial integrated-history formula (9); the linear
mass-history contribution `D(M-η Mη)/X` vanishes for `U=k(y)η`. -/
theorem axialLag_integrated_history (v : TailData) (y η : ℝ) :
    axialLag v y η = -transportW v.core v.h y η * (dropCoefficient v.core.m y * η) +
      4 * v.h * η * normalizedEnergyHistory v.core y η -
        d η * deriv (normalizedEnergyHistory v.core y) η +
          4 * A v.h * η * entrancePressure v y η -
            d η * deriv (entrancePressure v y) η := by
  rw [(normalizedEnergyHistory_hasDerivAt_eta v.core y η).deriv,
    (entrancePressure_hasDerivAt_eta v y η).deriv]
  unfold axialLag geometricAxialLag pressureAxialLag normalizedEnergyHistory
  ring


-- @@ L889-895 verbatim
theorem geometricAxialLag_ideal (c : Parameters) (h η : ℝ) {y : ℝ} (hy : y ≤ 0) :
    geometricAxialLag c h y η = -20 * η + (32 + 32 * h) * η ^ 3 := by
  unfold geometricAxialLag transportW
  rw [averagedDrop_early c (by linarith), dropCoefficient_early c.m (by linarith),
    averagedDropSquare_early c (by linarith)]
  unfold L d
  ring


-- @@ L897-906 verbatim
theorem pressureAxialLag_ideal (v : TailData) (η : ℝ) {y : ℝ} (hy : y ≤ 0) :
    pressureAxialLag v y η =
      4 * A v.h * η * SchedulePressure.axisPressure v η -
        d η * deriv (SchedulePressure.axisPressure v) η +
          (5 / 6) * (5 * d η * shapeGradient η + (10 * A v.h + 1) * η) *
            angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
  unfold pressureAxialLag averagedEnergy entrancePressure pressureGradient
  rw [averagedClockEnergy_ideal v.core hy, pressureClock_ideal v.core hy]
  unfold angular clockEnergy A
  ring


-- @@ L908-911 verbatim
theorem entrancePressure_eq_future (v : TailData) {y : ℝ} (hy : 0 ≤ y)
    (hyend : y ≤ v.core.endpoint) : entrancePressure v y = FuturePressureBounds.Pi v y := by
  funext η
  exact (FuturePressureBounds.Pi_eq_radial_history v hy hyend η).symm


-- @@ L913-917 verbatim
theorem pressureGradient_eq_future (v : TailData) {y : ℝ} (hy : 0 ≤ y)
    (hyend : y ≤ v.core.endpoint) : pressureGradient v y = deriv (FuturePressureBounds.Pi v y) := by
  funext η
  rw [← entrancePressure_eq_future v hy hyend]
  exact (entrancePressure_hasDerivAt_eta v y η).deriv.symm


-- @@ L919-920 verbatim
/-- Pressure bound, given by `10 * FuturePressureBounds.envelopeConstant`. -/
noncomputable def pressureBound : ℝ := 10 * FuturePressureBounds.envelopeConstant


-- @@ L922-923 verbatim
theorem pressureBound_pos : 0 < pressureBound :=
  mul_pos (by norm_num) FuturePressureBounds.envelopeConstant_pos


-- @@ L925-942 verbatim
theorem actual_pressure_bounds (v : TailData) {y η : ℝ} (hy : 0 ≤ y)
    (hyend : y ≤ v.core.endpoint) (hη : |η| ≤ 1) :
    |entrancePressure v y η| ≤ pressureBound * angular v.core.P v.core.dropLength v.core.lam (y, η)
        ^ 2 ∧
    |pressureGradient v y η| ≤ pressureBound * |η| * angular v.core.P v.core.dropLength v.core.lam
        (y, η) ^ 2 ∧
    |deriv (pressureGradient v y) η| ≤ pressureBound * angular v.core.P v.core.dropLength
        v.core.lam (y, η) ^ 2 := by
  rw [entrancePressure_eq_future v hy hyend, pressureGradient_eq_future v hy hyend]
  have hb := FuturePressureBounds.uniform_pressure_bounds v hy hη
  rw [finalAngular_before v η hyend] at hb
  have hC := FuturePressureBounds.envelopeConstant_pos
  unfold pressureBound
  refine ⟨hb.1.trans ?_, hb.2.1.trans ?_, hb.2.2⟩
  · gcongr
    linarith
  · gcongr
    linarith


-- @@ L944-971 verbatim
theorem geometricAxialLag_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |geometricAxialLag c h y η| ≤ 64 * |η| := by
  have hk := dropCoefficient_bounds c.m y
  have hK := averagedDropSquare_bounds c hy
  have hW : |transportW c h y η| ≤ 3 := by
    exact abs_le.mpr (transportW_bounds c hh hh1 hy hη |>.imp_right (fun h => h.trans (by
        norm_num)))
  have hsq := parameter_square_le_one hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by unfold d; constructor <;> linarith [sq_nonneg η]
  have hc : |4 * h * η ^ 2 - 2 * d η| ≤ 3 := by
    apply abs_le.mpr
    have hm := mul_le_mul_of_nonneg_left hsq hh
    constructor <;> linarith [mul_nonneg hh (sq_nonneg η)]
  have hfirst : |-(transportW c h y η) * dropCoefficient c.m y * η| ≤ 12 * |η| := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hk.1]
    have hm := mul_le_mul hW hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 3)
    linarith [mul_le_mul_of_nonneg_right hm (abs_nonneg η)]
  have hsecond : |(4 * h * η ^ 3 - 2 * d η * η) * averagedDropSquare c y| ≤ 48 * |η| := by
    have he : 4 * h * η ^ 3 - 2 * d η * η = (4 * h * η ^ 2 - 2 * d η) * η := by ring
    rw [he, abs_mul, abs_mul, abs_of_nonneg hK.1]
    calc
      _ ≤ (3 * |η|) * 16 := mul_le_mul
        (mul_le_mul_of_nonneg_right hc (abs_nonneg η)) hK.2 hK.1 (by positivity)
      _ = _ := by ring
  exact (abs_add_le _ _).trans (by
    change _ ≤ 64 * |η|
    linarith [abs_nonneg η])


-- @@ L973-987 verbatim
theorem pressure_coefficient_bound {h η : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 100)
    (hη : |η| ≤ 1) : |2 * h * η + d η * shapeGradient η| ≤ 3 * |η| := by
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by
    unfold d
    constructor <;> linarith [parameter_square_le_one hη, sq_nonneg η]
  calc
    _ ≤ |2 * h * η| + |d η * shapeGradient η| := abs_add_le _ _
    _ = 2 * h * |η| + d η * |shapeGradient η| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hh, abs_of_nonneg hd.1]
    _ ≤ 2 * h * |η| + 2 * |η| := by
      apply add_le_add_right
      simpa only [one_mul] using
        mul_le_mul hd.2 (abs_shapeGradient_le η) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ _ := by linarith [abs_nonneg η, mul_le_mul_of_nonneg_right hh1 (abs_nonneg η)]


-- @@ L989-1030 verbatim
theorem pressureAxialLag_bound (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hy' : y ≤ v.core.dropLength + 1) (hη : |η| ≤ 1) :
    |pressureAxialLag v y η| ≤ (3 * (y + 1) + 4 * pressureBound) * |η| *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
  have hend : y ≤ v.core.endpoint := by
    have h0 := v.core.pulseStart_ge_hold
    have h1 := v.core.pulseLength_pos
    dsimp [Parameters.endpoint, Parameters.holdStart] at *
    linarith
  have hp := actual_pressure_bounds v hy hend hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by
    unfold d
    constructor <;> linarith [parameter_square_le_one hη, sq_nonneg η]
  have hA : 0 ≤ 4 * A v.h ∧ 4 * A v.h ≤ 3 := by
    unfold A
    constructor <;> linarith [v.h_pos]
  have hE : 0 ≤ averagedEnergy v.core y η :=
    mul_nonneg (sq_nonneg _) (averagedClockEnergy_nonneg v.core hy)
  have hEb : averagedEnergy v.core y η ≤ (y + 1) * angular v.core.P v.core.dropLength v.core.lam
      (y, η) ^ 2 := by
    exact (averagedEnergy_upper v.core hy hy' η).trans
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  have hcoef := pressure_coefficient_bound v.h_pos.le hh1 hη
  unfold pressureAxialLag
  calc
    _ ≤ |-(2 * v.h * η + d η * shapeGradient η) * averagedEnergy v.core y η| +
        |4 * A v.h * η * entrancePressure v y η| + |d η * pressureGradient v y η| :=
      (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = |2 * v.h * η + d η * shapeGradient η| * averagedEnergy v.core y η +
        (4 * A v.h * |η|) * |entrancePressure v y η| + d η * |pressureGradient v y η| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hE, abs_of_nonneg hd.1]
      rw [← abs_mul 4 (A v.h), abs_of_nonneg hA.1]
    _ ≤ (3 * |η|) * ((y + 1) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) +
        (3 * |η|) * (pressureBound * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) +
        pressureBound * |η| * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
      apply add_le_add
      · exact add_le_add (mul_le_mul hcoef hEb hE (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_right hA.2 (abs_nonneg η)) hp.1
            (abs_nonneg _) (by positivity))
      · simpa only [one_mul] using
          mul_le_mul hd.2 hp.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by ring


-- @@ L1032-1033 verbatim
/-- Axial bound, given by `259 + 4 * pressureBound`. -/
noncomputable def axialBound : ℝ := 259 + 4 * pressureBound


-- @@ L1035-1035 verbatim
theorem axialBound_pos : 0 < axialBound := by unfold axialBound; linarith [pressureBound_pos]


-- @@ L1037-1065 verbatim
/-- The actual full axial lag has the required normalized drop bound. The
geometric part is suppressed by choosing the fixed prefix amplitude first. -/
theorem axialLag_drop_bound (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hy' : y ≤ v.core.dropLength + 1) (hη : |η| ≤ 1)
    (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2) :
    |axialLag v y η| ≤ axialBound * |η| * (1 + y) *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
  have hEp : (1 / 4 : ℝ) ≤ angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    have hP' : Real.exp y ≤ v.core.P ^ 2 := (Real.exp_le_exp.mpr hy').trans hP
    have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have hmul := mul_le_mul_of_nonneg_right hP' (Real.exp_pos (-y)).le
    rw [he] at hmul
    have hlow := angular_square_lower v.core hy hy' hη
    linarith
  have hg := geometricAxialLag_bound v.core v.h_pos.le hh1 hy hη
  have hp := pressureAxialLag_bound v hh1 hy hy' hη
  have hg' : |geometricAxialLag v.core v.h y η| ≤
      256 * |η| * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    apply hg.trans
    linarith [mul_le_mul_of_nonneg_left hEp (show 0 ≤ 256 * |η| by positivity)]
  unfold axialLag
  apply (abs_add_le _ _).trans
  apply (add_le_add hg' hp).trans
  unfold axialBound
  have hC : 0 ≤ (256 + 4 * pressureBound) * |η| * y *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    have := pressureBound_pos
    positivity
  linarith


-- @@ L1067-1067 verbatim
/-! ## The two small shear quantities in the cone test -/


-- @@ L1069-1072 verbatim
/-- Shear, given by `2 * deriv (dropCoefficient c.m) y * η / angular c.P c.dropLength c.lam (y,
η)`. -/
noncomputable def shear (c : Parameters) (y η : ℝ) : ℝ :=
  2 * deriv (dropCoefficient c.m) y * η / angular c.P c.dropLength c.lam (y, η)


-- @@ L1074-1078 verbatim
/-- Direction ratio, given by `axialLag v y η / (angular v.core.P v.core.dropLength v.core.lam
(y, η) * angularLag v.core v.h η y)`. -/
noncomputable def directionRatio (v : TailData) (y η : ℝ) : ℝ :=
  axialLag v y η /
    (angular v.core.P v.core.dropLength v.core.lam (y, η) * angularLag v.core v.h η y)


-- @@ L1080-1082 verbatim
/-- Radial A, given by `2 - 2 * slope c.dropLength c.lam y`. -/
noncomputable def radialA (c : Parameters) (y : ℝ) : ℝ :=
  2 - 2 * slope c.dropLength c.lam y


-- @@ L1084-1095 verbatim
theorem shear_is_actual (c : Parameters) (amp : ℝ → ℝ) {y : ℝ}
    (hy : y < c.pulseStart) (η : ℝ) :
    shear c y η = 2 * deriv (fun t => axial c amp (t, η)) y /
      angular c.P c.dropLength c.lam (y, η) := by
  have heq : (fun t => axial c amp (t, η)) =ᶠ[𝓝 y] (fun t => dropCoefficient c.m t * η) := by
    filter_upwards [Iio_mem_nhds hy] with t ht
    exact axial_before_pulse c amp η ht.le
  rw [heq.deriv_eq,
    ((((dropCoefficient_contDiff c.m_pos).differentiable (by
        simp) y).hasDerivAt).mul_const η).deriv]
  unfold shear
  ring


-- @@ L1097-1106 verbatim
theorem angular_square_ge_quarter (c : Parameters) {y η : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ c.dropLength + 1) (hη : |η| ≤ 1)
    (hP : Real.exp (c.dropLength + 1) ≤ c.P ^ 2) :
    (1 / 4 : ℝ) ≤ angular c.P c.dropLength c.lam (y, η) ^ 2 := by
  have hP' : Real.exp y ≤ c.P ^ 2 := (Real.exp_le_exp.mpr hy').trans hP
  have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hP' (Real.exp_pos (-y)).le
  rw [he] at hm
  have hlow := angular_square_lower c hy hy' hη
  linarith


-- @@ L1108-1126 verbatim
theorem shear_drop_abs (c : Parameters) {y η : ℝ} (hy : 1 ≤ y)
    (hy' : y ≤ c.dropLength + 1) (hη : |η| ≤ 1)
    (hP : Real.exp (c.dropLength + 1) ≤ c.P ^ 2) :
    |shear c y η| ≤ 4 * dropSpeed c.m := by
  have hy0 : 0 < y := by linarith
  have hd := dropCoefficient_deriv_bound c.m_pos hy0
  have he := angular_pos c.P_pos c.dropLength c.lam (y, η)
  have he2 := angular_square_ge_quarter c hy0.le hy' hη hP
  have hhalf : (1 / 2 : ℝ) ≤ angular c.P c.dropLength c.lam (y, η) := by nlinarith
  have hd' : |deriv (dropCoefficient c.m) y| ≤ dropSpeed c.m :=
    hd.trans (div_le_self (dropSpeed_pos c.m_pos).le hy)
  unfold shear
  rw [abs_div, abs_mul, abs_mul, abs_of_pos he]
  norm_num
  apply (div_le_iff₀ he).mpr
  have hprod := mul_le_mul hd' hη (abs_nonneg η) (dropSpeed_pos c.m_pos).le
  have hden := mul_le_mul_of_nonneg_left hhalf
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (dropSpeed_pos c.m_pos).le)
  linarith


-- @@ L1128-1134 verbatim
theorem shear_drop_square (c : Parameters) {y η : ℝ} (hy : 1 ≤ y)
    (hy' : y ≤ c.dropLength + 1) (hη : |η| ≤ 1)
    (hP : Real.exp (c.dropLength + 1) ≤ c.P ^ 2) :
    shear c y η ^ 2 ≤ 16 * dropSpeed c.m ^ 2 := by
  have hb := shear_drop_abs c hy hy' hη hP
  have hd := dropSpeed_pos c.m_pos
  nlinarith [sq_abs (shear c y η), abs_nonneg (shear c y η)]


-- @@ L1136-1145 verbatim
theorem shear_direction_identity (v : TailData) (y η : ℝ)
    (hQ : 0 < angularLag v.core v.h η y) :
    |shear v.core y η * directionRatio v y η| =
      (2 * |deriv (dropCoefficient v.core.m) y| * |η| * |axialLag v y η|) /
        (angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 * angularLag v.core v.h η y) := by
  have hE := angular_pos v.core.P_pos v.core.dropLength v.core.lam (y, η)
  simp only [shear, directionRatio, abs_mul, abs_div, abs_of_pos hE, abs_of_pos hQ]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring


-- @@ L1147-1195 verbatim
theorem shear_direction_drop_bound (v : TailData) {y η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hy : 1 ≤ y) (hy' : y ≤ v.core.dropLength + 1)
    (hη : |η| ≤ 1) (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8) :
    |shear v.core y η * directionRatio v y η| ≤
      (4 * axialBound / coneFloor) * dropSpeed v.core.m := by
  have hy0 : 0 < y := by linarith
  have hyT : y ≤ v.core.holdStart := by dsimp [Parameters.holdStart]; linarith
  have hE := angular_pos v.core.P_pos v.core.dropLength v.core.lam (y, η)
  have hQ := angularLag_pos v.core v.h_pos.le hh1 hy0.le hyT hη hhT
  have hQb := angularLag_lower v.core v.h_pos.le hh1 hy0.le hyT hη hhT
  have hQη : coneFloor * η ^ 2 ≤ angularLag v.core v.h η y := by
    linarith [mul_pos coneFloor_pos (Real.exp_pos (-y))]
  have hd := dropCoefficient_deriv_bound v.core.m_pos hy0
  have hdy : |deriv (dropCoefficient v.core.m) y| * (1 + y) ≤ 2 * dropSpeed v.core.m := by
    have hmul := (le_div_iff₀ hy0).mp hd
    have h1 : |deriv (dropCoefficient v.core.m) y| ≤
        |deriv (dropCoefficient v.core.m) y| * y :=
      le_mul_of_one_le_right (abs_nonneg _) hy
    linarith
  have hN := axialLag_drop_bound v hh1 hy0.le hy' hη hP
  rw [shear_direction_identity v y η hQ]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hE) hQ)).mpr
  have hnum : 2 * |deriv (dropCoefficient v.core.m) y| * |η| * |axialLag v y η| ≤
      4 * axialBound * dropSpeed v.core.m * η ^ 2 *
        angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    calc
      _ ≤ 2 * |deriv (dropCoefficient v.core.m) y| * |η| *
          (axialBound * |η| * (1 + y) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (2 * axialBound * η ^ 2 * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) *
          (|deriv (dropCoefficient v.core.m) y| * (1 + y)) := by rw [← sq_abs η]; ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hdy
          (show 0 ≤ 2 * axialBound * η ^ 2 * angular v.core.P v.core.dropLength v.core.lam (y, η) ^
              2 by
            have := axialBound_pos
            positivity)
        convert! h using 1
        ring
  apply hnum.trans
  have hc : 0 ≤ (4 * axialBound / coneFloor) * dropSpeed v.core.m *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    have := axialBound_pos
    have := coneFloor_pos
    have := dropSpeed_pos v.core.m_pos
    positivity
  have h := mul_le_mul_of_nonneg_left hQη hc
  convert! h using 1 <;> field_simp [coneFloor_pos.ne']


-- @@ L1197-1199 verbatim
theorem radialA_drop (c : Parameters) {y : ℝ} (hy : 1 ≤ y)
    (hy' : y ≤ c.dropLength + 1) : radialA c y = 2 := by
  simp [radialA, slope_drop hy hy']


-- @@ L1201-1225 verbatim
/-- Quantified strict margins in the preliminary drop cone. -/
theorem drop_cone_margins (v : TailData) {y η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hy : 1 ≤ y) (hy' : y ≤ v.core.dropLength + 1)
    (hη : |η| ≤ 1) (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (he : dropSpeed v.core.m ≤ min (1 / 8) (coneFloor / (16 * axialBound))) :
    (7 / 4 : ℝ) ≤ radialA v.core y - shear v.core y η * directionRatio v y η ∧
      2 * shear v.core y η * directionRatio v y η + shear v.core y η ^ 2 / radialA v.core y +
        (radialA v.core y - 2) * directionRatio v y η ^ 2 ≤ 5 / 8 := by
  have he1 := he.trans (min_le_left _ _)
  have he2 := he.trans (min_le_right _ _)
  have hsw := shear_direction_drop_bound v hh1 hy hy' hη hP hhT
  have hsq := shear_drop_square v.core hy hy' hη hP
  have hS : shear v.core y η * directionRatio v y η ≤ 1 / 4 := by
    have hc : (4 * axialBound / coneFloor) * dropSpeed v.core.m ≤ 1 / 4 := by
      have hmul := (le_div_iff₀ (mul_pos (by norm_num) axialBound_pos)).mp he2
      calc
        _ = 4 * axialBound * dropSpeed v.core.m / coneFloor := by ring
        _ ≤ 1 / 4 := (div_le_iff₀ coneFloor_pos).mpr (by linarith)
    exact (le_abs_self _).trans (hsw.trans hc)
  have hsq' : shear v.core y η ^ 2 ≤ 1 / 4 := by
    have he0 := (dropSpeed_pos v.core.m_pos).le
    nlinarith
  rw [radialA_drop v.core hy hy']
  constructor <;> linarith


-- @@ L1227-1242 verbatim
theorem linearLag_pos_after {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ a y : ℝ} (hay : a ≤ y) (ha : 0 < linearLag r b q₀ a)
    (hs : ∀ t ∈ Icc a y, 0 ≤ b t) : 0 < linearLag r b q₀ y := by
  let F := fun t => Real.exp (OutgoingSchedule.primitive r t) * b t
  have hF : Continuous F := (Real.continuous_exp.comp (primitive_continuous_of_continuous hr)).mul
      hb
  have hinit : 0 < q₀ + OutgoingSchedule.primitive F a := by
    exact (mul_pos_iff_of_pos_left (Real.exp_pos (-OutgoingSchedule.primitive r a))).mp ha
  have hi : 0 ≤ ∫ t in a..y, F t := intervalIntegral.integral_nonneg hay
    (fun t ht => mul_nonneg (Real.exp_pos _).le (hs t ht))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable 0 a) (hF.intervalIntegrable a y)
  have hfin : 0 < q₀ + OutgoingSchedule.primitive F y := by
    unfold OutgoingSchedule.primitive at hinit ⊢
    linarith
  exact mul_pos (Real.exp_pos _) hfin


-- @@ L1244-1258 verbatim
theorem angularSource_hold_lower (v : TailData) {y η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hy : v.core.holdStart ≤ y) (hη : |η| ≤ 1) :
    v.core.lam / 2 - v.h ≤ angularSource v.core v.h η y := by
  have hy' : v.core.dropLength + 2 ≤ y := hy
  have hk : dropCoefficient v.core.m y = 0 :=
    dropCoefficient_late v.core.m_pos (by
      dsimp [Parameters.dropLength] at hy'
      linarith)
  have hl := slope_hold (lam := v.core.lam) v.core.dropLength_pos.le hy'
  have hW := transportW_second_ramp v.core (y := y) v.h_pos.le hh1 (by linarith) hη
  have hD : 0 ≤ D v.h := by unfold D; linarith [v.h_pos]
  have hJ : 0 ≤ η * shapeGradient η := (sq_nonneg η).trans (eta_shapeGradient_bounds hη).1
  rw [angularSource, hl, hk]
  simp only [mul_zero, add_zero, neg_neg]
  linarith [mul_le_mul_of_nonneg_left hW v.core.lam_pos.le, mul_nonneg hD hJ]


-- @@ L1260-1270 verbatim
/-- Positive incoming angular lag at every point of the unedited shaped hold. -/
theorem angularLag_pos_on_hold (v : TailData) {y η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hy : v.core.holdStart ≤ y) (hη : |η| ≤ 1) :
    0 < angularLag v.core v.h η y := by
  have hstart := angularLag_pos v.core v.h_pos.le hh1 v.core.holdStart_pos.le le_rfl hη hhT
  apply linearLag_pos_after (angularRate_contDiff v.core).continuous
    (angularSource_contDiff v.core v.h η).continuous hy hstart
  intro t ht
  have hsource := angularSource_hold_lower v hh1 ht.1 hη
  linarith [v.h_small]


-- @@ L1272-1275 verbatim
theorem angularLag_pos_at_pulseStart (v : TailData) {η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) : 0 < angularLag v.core v.h η v.core.pulseStart :=
  angularLag_pos_on_hold v hh1 hhT v.core.pulseStart_ge_hold hη


-- @@ L1277-1277 verbatim
/-! ## A parameter-uniform bound at the shaped-wait entrance -/


-- @@ L1279-1286 verbatim
theorem shape_interval {η : ℝ} (hη : |η| ≤ 1) : (1 / 2 : ℝ) ≤ shape η ∧ shape η ≤ 1 := by
  have hs := parameter_square_le_one hη
  unfold shape
  rw [← one_div]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 1 + η ^ 2)).mpr
    linarith
  · exact div_le_self (by norm_num) (by linarith [sq_nonneg η])


-- @@ L1288-1289 verbatim
/-- Entrance time, given by `Real.exp m + 12`. -/
noncomputable def entranceTime (m : ℝ) : ℝ := Real.exp m + 12


-- @@ L1291-1293 verbatim
theorem holdStart_eq_entranceTime (c : Parameters) : c.holdStart = entranceTime c.m := by
  unfold Parameters.holdStart Parameters.dropLength entranceTime
  ring


-- @@ L1295-1296 verbatim
/-- Energy envelope, given by `P ^ 2 * Real.exp (2 * T)`. -/
noncomputable def energyEnvelope (P T : ℝ) : ℝ := P ^ 2 * Real.exp (2 * T)


-- @@ L1298-1305 verbatim
theorem clockEnergy_le_envelope (c : Parameters) {y T : ℝ} (hy : 0 ≤ y) (hyT : y ≤ T) :
    clockEnergy c y ≤ energyEnvelope c.P T := by
  have hb := (OutgoingPulseBounds.radialAmplitude_bounds c hy).2
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hyT) c.P_pos.le
  have ha : 0 ≤ radialAmplitude c.P c.dropLength c.lam y :=
    (mul_pos c.P_pos (Real.exp_pos _)).le
  have hsq := pow_le_pow_left₀ ha (hb.trans he) 2
  simpa only [clockEnergy, energyEnvelope, mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat] using hsq


-- @@ L1307-1314 verbatim
theorem angular_square_le_envelope (c : Parameters) {y T η : ℝ} (hy : 0 ≤ y)
    (hyT : y ≤ T) (hη : |η| ≤ 1) :
    angular c.P c.dropLength c.lam (y, η) ^ 2 ≤ energyEnvelope c.P T := by
  have hs := shape_interval hη
  have hss : shape η ^ 2 ≤ 1 := by nlinarith [shape_pos η]
  have hb := clockEnergy_le_envelope c hy hyT
  have h := mul_le_mul hb hss (sq_nonneg _) (by unfold energyEnvelope; positivity)
  simpa only [angular, clockEnergy, mul_pow, mul_one] using h


-- @@ L1316-1331 verbatim
theorem averagedEnergy_le_envelope (c : Parameters) {y T η : ℝ} (hy : 0 ≤ y)
    (hyT : y ≤ T) (hη : |η| ≤ 1) : averagedEnergy c y η ≤ energyEnvelope c.P T := by
  have hT : 0 ≤ T := hy.trans hyT
  have hK : 0 ≤ energyEnvelope c.P T := by unfold energyEnvelope; positivity
  have he : 1 ≤ Real.exp (2 * T) := Real.one_le_exp_iff.mpr (by linarith)
  have hinit : (5 / 6 : ℝ) * c.P ^ 2 ≤ energyEnvelope c.P T := by
    unfold energyEnvelope
    linarith [sq_nonneg c.P, mul_le_mul_of_nonneg_left he (sq_nonneg c.P)]
  have hb := historyAverage_le (clockEnergy_contDiff c).continuous hinit hy
    (fun t ht => clockEnergy_le_envelope c ht.1 (ht.2.trans hyT))
  have hs := shape_interval hη
  have hss : shape η ^ 2 ≤ 1 := by nlinarith [shape_pos η]
  have hp := mul_le_mul hss hb (averagedClockEnergy_nonneg c hy) (by norm_num : (0 : ℝ) ≤ 1)
  unfold averagedEnergy
  simp only [one_mul] at hp
  exact hp


-- @@ L1333-1340 verbatim
theorem angular_lower_envelope (c : Parameters) {y T η : ℝ} (hy : 0 ≤ y)
    (hyT : y ≤ T) (hη : |η| ≤ 1) :
    c.P * Real.exp (-T) / 2 ≤ angular c.P c.dropLength c.lam (y, η) := by
  have hb := (OutgoingPulseBounds.radialAmplitude_bounds c hy).1
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hyT)) c.P_pos.le
  have hp := mul_le_mul (he.trans hb) (shape_interval hη).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by exact (mul_pos c.P_pos (Real.exp_pos _)).le)
  simpa only [angular, div_eq_mul_inv, one_div, mul_one, one_mul] using hp


-- @@ L1342-1378 verbatim
theorem pressureAxialLag_le_envelope (v : TailData) {y T η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyT : y ≤ T) (hyend : y ≤ v.core.endpoint) (hη : |η| ≤ 1) :
    |pressureAxialLag v y η| ≤ (3 + 4 * pressureBound) * |η| * energyEnvelope v.core.P T := by
  have hp := actual_pressure_bounds v hy hyend hη
  have hEE := angular_square_le_envelope v.core hy hyT hη
  have hB := averagedEnergy_le_envelope v.core hy hyT hη
  have hB0 : 0 ≤ averagedEnergy v.core y η :=
    mul_nonneg (sq_nonneg _) (averagedClockEnergy_nonneg v.core hy)
  have hK : 0 ≤ energyEnvelope v.core.P T := by unfold energyEnvelope; positivity
  have hC := pressureBound_pos.le
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by
    unfold d
    constructor <;> linarith [parameter_square_le_one hη, sq_nonneg η]
  have hA : 0 ≤ 4 * A v.h ∧ 4 * A v.h ≤ 3 := by
    unfold A
    constructor <;> linarith [v.h_pos]
  have hcoef := pressure_coefficient_bound v.h_pos.le hh1 hη
  have hp' := hp.1.trans (mul_le_mul_of_nonneg_left hEE hC)
  have hg' := hp.2.1.trans (mul_le_mul_of_nonneg_left hEE (mul_nonneg hC (abs_nonneg η)))
  unfold pressureAxialLag
  calc
    _ ≤ |-(2 * v.h * η + d η * shapeGradient η) * averagedEnergy v.core y η| +
        |4 * A v.h * η * entrancePressure v y η| + |d η * pressureGradient v y η| :=
      (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = |2 * v.h * η + d η * shapeGradient η| * averagedEnergy v.core y η +
        (4 * A v.h * |η|) * |entrancePressure v y η| + d η * |pressureGradient v y η| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hB0, abs_of_nonneg hd.1]
      rw [← abs_mul 4 (A v.h), abs_of_nonneg hA.1]
    _ ≤ (3 * |η|) * energyEnvelope v.core.P T +
        (3 * |η|) * (pressureBound * energyEnvelope v.core.P T) +
        pressureBound * |η| * energyEnvelope v.core.P T := by
      apply add_le_add
      · exact add_le_add (mul_le_mul hcoef hB hB0 (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_right hA.2 (abs_nonneg η)) hp'
            (abs_nonneg _) (by positivity))
      · simpa only [one_mul] using mul_le_mul hd.2 hg' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by ring


-- @@ L1380-1394 verbatim
theorem axialLag_le_envelope (v : TailData) {y T η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyT : y ≤ T) (hyend : y ≤ v.core.endpoint) (hη : |η| ≤ 1) :
    |axialLag v y η| ≤ 64 + (3 + 4 * pressureBound) * energyEnvelope v.core.P T := by
  have hg := geometricAxialLag_bound v.core v.h_pos.le hh1 hy hη
  have hp := pressureAxialLag_le_envelope v hh1 hy hyT hyend hη
  have hK : 0 ≤ (3 + 4 * pressureBound) * energyEnvelope v.core.P T := by
    have := pressureBound_pos
    unfold energyEnvelope
    positivity
  unfold axialLag
  apply (abs_add_le _ _).trans
  have hsum := add_le_add hg hp
  have hg1 := mul_le_mul_of_nonneg_left hη (by norm_num : (0 : ℝ) ≤ 64)
  have hp1 := mul_le_mul_of_nonneg_left hη hK
  linarith


-- @@ L1396-1399 verbatim
/-- Entrance ratio bound as an element of `ℝ`. -/
noncomputable def entranceRatioBound (P m : ℝ) : ℝ :=
  (64 + (3 + 4 * pressureBound) * energyEnvelope P (entranceTime m)) /
    ((P * Real.exp (-entranceTime m) / 2) * (coneFloor * Real.exp (-entranceTime m)))


-- @@ L1401-1405 verbatim
theorem entranceRatioBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < entranceRatioBound P m := by
  unfold entranceRatioBound energyEnvelope
  have := pressureBound_pos
  have := coneFloor_pos
  positivity


-- @@ L1407-1447 verbatim
/-- A fixed pre-`λ` bound on the ratio throughout the first ramp, drop, and
shaped-wait entrance. It depends only on the already fixed `P,m`. -/
theorem directionRatio_entrance_bound (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyT : y ≤ v.core.holdStart) (hη : |η| ≤ 1)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8) :
    |directionRatio v y η| ≤ entranceRatioBound v.core.P v.core.m := by
  have hend : y ≤ v.core.endpoint := by
    have h0 := v.core.pulseStart_ge_hold
    have h1 := v.core.pulseLength_pos
    dsimp [Parameters.endpoint]
    linarith
  have hN := axialLag_le_envelope v hh1 hy hyT hend hη
  have hE := angular_lower_envelope v.core hy hyT hη
  have hQ := angularLag_lower v.core v.h_pos.le hh1 hy hyT hη hhT
  have hQ' : coneFloor * Real.exp (-v.core.holdStart) ≤ angularLag v.core v.h η y := by
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hyT)) coneFloor_pos.le
    linarith [mul_nonneg coneFloor_pos.le (sq_nonneg η)]
  have hden := mul_le_mul hE hQ' (mul_pos coneFloor_pos (Real.exp_pos _)).le
    (angular_pos v.core.P_pos v.core.dropLength v.core.lam (y, η)).le
  have hlo : 0 < (v.core.P * Real.exp (-v.core.holdStart) / 2) *
      (coneFloor * Real.exp (-v.core.holdStart)) := by
    have := v.core.P_pos
    have := coneFloor_pos
    positivity
  have hD : 0 < angular v.core.P v.core.dropLength v.core.lam (y, η) * angularLag v.core v.h η y :=
    hlo.trans_le hden
  have hnum : 0 ≤ 64 + (3 + 4 * pressureBound) * energyEnvelope v.core.P v.core.holdStart := by
    have := pressureBound_pos
    unfold energyEnvelope
    positivity
  unfold directionRatio
  rw [abs_div, abs_of_pos hD]
  calc
    _ ≤ (64 + (3 + 4 * pressureBound) * energyEnvelope v.core.P v.core.holdStart) /
        (angular v.core.P v.core.dropLength v.core.lam (y, η) * angularLag v.core v.h η y) :=
      div_le_div_of_nonneg_right hN hD.le
    _ ≤ (64 + (3 + 4 * pressureBound) * energyEnvelope v.core.P v.core.holdStart) /
        ((v.core.P * Real.exp (-v.core.holdStart) / 2) * (coneFloor * Real.exp
            (-v.core.holdStart))) :=
      div_le_div_of_nonneg_left hnum hlo hden
    _ = _ := by rw [holdStart_eq_entranceTime]; rfl


-- @@ L1449-1449 verbatim
/-! ## Identification with the canonical, incoming-history fields -/


-- @@ L1451-1477 verbatim
theorem linearLag_eq_of_solution {r b f : ℝ → ℝ} (hr : Continuous r)
    (hb : Continuous b) {q₀ y : ℝ} (hf₀ : f 0 = q₀)
    (hf : ∀ t ∈ uIcc (0 : ℝ) y, HasDerivAt f (b t - r t * f t) t) :
    f y = linearLag r b q₀ y := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) y,
      HasDerivAt (fun t => Real.exp (OutgoingSchedule.primitive r t) * f t)
        (Real.exp (OutgoingSchedule.primitive r t) * b t) t := by
    intro t ht
    convert! ((primitive_hasDerivAt hr t).exp.mul (hf t ht)) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((Real.continuous_exp.comp (primitive_continuous_of_continuous hr)).mul hb).intervalIntegrable
        0 y)
  simp only [OutgoingSchedule.primitive, intervalIntegral.integral_same, Real.exp_zero,
    one_mul, hf₀] at hi
  change (∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * b t) =
    Real.exp (OutgoingSchedule.primitive r y) * f y - q₀ at hi
  unfold linearLag
  have he : Real.exp (-OutgoingSchedule.primitive r y) *
      Real.exp (OutgoingSchedule.primitive r y) = 1 := by rw [← Real.exp_add]; simp
  change f y = Real.exp (-OutgoingSchedule.primitive r y) *
    (q₀ + ∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * b t)
  rw [hi]
  calc
    f y = (Real.exp (-OutgoingSchedule.primitive r y) *
      Real.exp (OutgoingSchedule.primitive r y)) * f y := by rw [he, one_mul]
    _ = _ := by ring


-- @@ L1479-1482 verbatim
theorem canonical_Ubar_before (v : TailData) (Amp : ℝ → ℝ) {y : ℝ}
    (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.Ubar v Amp (y, η) = averagedDrop v.core y * η := by
  exact averagedDrop_is_mass_history v.core Amp η hy


-- @@ L1484-1490 verbatim
theorem canonical_Ubar_parameter_before (v : TailData) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.dEta (OutgoingHistories.Ubar v Amp) (y, η) = averagedDrop v.core y := by
  have he : (fun η => OutgoingHistories.Ubar v Amp (y, η)) =
      fun η => averagedDrop v.core y * η := funext (canonical_Ubar_before v Amp hy)
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Ubar_smooth v ha), he]
  simp


-- @@ L1492-1498 verbatim
theorem canonical_W_before (v : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {y : ℝ} (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.W v Amp (y, η) = transportW v.core v.h y η := by
  rw [OutgoingHistories.W_formula v ha, canonical_Ubar_before v Amp hy,
    canonical_Ubar_parameter_before v ha hy]
  simp only [transportW, L, StressAlgebra.axialExponent, StressAlgebra.coordinateFactor]
  ring


-- @@ L1500-1515 verbatim
theorem canonical_E_parameter_ratio {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {y : ℝ} (hy : y ≤ v.core.endpoint) (η : ℝ) :
    OutgoingHistories.dEta (OutgoingHistories.E w) (y, η) /
      OutgoingHistories.E w (y, η) = -shapeGradient η := by
  have he : (fun η => OutgoingHistories.E w (y, η)) =
      fun η => radialAmplitude v.core.P v.core.dropLength v.core.lam y * shape η :=
    funext (fun η => OutgoingHistories.E_before w η hy)
  have hd := (shape_hasDerivAt η).const_mul
    (radialAmplitude v.core.P v.core.dropLength v.core.lam y)
  have he' : OutgoingHistories.dEta (OutgoingHistories.E w) (y, η) =
      -shapeGradient η * OutgoingHistories.E w (y, η) := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.E_smooth w), he, hd.deriv,
      OutgoingHistories.E_before w η hy]
    simp only [angular]
    ring
  rw [he', mul_div_cancel_right₀ _ (OutgoingHistories.E_pos w (y, η)).ne']


-- @@ L1517-1535 verbatim
theorem canonical_H_radial_ratio {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {y : ℝ} (hy : y < v.core.endpoint) (η : ℝ) :
    OutgoingHistories.dY (OutgoingHistories.H w) (y, η) /
      OutgoingHistories.H w (y, η) = slope v.core.dropLength v.core.lam y := by
  have he : (fun t => OutgoingHistories.H w (t, η)) =ᶠ[𝓝 y]
      (fun t => Real.exp (t / 2) * (radialAmplitude v.core.P v.core.dropLength v.core.lam t * shape
          η)) := by
    filter_upwards [Iio_mem_nhds hy] with t ht
    simp only [OutgoingHistories.H, OutgoingHistories.E_before w η ht.le, angular]
  have hd := (((hasDerivAt_id y).div_const 2).exp).mul
    ((radialAmplitude_hasDerivAt v.core.P v.core.dropLength v.core.lam y).mul_const (shape η))
  have hd' := hd.congr_of_eventuallyEq he
  have hx := (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.H_smooth w) (y, η)).unique hd'
  have hp : OutgoingHistories.dY (OutgoingHistories.H w) (y, η) =
      slope v.core.dropLength v.core.lam y * OutgoingHistories.H w (y, η) := by
    rw [hx, OutgoingHistories.H, OutgoingHistories.E_before w η hy.le]
    simp only [angular, id_eq]
    ring
  rw [hp, mul_div_cancel_right₀ _ (OutgoingHistories.H_pos w (y, η)).ne']


-- @@ L1537-1548 verbatim
theorem canonical_Sq_before {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.Sq w Amp (y, η) = angularSource v.core v.h η y := by
  have hyend : y < v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [OutgoingHistories.Sq_formula, canonical_W_before v ha hy,
    canonical_H_radial_ratio w hyend, OutgoingHistories.U_before_pulse v Amp η hy,
    canonical_E_parameter_ratio w hyend.le]
  simp only [angularSource, StressAlgebra.axialExponent, StressAlgebra.coordinateFactor, D, d]
  ring


-- @@ L1550-1569 verbatim
/-- The positive scalar lag is exactly the canonical integrated angular stress.
No positivity or cone assumption is used in this identification. -/
theorem canonical_Qs_before {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.Qs w Amp (y, η) = angularLag v.core v.h η y := by
  unfold angularLag
  apply linearLag_eq_of_solution (f := fun t => OutgoingHistories.Qs w Amp (t, η))
    (angularRate_contDiff v.core).continuous (angularSource_contDiff v.core v.h η).continuous
  · rw [OutgoingHistories.Qs_initial w ha]
    simp only [idealAngularLag, idealAngularSource, L, D, d, shapeGradient,
      StressAlgebra.axialExponent, StressAlgebra.coordinateFactor]
  · intro t ht
    have ht' : t ≤ v.core.pulseStart := ((uIcc_of_le hy ▸ ht).2).trans hy'
    have htend : t < v.core.endpoint := by
      dsimp [Parameters.endpoint]
      linarith [v.core.pulseLength_pos]
    have hd := OutgoingHistories.Qs_hasDerivAt w ha (t, η)
    rw [canonical_Sq_before w ha ht', canonical_H_radial_ratio w htend] at hd
    exact hd


-- @@ L1571-1578 verbatim
theorem canonical_Qs_pos_at_pulseStart {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    {η : ℝ} (hη : |η| ≤ 1) :
    0 < OutgoingHistories.Qs w Amp (v.core.pulseStart, η) := by
  rw [canonical_Qs_before w ha v.core.pulseStart_pos.le le_rfl]
  exact angularLag_pos_at_pulseStart v hh1 hhT hη


-- @@ L1580-1598 verbatim
theorem canonical_Pi_before {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {y : ℝ}
    (hy : y ≤ v.core.endpoint) (η : ℝ) :
    OutgoingHistories.Pi w (y, η) = entrancePressure v y η := by
  have hi : (∫ t in (0 : ℝ)..y, OutgoingHistories.pressureWeight w (t, η)) =
      (shape η ^ 2 / 2) * ∫ t in (0 : ℝ)..y, clockEnergy v.core t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ v.core.endpoint :=
      ht.2.trans (max_le (SchedulePressure.endpoint_pos v).le hy)
    simp only [OutgoingHistories.pressureWeight, OutgoingHistories.E_before w η ht',
      angular, clockEnergy]
    ring
  change OutgoingHistories.initialPi v η +
    (∫ t in (0 : ℝ)..y, OutgoingHistories.pressureWeight w (t, η)) = _
  rw [hi]
  unfold OutgoingHistories.initialPi entrancePressure pressureClock OutgoingSchedule.primitive
  ring


-- @@ L1600-1632 verbatim
theorem canonical_S_before {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) (Amp : ℝ → ℝ) {y : ℝ}
    (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.S w Amp (y, η) / Real.exp y = normalizedEnergyHistory v.core y η := by
  have hk : IntervalIntegrable (fun t => Real.exp t * dropCoefficient v.core.m t ^ 2) volume 0 y :=
    (Real.continuous_exp.fun_mul ((dropCoefficient_contDiff v.core.m_pos).continuous.pow
        2)).intervalIntegrable 0 y
  have he : IntervalIntegrable (fun t => Real.exp t * clockEnergy v.core t) volume 0 y :=
    (Real.continuous_exp.fun_mul (clockEnergy_contDiff v.core).continuous).intervalIntegrable 0 y
  have hi : (∫ t in (0 : ℝ)..y, OutgoingHistories.energyWeight w Amp (t, η)) =
      η ^ 2 * (∫ t in (0 : ℝ)..y, Real.exp t * dropCoefficient v.core.m t ^ 2) -
        (shape η ^ 2 / 2) * ∫ t in (0 : ℝ)..y, Real.exp t * clockEnergy v.core t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hk.const_mul _) (he.const_mul _)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ v.core.pulseStart :=
      ht.2.trans (max_le v.core.pulseStart_pos.le hy)
    have htend : t ≤ v.core.endpoint := by
      dsimp [Parameters.endpoint]
      linarith [v.core.pulseLength_pos]
    simp only [OutgoingHistories.energyWeight, OutgoingHistories.energyDensity,
      OutgoingHistories.X, OutgoingHistories.U_before_pulse v Amp η ht',
      OutgoingHistories.E_before w η htend, angular, clockEnergy]
    ring
  change (OutgoingHistories.initialS v η +
    (∫ t in (0 : ℝ)..y, OutgoingHistories.energyWeight w Amp (t, η))) / Real.exp y = _
  rw [hi]
  unfold normalizedEnergyHistory averagedDropSquare averagedEnergy averagedClockEnergy
  rw [historyAverage_formula, historyAverage_formula]
  unfold OutgoingHistories.initialS
  rw [Real.exp_neg]
  ring


-- @@ L1634-1639 verbatim
theorem canonical_M_before (v : TailData) (Amp : ℝ → ℝ) {y : ℝ}
    (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.M v Amp (y, η) = Real.exp y * (averagedDrop v.core y * η) := by
  have he := canonical_Ubar_before v Amp hy η
  change OutgoingHistories.M v Amp (y, η) / Real.exp y = _ at he
  exact (div_eq_iff (Real.exp_pos y).ne').mp he |>.trans (by ring)


-- @@ L1641-1676 verbatim
theorem canonical_Ns_before {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.Ns w Amp (y, η) = axialLag v y η := by
  have hyend : y ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hM : (fun η => OutgoingHistories.M v Amp (y, η)) =
      fun η => Real.exp y * (averagedDrop v.core y * η) :=
    funext (canonical_M_before v Amp hy)
  have hMd : OutgoingHistories.dEta (OutgoingHistories.M v Amp) (y, η) =
      Real.exp y * averagedDrop v.core y := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.M_smooth v ha), hM]
    simp
  have hS : (fun η => OutgoingHistories.S w Amp (y, η)) =
      fun η => Real.exp y * normalizedEnergyHistory v.core y η := by
    funext η
    have hs := (div_eq_iff (Real.exp_pos y).ne').mp (canonical_S_before w Amp hy η)
    exact hs.trans (by ring)
  have hSd : OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, η) =
      Real.exp y * deriv (normalizedEnergyHistory v.core y) η := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.S_smooth w ha), hS,
      ((normalizedEnergyHistory_hasDerivAt_eta v.core y η).const_mul (Real.exp y)).deriv,
      (normalizedEnergyHistory_hasDerivAt_eta v.core y η).deriv]
  have hP : (fun η => OutgoingHistories.Pi w (y, η)) = entrancePressure v y :=
    funext (canonical_Pi_before w hyend)
  have hPd : OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, η) =
      deriv (entrancePressure v y) η := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Pi_smooth w), hP]
  rw [OutgoingHistories.Ns_integrated, canonical_W_before v ha hy,
    OutgoingHistories.U_before_pulse v Amp η hy, canonical_M_before v Amp hy,
    hMd, congrFun hS η, hSd, canonical_Pi_before w hyend, hPd,
    axialLag_integrated_history]
  simp only [OutgoingHistories.X, StressAlgebra.axialExponent,
    StressAlgebra.coordinateFactor, StressAlgebra.velocityExponent, d, A]
  field_simp [(Real.exp_pos y).ne']; ring


-- @@ L1678-1678 verbatim
/-! ## The first and last preliminary ramps -/


-- @@ L1680-1689 verbatim
theorem dropCoefficient_deriv_early {m y : ℝ} (hm : 0 < m) (hy : y ≤ 1) :
    deriv (dropCoefficient m) y = 0 := by
  have he : Set.EqOn (deriv (dropCoefficient m)) (fun _ => 0) (Iio 1) := by
    intro t ht
    have hf : dropCoefficient m =ᶠ[𝓝 t] (fun _ => 4) := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact dropCoefficient_early m hx.le
    exact ((hasDerivAt_const t (4 : ℝ)).congr_of_eventuallyEq hf).deriv
  have hc := he.closure ((dropCoefficient_contDiff hm).continuous_deriv (by simp)) continuous_const
  exact hc (by rw [closure_Iio]; exact hy)


-- @@ L1691-1696 verbatim
theorem dropCoefficient_deriv_late {m y : ℝ} (hm : 0 < m) (hy : Real.exp m < y) :
    deriv (dropCoefficient m) y = 0 := by
  have hf : dropCoefficient m =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact dropCoefficient_late hm ht.le
  exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hf).deriv


-- @@ L1698-1699 verbatim
theorem shear_early (c : Parameters) {y : ℝ} (hy : y ≤ 1) (η : ℝ) : shear c y η = 0 := by
  simp only [shear, dropCoefficient_deriv_early c.m_pos hy, mul_zero, zero_mul, zero_div]


-- @@ L1701-1704 verbatim
theorem shear_second_ramp (c : Parameters) {y : ℝ} (hy : c.dropLength + 1 ≤ y) (η : ℝ) :
    shear c y η = 0 := by
  have he : Real.exp c.m < y := by dsimp [Parameters.dropLength] at hy; linarith
  simp only [shear, dropCoefficient_deriv_late c.m_pos he, mul_zero, zero_mul, zero_div]


-- @@ L1706-1711 verbatim
theorem radialA_bounds (c : Parameters) (y : ℝ) : (4 / 5 : ℝ) ≤ radialA c y ∧ radialA c y ≤ 11 / 5
    := by
  have hb := angularRate_bounds c y
  unfold angularRate at hb
  unfold radialA
  constructor <;> linarith


-- @@ L1713-1719 verbatim
theorem radialA_upper_lam (c : Parameters) {y : ℝ} (hy : 1 ≤ y) :
    radialA c y ≤ 2 + 2 * c.lam := by
  have hs : slope c.dropLength c.lam y = -c.lam * sigma (y - (c.dropLength + 1)) := by
    simp [OutgoingSchedule.slope, sigma_one hy]
  unfold radialA
  rw [hs]
  nlinarith [sigma_le_one (y - (c.dropLength + 1)), c.lam_pos]


-- @@ L1721-1733 verbatim
theorem first_ramp_cone_margins (v : TailData) {y : ℝ} (hy : y ≤ 1) (η : ℝ) :
    (4 / 5 : ℝ) ≤ radialA v.core y - shear v.core y η * directionRatio v y η ∧
      2 * shear v.core y η * directionRatio v y η + shear v.core y η ^ 2 / radialA v.core y +
        (radialA v.core y - 2) * directionRatio v y η ^ 2 ≤ 0 := by
  have ha : radialA v.core y ≤ 2 := by
    have hs := slope_nonneg_before_dropEnd v.core (hy.trans (by linarith [v.core.dropLength_pos]))
    unfold radialA
    linarith
  rw [shear_early v.core hy]
  simp only [zero_mul, mul_zero, sub_zero, zero_pow (by
      decide : (2 : ℕ) ≠ 0), zero_div, zero_add, add_zero]
  refine ⟨(radialA_bounds v.core y).1, ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha) (sq_nonneg _)


-- @@ L1735-1755 verbatim
theorem second_ramp_cone_margins (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : v.core.dropLength + 1 ≤ y) (hyT : y ≤ v.core.holdStart) (hη : |η| ≤ 1)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hlam : v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4) :
    (2 : ℝ) ≤ radialA v.core y - shear v.core y η * directionRatio v y η ∧
      2 * shear v.core y η * directionRatio v y η + shear v.core y η ^ 2 / radialA v.core y +
        (radialA v.core y - 2) * directionRatio v y η ^ 2 ≤ 1 / 2 := by
  have hy1 : 1 ≤ y := by linarith [v.core.dropLength_pos]
  have hs := slope_nonpos_after_first_ramp v.core hy1
  have ha : 2 ≤ radialA v.core y := by unfold radialA; linarith
  have ha' := radialA_upper_lam v.core hy1
  have hw := directionRatio_entrance_bound v hh1 (by linarith) hyT hη hhT
  have hw2 : directionRatio v y η ^ 2 ≤ entranceRatioBound v.core.P v.core.m ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  rw [shear_second_ramp v.core hy]
  simp only [zero_mul, mul_zero, sub_zero, zero_pow (by
      decide : (2 : ℕ) ≠ 0), zero_div, zero_add, add_zero]
  refine ⟨ha, ?_⟩
  have hmul := mul_le_mul (show radialA v.core y - 2 ≤ 2 * v.core.lam by linarith)
    hw2 (sq_nonneg _) (by linarith [v.core.lam_pos])
  linarith


-- @@ L1757-1757 verbatim
/-! ## Uniform pressure-source estimates -/


-- @@ L1759-1762 verbatim
theorem pressureGradient_contDiff_eta (v : TailData) (y : ℝ) :
    ContDiff ℝ ∞ (pressureGradient v y) := by
  exact (contDiff_infty_iff_deriv.mp (SchedulePressure.axisPressure_contDiff v)).2.sub
    ((((contDiff_const.mul shapeGradient_contDiff).mul (shape_contDiff.pow 2))).mul contDiff_const)


-- @@ L1764-1769 verbatim
theorem angularSquare_hasDerivAt_eta (c : Parameters) (y η : ℝ) :
    HasDerivAt (fun t => angular c.P c.dropLength c.lam (y, t) ^ 2)
      (-2 * shapeGradient η * angular c.P c.dropLength c.lam (y, η) ^ 2) η := by
  convert! ((shape_hasDerivAt η).const_mul (radialAmplitude c.P c.dropLength c.lam y)).pow 2 using 1
  simp only [angular]
  ring


-- @@ L1771-1786 verbatim
theorem pressureAxialSource_hasDerivAt_eta (v : TailData) (y η : ℝ) :
    HasDerivAt (pressureAxialSource v y)
      ((2 + 4 * A v.h) * η * pressureGradient v y η -
        d η * deriv (pressureGradient v y) η + 4 * A v.h * entrancePressure v y η +
          (1 - 2 * η * shapeGradient η) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2)
              η := by
  have hd : HasDerivAt d (-2 * η) η := by
    convert! (hasDerivAt_const η (1 : ℝ)).fun_sub ((hasDerivAt_id η).fun_pow 2) using 1
    simp []
  have hp := ((pressureGradient_contDiff_eta v y).differentiable (by simp) η).hasDerivAt
  convert! ((hd.fun_neg.fun_mul hp).fun_add
    (((hasDerivAt_id η).const_mul (4 * A v.h)).fun_mul (entrancePressure_hasDerivAt_eta v y
        η))).fun_add
      ((hasDerivAt_id η).fun_mul (angularSquare_hasDerivAt_eta v.core y η)) using 1
  simp only [id_eq]
  ring


-- @@ L1788-1789 verbatim
/-- Pressure source bound, given by `10 * pressureBound + 10`. -/
noncomputable def pressureSourceBound : ℝ := 10 * pressureBound + 10


-- @@ L1791-1793 verbatim
theorem pressureSourceBound_pos : 0 < pressureSourceBound := by
  unfold pressureSourceBound
  linarith [pressureBound_pos]


-- @@ L1795-1829 verbatim
theorem pressureAxialSource_bound (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyend : y ≤ v.core.endpoint) (hη : |η| ≤ 1) :
    |pressureAxialSource v y η| ≤ pressureSourceBound * |η| *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
  have hp := actual_pressure_bounds v hy hyend hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by
    unfold d
    constructor <;> linarith [sq_nonneg η, parameter_square_le_one hη]
  have hA : 0 ≤ 4 * A v.h ∧ 4 * A v.h ≤ 3 := by
    unfold A
    constructor <;> linarith [v.h_pos]
  have hfirst : |-d η * pressureGradient v y η| ≤
      pressureBound * |η| * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hd.1]
    simpa only [one_mul] using mul_le_mul hd.2 hp.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsecond : |4 * A v.h * η * entrancePressure v y η| ≤
      3 * pressureBound * |η| * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hA.1]
    have hb := mul_le_mul (mul_le_mul_of_nonneg_right hA.2 (abs_nonneg η)) hp.1
      (abs_nonneg _) (by positivity : 0 ≤ 3 * |η|)
    linarith
  have hthird : |η * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2| =
      |η| * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    simp only [abs_mul, abs_pow, sq_abs]
  unfold pressureAxialSource
  have hs : |-d η * pressureGradient v y η + 4 * A v.h * η * entrancePressure v y η +
      η * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2| ≤
      |-d η * pressureGradient v y η| + |4 * A v.h * η * entrancePressure v y η| +
        |η * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2| :=
    (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  rw [hthird] at hs
  unfold pressureSourceBound
  have hn := mul_nonneg (abs_nonneg η) (sq_nonneg (angular v.core.P v.core.dropLength v.core.lam
      (y, η)))
  linarith [mul_nonneg pressureBound_pos.le hn]


-- @@ L1831-1883 verbatim
theorem pressureAxialSource_deriv_bound (v : TailData) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyend : y ≤ v.core.endpoint) (hη : |η| ≤ 1) :
    |deriv (pressureAxialSource v y) η| ≤ pressureSourceBound *
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
  have hp := actual_pressure_bounds v hy hyend hη
  have hE := sq_nonneg (angular v.core.P v.core.dropLength v.core.lam (y, η))
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by
    unfold d
    constructor <;> linarith [sq_nonneg η, parameter_square_le_one hη]
  have hA : 0 ≤ 4 * A v.h ∧ 4 * A v.h ≤ 3 := by
    unfold A
    constructor <;> linarith [v.h_pos]
  have hp1 : |pressureGradient v y η| ≤ pressureBound * angular v.core.P v.core.dropLength
      v.core.lam (y, η) ^ 2 := by
    apply hp.2.1.trans
    linarith [mul_le_mul_of_nonneg_right hη (mul_nonneg pressureBound_pos.le hE)]
  have hfirst : |(2 + 4 * A v.h) * η * pressureGradient v y η| ≤
      5 * pressureBound * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 + 4 * A v.h)]
    have hc : (2 + 4 * A v.h) * |η| ≤ 5 := by
      linarith [mul_le_mul_of_nonneg_left hη (by linarith : 0 ≤ 2 + 4 * A v.h)]
    have hb := mul_le_mul hc hp1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
    linarith
  have hsecond : |d η * deriv (pressureGradient v y) η| ≤
      pressureBound * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hd.1]
    simpa only [one_mul] using mul_le_mul hd.2 hp.2.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hthird : |4 * A v.h * entrancePressure v y η| ≤
      3 * pressureBound * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hA.1]
    have hb := mul_le_mul hA.2 hp.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hc : |1 - 2 * η * shapeGradient η| ≤ 1 := by
    apply abs_le.mpr
    have hb := eta_shapeGradient_bounds hη
    constructor <;> linarith [sq_nonneg η]
  have hfourth : |(1 - 2 * η * shapeGradient η) * angular v.core.P v.core.dropLength v.core.lam (y,
      η) ^ 2| ≤
      angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hE]
    exact (mul_le_mul_of_nonneg_right hc hE).trans_eq (one_mul _)
  rw [(pressureAxialSource_hasDerivAt_eta v y η).deriv]
  have hs : |(2 + 4 * A v.h) * η * pressureGradient v y η -
      d η * deriv (pressureGradient v y) η + 4 * A v.h * entrancePressure v y η +
        (1 - 2 * η * shapeGradient η) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2| ≤
      |(2 + 4 * A v.h) * η * pressureGradient v y η| +
        |d η * deriv (pressureGradient v y) η| + |4 * A v.h * entrancePressure v y η| +
          |(1 - 2 * η * shapeGradient η) * angular v.core.P v.core.dropLength v.core.lam (y, η) ^
              2| :=
    (abs_add_le _ _).trans (add_le_add_left
      ((abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)) _)
  unfold pressureSourceBound
  linarith [mul_nonneg pressureBound_pos.le hE]


-- @@ L1885-1885 verbatim
/-! ## A single ordered choice of the preliminary parameters -/


-- @@ L1887-1888 verbatim
/-- Drop threshold, given by `min (1 / 8) (coneFloor / (16 * axialBound))`. -/
noncomputable def dropThreshold : ℝ := min (1 / 8) (coneFloor / (16 * axialBound))

-- @@ L1889-1890 verbatim
/-- Amplitude threshold, given by `Real.exp (Real.exp m + 11) + 1`. -/
noncomputable def amplitudeThreshold (m : ℝ) : ℝ := Real.exp (Real.exp m + 11) + 1

-- @@ L1891-1893 verbatim
/-- Lambda threshold, given by `min (1 / 20) (1 / (4 * (entranceRatioBound P m ^ 2 + 1)))`. -/
noncomputable def lambdaThreshold (P m : ℝ) : ℝ :=
  min (1 / 20) (1 / (4 * (entranceRatioBound P m ^ 2 + 1)))

-- @@ L1894-1897 verbatim
/-- Height threshold, given by `min (1 / 100) (min (lam / 4) (Real.exp (-(entranceTime m + 3 /
5)) / 8))`. -/
noncomputable def heightThreshold (m lam : ℝ) : ℝ :=
  min (1 / 100) (min (lam / 4) (Real.exp (-(entranceTime m + 3 / 5)) / 8))


-- @@ L1899-1900 verbatim
theorem dropThreshold_pos : 0 < dropThreshold := by
  exact lt_min (by norm_num) (div_pos coneFloor_pos (mul_pos (by norm_num) axialBound_pos))

-- @@ L1901-1903 verbatim
theorem amplitudeThreshold_pos (m : ℝ) : 0 < amplitudeThreshold m := by
  unfold amplitudeThreshold
  positivity

-- @@ L1904-1906 verbatim
theorem lambdaThreshold_pos (P m : ℝ) : 0 < lambdaThreshold P m := by
  unfold lambdaThreshold
  positivity

-- @@ L1907-1909 verbatim
theorem heightThreshold_pos (m : ℝ) {lam : ℝ} (hlam : 0 < lam) : 0 < heightThreshold m lam := by
  unfold heightThreshold
  positivity


-- @@ L1911-1927 verbatim
theorem preliminary_cone_margins (v : TailData) {y η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (_hy : 0 ≤ y) (hyT : y ≤ v.core.holdStart) (hη : |η| ≤ 1)
    (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (he : dropSpeed v.core.m ≤ dropThreshold)
    (hlam : v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4) :
    (4 / 5 : ℝ) ≤ radialA v.core y - shear v.core y η * directionRatio v y η ∧
      2 * shear v.core y η * directionRatio v y η + shear v.core y η ^ 2 / radialA v.core y +
        (radialA v.core y - 2) * directionRatio v y η ^ 2 ≤ 5 / 8 := by
  by_cases hfirst : y ≤ 1
  · have hm := first_ramp_cone_margins v hfirst η
    exact ⟨hm.1, hm.2.trans (by norm_num)⟩
  by_cases hdrop : y ≤ v.core.dropLength + 1
  · have hm := drop_cone_margins v hh1 (le_of_not_ge hfirst) hdrop hη hP hhT he
    exact ⟨(by norm_num : (4 / 5 : ℝ) ≤ 7 / 4).trans hm.1, hm.2⟩
  · have hm := second_ramp_cone_margins v hh1 (le_of_not_ge hdrop) hyT hη hhT hlam
    exact ⟨(by norm_num : (4 / 5 : ℝ) ≤ 2).trans hm.1, hm.2.trans (by norm_num)⟩


-- @@ L1929-1950 verbatim
theorem chosen_parameters_bounds (v : TailData)
    (hP : amplitudeThreshold v.core.m ≤ v.core.P)
    (hlam : v.core.lam ≤ lambdaThreshold v.core.P v.core.m)
    (hh : v.h ≤ heightThreshold v.core.m v.core.lam) :
    Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2 ∧
      v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4 ∧
      v.h ≤ 1 / 100 ∧ v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8 := by
  have hp : Real.exp (Real.exp v.core.m + 11) + 1 ≤ v.core.P := hP
  have hp' : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2 := by
    have he := Real.exp_pos (Real.exp v.core.m + 11)
    have harg : v.core.dropLength + 1 = Real.exp v.core.m + 11 := by
      simp only [Parameters.dropLength]
      ring
    rw [harg]
    nlinarith
  have hl : v.core.lam ≤ 1 / (4 * (entranceRatioBound v.core.P v.core.m ^ 2 + 1)) :=
    hlam.trans (min_le_right _ _)
  have hl' := (le_div_iff₀ (show 0 < 4 * (entranceRatioBound v.core.P v.core.m ^ 2 + 1) by
      positivity)).mp hl
  refine ⟨hp', (by linarith [v.core.lam_pos]), hh.trans (min_le_left _ _), ?_⟩
  rw [holdStart_eq_entranceTime]
  exact hh.trans ((min_le_right _ _).trans (min_le_right _ _))


-- @@ L1952-1969 verbatim
/-- The drop is chosen first. All subsequent cutoffs display precisely which
earlier parameters they depend on; the cone constants are absolute. -/
theorem exists_ordered_preliminary_bounds :
    ∃ M : ℝ, 0 < M ∧ ∀ v : TailData, M ≤ v.core.m →
      amplitudeThreshold v.core.m ≤ v.core.P →
      v.core.lam ≤ lambdaThreshold v.core.P v.core.m →
      v.h ≤ heightThreshold v.core.m v.core.lam →
      ∀ y η : ℝ, 0 ≤ y → y ≤ v.core.holdStart → |η| ≤ 1 →
        coneFloor * (η ^ 2 + Real.exp (-y)) ≤ angularLag v.core v.h η y ∧
        (4 / 5 : ℝ) ≤ radialA v.core y - shear v.core y η * directionRatio v y η ∧
        2 * shear v.core y η * directionRatio v y η + shear v.core y η ^ 2 / radialA v.core y +
          (radialA v.core y - 2) * directionRatio v y η ^ 2 ≤ 5 / 8 := by
  obtain ⟨M, hM, hsmall⟩ := exists_small_dropSpeed dropThreshold_pos
  refine ⟨M, hM, ?_⟩
  intro v hm hP hlam hh y η hy hyT hη
  have hb := chosen_parameters_bounds v hP hlam hh
  exact ⟨angularLag_lower v.core v.h_pos.le hb.2.2.1 hy hyT hη hb.2.2.2,
    preliminary_cone_margins v hb.2.2.1 hy hyT hη hb.1 hb.2.2.2 (hsmall _ hm) hb.2.1⟩


-- @@ L1971-1971 verbatim
/-! ## The actual stress-cone fields and finite amplitude -/


-- @@ L1973-1977 verbatim
/-- Cone A, given by `2 - 2 * (OutgoingHistories.dY (OutgoingHistories.H w) p /
OutgoingHistories.H w p)`. -/
noncomputable def coneA {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) (p : ℝ × ℝ) : ℝ :=
  2 - 2 * (OutgoingHistories.dY (OutgoingHistories.H w) p / OutgoingHistories.H w p)


-- @@ L1979-1983 verbatim
/-- Cone B, given by `2 * OutgoingHistories.dY (OutgoingHistories.U v Amp) p /
OutgoingHistories.E w p`. -/
noncomputable def coneB {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * OutgoingHistories.dY (OutgoingHistories.U v Amp) p / OutgoingHistories.E w p


-- @@ L1985-1989 verbatim
/-- Cone ratio, given by `OutgoingHistories.Ns w Amp p / (OutgoingHistories.E w p *
OutgoingHistories.Qs w Amp p)`. -/
noncomputable def coneRatio {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) (Amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  OutgoingHistories.Ns w Amp p / (OutgoingHistories.E w p * OutgoingHistories.Qs w Amp p)


-- @@ L1991-1993 verbatim
/-- Preliminary window, given by `Icc 0 v.core.holdStart ×ˢ Icc (-1) 1`. -/
noncomputable def preliminaryWindow (v : TailData) : Set (ℝ × ℝ) :=
  Icc 0 v.core.holdStart ×ˢ Icc (-1) 1


-- @@ L1995-1998 verbatim
theorem coneA_before {v : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness v K)
    {y : ℝ} (hy : y < v.core.endpoint) (η : ℝ) : coneA w (y, η) = radialA v.core y := by
  unfold coneA radialA
  rw [canonical_H_radial_ratio w hy]


-- @@ L2000-2008 verbatim
theorem coneB_before {v : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness v K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y < v.core.pulseStart) (η : ℝ) :
    coneB w Amp (y, η) = shear v.core y η := by
  have hyend : y ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [coneB, OutgoingHistories.dY_eq_deriv (OutgoingHistories.U_smooth v ha),
    OutgoingHistories.E_before w η hyend]
  exact (shear_is_actual v.core Amp hy η).symm


-- @@ L2010-2019 verbatim
theorem coneRatio_before {v : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness v K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : 0 ≤ y)
    (hy' : y ≤ v.core.pulseStart) (η : ℝ) :
    coneRatio w Amp (y, η) = directionRatio v y η := by
  have hyend : y ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [coneRatio, canonical_Ns_before w ha hy', canonical_Qs_before w ha hy hy',
    OutgoingHistories.E_before w η hyend]
  rfl


-- @@ L2021-2028 verbatim
theorem canonical_Qs_lower {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyT : y ≤ v.core.holdStart) (hη : |η| ≤ 1)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8) :
    coneFloor * (η ^ 2 + Real.exp (-y)) ≤ OutgoingHistories.Qs w Amp (y, η) := by
  rw [canonical_Qs_before w ha hy (hyT.trans v.core.pulseStart_ge_hold)]
  exact angularLag_lower v.core v.h_pos.le hh1 hy hyT hη hhT


-- @@ L2030-2037 verbatim
theorem canonical_Qs_pos {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y η : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hy : 0 ≤ y) (hyT : y ≤ v.core.holdStart) (hη : |η| ≤ 1)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8) :
    0 < OutgoingHistories.Qs w Amp (y, η) :=
  (mul_pos coneFloor_pos (add_pos_of_nonneg_of_pos (sq_nonneg η) (Real.exp_pos _))).trans_le
    (canonical_Qs_lower w ha hh1 hy hyT hη hhT)


-- @@ L2039-2043 verbatim
theorem coneA_continuous {v : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness v K) :
    Continuous (coneA w) := by
  exact continuous_const.sub (continuous_const.mul
    ((OutgoingHistories.dY_smooth (OutgoingHistories.H_smooth w)).continuous.div
      (OutgoingHistories.H_smooth w).continuous (fun p => (OutgoingHistories.H_pos w p).ne')))


-- @@ L2045-2049 verbatim
theorem coneB_continuous {v : TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness v K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) : Continuous (coneB w Amp) := by
  exact (continuous_const.mul (OutgoingHistories.dY_smooth (OutgoingHistories.U_smooth v
      ha)).continuous).div
    (OutgoingHistories.E_smooth w).continuous (fun p => (OutgoingHistories.E_pos w p).ne')


-- @@ L2051-2061 verbatim
theorem coneRatio_continuousOn {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8) :
    ContinuousOn (coneRatio w Amp) (preliminaryWindow v) := by
  apply (OutgoingHistories.Ns_smooth w ha).continuous.continuousOn.div
    ((OutgoingHistories.E_smooth w).continuous.mul (OutgoingHistories.Qs_smooth w
        ha).continuous).continuousOn
  rintro ⟨y, η⟩ ⟨hy, hη⟩
  exact (mul_pos (OutgoingHistories.E_pos w (y, η))
    (canonical_Qs_pos w ha hh1 hy.1 hy.2 (abs_le.mpr hη) hhT)).ne'


-- @@ L2063-2083 verbatim
theorem actual_preliminary_margins {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (he : dropSpeed v.core.m ≤ dropThreshold)
    (hlam : v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4)
    {p : ℝ × ℝ} (hp : p ∈ preliminaryWindow v) :
    (4 / 5 : ℝ) ≤ coneA w p - coneB w Amp p * coneRatio w Amp p ∧
      2 * coneB w Amp p * coneRatio w Amp p + coneB w Amp p ^ 2 / coneA w p +
        (coneA w p - 2) * coneRatio w Amp p ^ 2 ≤ 5 / 8 := by
  rcases p with ⟨y, η⟩
  rcases hp with ⟨hy, hη⟩
  have hyp : y < v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith [hy.2, v.core.wait_gt]
  have hye : y < v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [coneA_before w hye, coneB_before w ha hyp, coneRatio_before w ha hy.1 hyp.le]
  exact preliminary_cone_margins v hh1 hy.1 hy.2 (abs_le.mpr hη) hP hhT he hlam


-- @@ L2085-2114 verbatim
/-- Uniform finite-amplitude relaxed cone for the actual history stresses on
the whole preliminary interval. Both root inequalities have a common gap. -/
theorem compact_actual_preliminary_cone {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (he : dropSpeed v.core.m ≤ dropThreshold)
    (hlam : v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4) :
    ∃ gap p₀ : ℝ, 0 < gap ∧ 0 ≤ p₀ ∧ ∀ s : ℝ, p₀ < s →
      ∀ p ∈ preliminaryWindow v,
        2 + gap < s * (1 - coneB w Amp p * coneRatio w Amp p / coneA w p) ∧
        coneA w p * (1 + (coneB w Amp p / coneA w p) ^ 2) + gap <
          ConeAlgebra.coneBound (s * (1 - coneB w Amp p * coneRatio w Amp p / coneA w p))
            (s * (coneRatio w Amp p + coneB w Amp p / coneA w p)) := by
  apply UniformCone.compact_equation_eleven_gap (isCompact_Icc.prod isCompact_Icc)
    (coneA_continuous w).continuousOn (coneB_continuous w ha).continuousOn
    (coneRatio_continuousOn w ha hh1 hhT)
  · rintro ⟨y, η⟩ ⟨hy, _⟩
    have hye : y < v.core.endpoint := by
      have hyp := v.core.pulseStart_ge_hold
      dsimp [Parameters.endpoint]
      linarith [hy.2, v.core.pulseLength_pos]
    rw [coneA_before w hye]
    exact (by norm_num : (0 : ℝ) < 4 / 5).trans_le (radialA_bounds v.core y).1
  · intro p hp
    exact (by norm_num : (0 : ℝ) < 4 / 5).trans_le
      (actual_preliminary_margins w ha hh1 hP hhT he hlam hp).1
  · intro p hp
    exact (actual_preliminary_margins w ha hh1 hP hhT he hlam hp).2.trans_lt (by norm_num)


-- @@ L2116-2140 verbatim
theorem actual_stress_amplitude_lower {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    {XR : ℝ} (hXR : 0 ≤ XR) {p : ℝ × ℝ} (hp : p ∈ preliminaryWindow v) :
    XR * coneFloor ≤ OutgoingHistories.p1 XR w Amp p := by
  rcases p with ⟨y, η⟩
  rcases hp with ⟨hy, hη⟩
  have hq := canonical_Qs_lower w ha hh1 hy.1 hy.2 (abs_le.mpr hη) hhT
  have hL := natural_L_bounds v.h_pos.le hh1 (abs_le.mpr hη)
  have hL0 : 0 < L v.h η := (by norm_num : (0 : ℝ) < 49 / 50).trans_le hL.1
  have hx : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hq' : coneFloor ≤ Real.exp y * OutgoingHistories.Qs w Amp (y, η) := by
    have hb := mul_le_mul_of_nonneg_left hq (Real.exp_pos y).le
    have he : Real.exp y * (coneFloor * Real.exp (-y)) = coneFloor := by
      calc
        _ = coneFloor * (Real.exp y * Real.exp (-y)) := by ring
        _ = _ := by rw [hx, mul_one]
    have heta := mul_nonneg (Real.exp_pos y).le (mul_nonneg coneFloor_pos.le (sq_nonneg η))
    linarith
  change XR * coneFloor ≤ XR * Real.exp y * OutgoingHistories.Qs w Amp (y, η) / L v.h η
  apply (le_div_iff₀ hL0).mpr
  have hleft := mul_le_mul_of_nonneg_left hL.2 (mul_nonneg hXR coneFloor_pos.le)
  have hright := mul_le_mul_of_nonneg_left hq' hXR
  linarith


-- @@ L2142-2168 verbatim
/-- A single large physical radial scale gives the actual relaxed cone,
uniformly in the complete first-ramp/drop/entrance region. -/
theorem exists_actual_preliminary_cone_scale {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100)
    (hP : Real.exp (v.core.dropLength + 1) ≤ v.core.P ^ 2)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (he : dropSpeed v.core.m ≤ dropThreshold)
    (hlam : v.core.lam * entranceRatioBound v.core.P v.core.m ^ 2 ≤ 1 / 4) :
    ∃ gap XR₀ : ℝ, 0 < gap ∧ 0 < XR₀ ∧ ∀ XR : ℝ, XR₀ < XR →
      ∀ p ∈ preliminaryWindow v,
        2 + gap < OutgoingHistories.p1 XR w Amp p *
          (1 - coneB w Amp p * coneRatio w Amp p / coneA w p) ∧
        coneA w p * (1 + (coneB w Amp p / coneA w p) ^ 2) + gap <
          ConeAlgebra.coneBound
            (OutgoingHistories.p1 XR w Amp p * (1 - coneB w Amp p * coneRatio w Amp p / coneA w p))
            (OutgoingHistories.p1 XR w Amp p * (coneRatio w Amp p + coneB w Amp p / coneA w p)) :=
                by
  obtain ⟨gap, p₀, hg, hp₀, hcone⟩ := compact_actual_preliminary_cone w ha hh1 hP hhT he hlam
  refine ⟨gap, (p₀ + 1) / coneFloor, hg, div_pos (by linarith) coneFloor_pos, ?_⟩
  intro XR hXR p hp
  have hXR0 : 0 < XR := (div_pos (by linarith : 0 < p₀ + 1) coneFloor_pos).trans hXR
  have hs : p₀ < OutgoingHistories.p1 XR w Amp p := by
    have hx := (div_lt_iff₀ coneFloor_pos).mp hXR
    exact (by linarith : p₀ < XR * coneFloor).trans_le
      (actual_stress_amplitude_lower w ha hh1 hhT hXR0.le hp)
  exact hcone _ hs p hp


-- @@ L2170-2188 verbatim
/-- The same canonical identification is valid to the left of clock zero. -/
theorem canonical_Qs_before_all {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ v.core.pulseStart) (η : ℝ) :
    OutgoingHistories.Qs w Amp (y, η) = angularLag v.core v.h η y := by
  unfold angularLag
  apply linearLag_eq_of_solution (f := fun t => OutgoingHistories.Qs w Amp (t, η))
    (angularRate_contDiff v.core).continuous (angularSource_contDiff v.core v.h η).continuous
  · rw [OutgoingHistories.Qs_initial w ha]
    simp only [idealAngularLag, idealAngularSource, L, D, d, shapeGradient,
      StressAlgebra.axialExponent, StressAlgebra.coordinateFactor]
  · intro t ht
    have ht' : t ≤ v.core.pulseStart := ht.2.trans (max_le v.core.pulseStart_pos.le hy)
    have htend : t < v.core.endpoint := by
      dsimp [Parameters.endpoint]
      linarith [v.core.pulseLength_pos]
    have hd := OutgoingHistories.Qs_hasDerivAt w ha (t, η)
    rw [canonical_Sq_before w ha ht', canonical_H_radial_ratio w htend] at hd
    exact hd


-- @@ L2190-2195 verbatim
theorem canonical_Qs_ideal {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ 0) (η : ℝ) :
    OutgoingHistories.Qs w Amp (y, η) = idealAngularLag v.h η := by
  rw [canonical_Qs_before_all w ha (hy.trans v.core.pulseStart_pos.le), angularLag_ideal v.core v.h
      η hy]


-- @@ L2197-2202 verbatim
theorem canonical_Qs_ideal_lower {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (hh1 : v.h ≤ 1 / 100) {y η : ℝ} (hy : y ≤ 0) (hη : |η| ≤ 1) :
    1 ≤ OutgoingHistories.Qs w Amp (y, η) := by
  rw [canonical_Qs_ideal w ha hy]
  exact idealAngularLag_lower v.h_pos.le hh1 hη


-- @@ L2204-2213 verbatim
theorem canonical_Ns_ideal {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ 0) (η : ℝ) :
    OutgoingHistories.Ns w Amp (y, η) = -20 * η + (32 + 32 * v.h) * η ^ 3 +
      (4 * A v.h * η * SchedulePressure.axisPressure v η -
        d η * deriv (SchedulePressure.axisPressure v) η +
          (5 / 6) * (5 * d η * shapeGradient η + (10 * A v.h + 1) * η) *
            angular v.core.P v.core.dropLength v.core.lam (y, η) ^ 2) := by
  rw [canonical_Ns_before w ha (hy.trans v.core.pulseStart_pos.le)]
  exact congrArg₂ (· + ·) (geometricAxialLag_ideal v.core v.h η hy) (pressureAxialLag_ideal v η hy)


-- @@ L2215-2234 verbatim
theorem actual_ideal_cone_margins {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) {y : ℝ} (hy : y ≤ 0) (η : ℝ) :
    coneA w (y, η) = 4 / 5 ∧ coneB w Amp (y, η) = 0 ∧
      0 < coneA w (y, η) - coneB w Amp (y, η) * coneRatio w Amp (y, η) ∧
      2 * coneB w Amp (y, η) * coneRatio w Amp (y, η) +
        coneB w Amp (y, η) ^ 2 / coneA w (y, η) +
          (coneA w (y, η) - 2) * coneRatio w Amp (y, η) ^ 2 ≤ 0 := by
  have hpulse : y < v.core.pulseStart := hy.trans_lt v.core.pulseStart_pos
  have hend : y < v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hA : coneA w (y, η) = 4 / 5 := by
    rw [coneA_before w hend]
    norm_num [radialA, slope_ideal v.core.dropLength_pos.le hy]
  have hB : coneB w Amp (y, η) = 0 := by
    rw [coneB_before w ha hpulse, shear_early v.core (by linarith)]
  rw [hA, hB]
  norm_num
  linarith [sq_nonneg (coneRatio w Amp (y, η))]


-- @@ L2236-2249 verbatim
/-- The radial normal coefficient agrees with the logarithmic derivative of
the true angular field `E`, rather than a declared slope proxy. -/
theorem coneA_eq_E_derivative {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) (p : ℝ × ℝ) :
    coneA w p = 1 - 2 * OutgoingHistories.dY (OutgoingHistories.E w) p / OutgoingHistories.E w p :=
        by
  rcases p with ⟨y, η⟩
  have hd := (((hasDerivAt_id y).div_const 2).exp).mul
    (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.E_smooth w) (y, η))
  have hh := (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.H_smooth w) (y, η)).unique hd
  unfold coneA
  rw [hh]
  simp only [OutgoingHistories.H, id_eq]
  field_simp [(Real.exp_pos (y / 2)).ne', (OutgoingHistories.E_pos w (y, η)).ne']; ring


-- @@ L2251-2277 verbatim
/-- Ordered parameter selection for actual histories, followed by the final
physical radial-scale choice. All thresholds before `XR` are explicit. -/
theorem exists_ordered_actual_preliminary_cone :
    ∃ M : ℝ, 0 < M ∧ ∀ v : TailData, M ≤ v.core.m →
      amplitudeThreshold v.core.m ≤ v.core.P →
      v.core.lam ≤ lambdaThreshold v.core.P v.core.m →
      v.h ≤ heightThreshold v.core.m v.core.lam →
      ∀ {K : ℝ} (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ},
        ContDiff ℝ ∞ Amp →
        (∀ y η : ℝ, 0 ≤ y → y ≤ v.core.holdStart → |η| ≤ 1 →
          coneFloor * (η ^ 2 + Real.exp (-y)) ≤ OutgoingHistories.Qs w Amp (y, η)) ∧
        ∃ gap XR₀ : ℝ, 0 < gap ∧ 0 < XR₀ ∧ ∀ XR : ℝ, XR₀ < XR →
          ∀ p ∈ preliminaryWindow v,
            2 + gap < OutgoingHistories.p1 XR w Amp p *
              (1 - coneB w Amp p * coneRatio w Amp p / coneA w p) ∧
            coneA w p * (1 + (coneB w Amp p / coneA w p) ^ 2) + gap <
              ConeAlgebra.coneBound
                (OutgoingHistories.p1 XR w Amp p * (1 - coneB w Amp p * coneRatio w Amp p / coneA w
                    p))
                (OutgoingHistories.p1 XR w Amp p * (coneRatio w Amp p + coneB w Amp p / coneA w p))
                    := by
  obtain ⟨M, hM, hsmall⟩ := exists_small_dropSpeed dropThreshold_pos
  refine ⟨M, hM, ?_⟩
  intro v hm hP hlam hh K w Amp ha
  have hb := chosen_parameters_bounds v hP hlam hh
  refine ⟨fun y η hy hyT hη => canonical_Qs_lower w ha hb.2.2.1 hy hyT hη hb.2.2.2, ?_⟩
  exact exists_actual_preliminary_cone_scale w ha hb.2.2.1 hb.1 hb.2.2.2 (hsmall _ hm) hb.2.1


-- @@ L2279-2279 verbatim
end NavierStokes.OutgoingEntranceCone
