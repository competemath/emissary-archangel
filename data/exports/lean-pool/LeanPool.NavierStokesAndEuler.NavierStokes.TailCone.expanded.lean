/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ReleaseMoments
public import LeanPool.NavierStokesAndEuler.NavierStokes.CoordinateAlgebra
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.FuturePressureBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral


-- @@ L16-22 verbatim
/-!
# The actual outgoing tail and its cone estimates

The controller below is identified with an actual corrected angular history
by `ReleaseMoments`. Bounds never assume an amplitude small relative to `h`:
the prescribed long release plateau supplies that suppression.
-/


-- @@ L24-24 verbatim
section


-- @@ L26-33 verbatim
/-!
# Pressure through the actual angular reset

The corrected pressure is the improper integral of the actual corrected field.
The difference from the clean pressure is an explicit finite partial-reset
integral.  Bounds use the first angular coefficient jet supplied by the proved
reset witness; no parity or second-jet estimate is assumed.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
open Set Filter MeasureTheory

-- @@ L40-40 verbatim
open scoped Topology ContDiff

-- @@ L41-41 verbatim
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

-- @@ L42-42 verbatim
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

-- @@ L43-43 verbatim
open NavierStokes.FuturePressureBounds


-- @@ L45-45 verbatim
namespace NavierStokes.CorrectedPressureBounds


-- @@ L47-51 verbatim
/-- Corrected pi, given by `-(1 / 2 : ℝ) * ∫ t in Ioi y, correctedAngular d w.coefficients (t,
eta) ^ 2`. -/
noncomputable def correctedPi {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2


-- @@ L53-56 verbatim
/-- Edit density, given by `correctedAngular d w.coefficients p ^ 2 - finalAngular d p ^ 2`. -/
noncomputable def editDensity {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) : ℝ :=
  correctedAngular d w.coefficients p ^ 2 - finalAngular d p ^ 2


-- @@ L58-60 verbatim
/-- Release square, given by `finalAngular d (d.releaseStart, 0) ^ 2`. -/
noncomputable def releaseSquare (d : TailData) : ℝ :=
  finalAngular d (d.releaseStart, 0) ^ 2


-- @@ L62-63 verbatim
/-- Edit size, given by `K * d.core.lam ^ (28 : ℕ)`. -/
noncomputable def editSize (d : TailData) (K : ℝ) : ℝ := K * d.core.lam ^ (28 : ℕ)


-- @@ L65-66 verbatim
theorem releaseSquare_pos (d : TailData) : 0 < releaseSquare d :=
  sq_pos_of_pos (finalAngular_pos d _)


-- @@ L68-70 verbatim
theorem editSize_nonneg {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    0 ≤ editSize d K :=
  (norm_nonneg (w.coefficients 0)).trans (w.coefficient_bound 0)


-- @@ L72-75 verbatim
theorem witness_K_nonneg {d : TailData} {K : ℝ} (w : ResetWitness d K) : 0 ≤ K := by
  have he := editSize_nonneg w
  dsimp [editSize] at he
  exact nonneg_of_mul_nonneg_left he (pow_pos d.core.lam_pos 28)


-- @@ L77-89 verbatim
theorem relative_abs_le_two_norm (c : Coeff) (t : ℝ) : |relative c t| ≤ 2 * ‖c‖ := by
  have h0 : |c 0| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 0
  have h1 : |c 1| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 1
  have hb (j : Fin 2) : |bump j t| ≤ 1 := by
    rw [abs_of_nonneg (bump_nonneg j t)]
    exact bump_le_one j t
  calc
    _ ≤ |c 0| * |bump 0 t| + |c 1| * |bump 1 t| := by
      simpa only [relative, abs_mul] using abs_add_le (c 0 * bump 0 t) (c 1 * bump 1 t)
    _ ≤ ‖c‖ * 1 + ‖c‖ * 1 := add_le_add
      (mul_le_mul h0 (hb 0) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul h1 (hb 1) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring


-- @@ L91-95 verbatim
theorem relative_coefficient_bound {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    |relative (w.coefficients eta) t| ≤ 2 * editSize d K :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.coefficient_bound eta) (by norm_num))


-- @@ L97-104 verbatim
theorem relative_eta_hasDerivAt {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    HasDerivAt (fun q => relative (w.coefficients q) t)
      (relative (deriv w.coefficients eta) t) eta := by
  have hc := (w.smooth.differentiable (by simp) eta).hasDerivAt
  simpa only [relative] using
    ((hasDerivAt_pi.mp hc 0).mul_const (bump 0 t)).fun_add
      ((hasDerivAt_pi.mp hc 1).mul_const (bump 1 t))


-- @@ L106-110 verbatim
theorem relative_eta_bound {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta t : ℝ) :
    |relative (deriv w.coefficients eta) t| ≤ 2 * editSize d K :=
  (relative_abs_le_two_norm _ _).trans
    (mul_le_mul_of_nonneg_left (w.eta_derivative_bound eta) (by norm_num))


-- @@ L112-126 verbatim
theorem corrected_square_comparison {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) :
    (1 / 4) * finalAngular d p ^ 2 ≤ correctedAngular d w.coefficients p ^ 2 ∧
      correctedAngular d w.coefficients p ^ 2 ≤ (9 / 4) * finalAngular d p ^ 2 := by
  have hr := abs_le.mp (w.small_jets p.2 (p.1 - correctionCenter d)).1
  have hsq : (1 / 4 : ℝ) ≤ (1 + relative (w.coefficients p.2)
      (p.1 - correctionCenter d)) ^ 2 ∧
      (1 + relative (w.coefficients p.2) (p.1 - correctionCenter d)) ^ 2 ≤ 9 / 4 := by
    constructor <;> nlinarith
  simp only [correctedAngular, mul_pow]
  constructor
  · simpa only [mul_comm (1 / 4 : ℝ)] using
      mul_le_mul_of_nonneg_left hsq.1 (sq_nonneg (finalAngular d p))
  · simpa only [mul_comm (9 / 4 : ℝ)] using
      mul_le_mul_of_nonneg_left hsq.2 (sq_nonneg (finalAngular d p))


-- @@ L128-133 verbatim
theorem baseE_square_ratio (lam amp t r : ℝ) :
    baseE lam amp t ^ 2 = baseE lam amp r ^ 2 * Real.exp ((1 + 2 * lam) * (r - t)) := by
  simp only [baseE, mul_pow, ← Real.exp_nat_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring


-- @@ L135-156 verbatim
theorem window_square_bounds (d : TailData) {t : ℝ}
    (ht : t ∈ Icc (d.releaseStart - 4) d.releaseStart) (eta : ℝ) :
    releaseSquare d ≤ finalAngular d (t, eta) ^ 2 ∧
      finalAngular d (t, eta) ^ 2 ≤ Real.exp 5 * releaseSquare d := by
  have hdt : 0 ≤ d.releaseStart - t := sub_nonneg.mpr ht.2
  have hdt4 : d.releaseStart - t ≤ 4 := by linarith [ht.1]
  have h0 : 0 ≤ (1 + 2 * d.core.lam) * (d.releaseStart - t) :=
    mul_nonneg (by linarith [d.core.lam_pos]) hdt
  have h5 : (1 + 2 * d.core.lam) * (d.releaseStart - t) ≤ 5 := by
    have hm := mul_le_mul (show 1 + 2 * d.core.lam ≤ (6 / 5 : ℝ) by linarith [d.core.lam_lt])
      hdt4 hdt (by norm_num)
    linarith
  have htR : d.releaseStart ∈ Icc (d.releaseStart - 4) d.releaseStart := by
    constructor <;> linarith
  rw [original_matches_reference d eta ht, baseE_square_ratio _ _ t d.releaseStart]
  have hR : releaseSquare d = baseE d.core.lam (referenceAmplitude d) d.releaseStart ^ 2 := by
    rw [releaseSquare, original_matches_reference d 0 htR]
  rw [← hR]
  constructor
  · exact le_mul_of_one_le_right (releaseSquare_pos d).le (Real.one_le_exp_iff.mpr h0)
  · simpa only [mul_comm (Real.exp 5)] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h5) (releaseSquare_pos d).le


-- @@ L158-161 verbatim
theorem editDensity_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (editDensity w) :=
  ((correctedAngular_contDiff d w.coefficients w.smooth).pow 2).sub
    ((finalAngular_contDiff d).pow 2)


-- @@ L163-168 verbatim
theorem editDensity_eq {d : TailData} {K : ℝ} (w : ResetWitness d K) (t eta : ℝ) :
    editDensity w (t, eta) = baseE d.core.lam (referenceAmplitude d) t ^ 2 *
      ((1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1) := by
  rw [editDensity, corrected_pressure_reference]
  unfold modifiedE
  ring


-- @@ L170-173 verbatim
theorem editDensity_zero_outside {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (d.releaseStart - 4) d.releaseStart) : editDensity w (t, eta) = 0 := by
  rw [editDensity, correctedAngular_unchanged d w.coefficients eta ht, sub_self]


-- @@ L175-180 verbatim
/-- Edit density eta, constructed using `2`. -/
noncomputable def editDensityEta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) : ℝ :=
  2 * baseE d.core.lam (referenceAmplitude d) p.1 ^ 2 *
    (1 + relative (w.coefficients p.2) (p.1 - correctionCenter d)) *
    relative (deriv w.coefficients p.2) (p.1 - correctionCenter d)


-- @@ L182-194 verbatim
theorem editDensity_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    HasDerivAt (fun q => editDensity w (t, q)) (editDensityEta w (t, eta)) eta := by
  have heq : (fun q => editDensity w (t, q)) = fun q =>
      baseE d.core.lam (referenceAmplitude d) t ^ 2 *
        ((1 + relative (w.coefficients q) (t - correctionCenter d)) ^ 2 - 1) :=
    funext (editDensity_eq w t)
  rw [heq]
  convert! ((((relative_eta_hasDerivAt w eta (t - correctionCenter d)).const_add 1).pow
      2).sub_const 1).const_mul
    (baseE d.core.lam (referenceAmplitude d) t ^ 2) using 1
  dsimp [editDensityEta]
  ring


-- @@ L196-199 verbatim
theorem editDensityEta_zero_outside {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (d.releaseStart - 4) d.releaseStart) : editDensityEta w (t, eta) = 0 := by
  simp only [editDensityEta, relative_zero_outside d _ ht, mul_zero]


-- @@ L201-209 verbatim
theorem editDensityEta_continuous_t {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (eta : ℝ) : Continuous (fun t => editDensityEta w (t, eta)) := by
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const.mul (((baseE_contDiff _ _).continuous).pow 2)
    · exact continuous_const.add ((relative_contDiff (w.coefficients eta)).continuous.comp
        (continuous_id.sub continuous_const))
  · exact (relative_contDiff (deriv w.coefficients eta)).continuous.comp
      (continuous_id.sub continuous_const)


-- @@ L211-239 verbatim
theorem editDensity_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    |editDensity w (t, eta)| ≤ 5 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hR := releaseSquare_pos d
  by_cases ht : t ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · have hs := (w.small_jets eta (t - correctionCenter d)).1
    have hr := relative_coefficient_bound w eta (t - correctionCenter d)
    have hsize := editSize_nonneg w
    have hprod : |(1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1| ≤
        5 * editSize d K := by
      rw [show (1 + relative (w.coefficients eta) (t - correctionCenter d)) ^ 2 - 1 =
        relative (w.coefficients eta) (t - correctionCenter d) *
          (2 + relative (w.coefficients eta) (t - correctionCenter d)) by ring, abs_mul]
      have ha : |2 + relative (w.coefficients eta) (t - correctionCenter d)| ≤ 5 / 2 := by
        have h := abs_add_le (2 : ℝ) (relative (w.coefficients eta) (t - correctionCenter d))
        norm_num at h
        linarith
      have hh := mul_le_mul hr ha (abs_nonneg _) (by positivity : 0 ≤ 2 * editSize d K)
      linarith
    rw [editDensity_eq, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hbase : baseE d.core.lam (referenceAmplitude d) t ^ 2 ≤ Real.exp 5 * releaseSquare d := by
      rw [← original_matches_reference d eta ⟨ht.1.le, ht.2.le⟩]
      exact (window_square_bounds d ⟨ht.1.le, ht.2.le⟩ eta).2
    have hb := mul_le_mul hbase hprod (abs_nonneg _) (by
        positivity : 0 ≤ Real.exp 5 * releaseSquare d)
    linarith
  · rw [editDensity_zero_outside w eta ht, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (editSize_nonneg w))
      (Real.exp_pos _).le) (releaseSquare_pos d).le


-- @@ L241-267 verbatim
theorem editDensityEta_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (t eta : ℝ) :
    |editDensityEta w (t, eta)| ≤ 6 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hR := releaseSquare_pos d
  by_cases ht : t ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · have hs := (w.small_jets eta (t - correctionCenter d)).1
    have hr := relative_eta_bound w eta (t - correctionCenter d)
    have hsize := editSize_nonneg w
    have ha : |1 + relative (w.coefficients eta) (t - correctionCenter d)| ≤ 3 / 2 := by
      have h := abs_add_le (1 : ℝ) (relative (w.coefficients eta) (t - correctionCenter d))
      norm_num at h
      linarith
    have hbase : baseE d.core.lam (referenceAmplitude d) t ^ 2 ≤ Real.exp 5 * releaseSquare d := by
      rw [← original_matches_reference d eta ⟨ht.1.le, ht.2.le⟩]
      exact (window_square_bounds d ⟨ht.1.le, ht.2.le⟩ eta).2
    rw [editDensityEta, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (baseE d.core.lam (referenceAmplitude d) t))]
    norm_num
    have h1 := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ 2 by norm_num)
    have h2 := mul_le_mul h1 ha (abs_nonneg _) (by
        positivity : 0 ≤ 2 * (Real.exp 5 * releaseSquare d))
    have h3 := mul_le_mul h2 hr (abs_nonneg _)
      (by positivity : 0 ≤ 2 * (Real.exp 5 * releaseSquare d) * (3 / 2))
    linarith
  · rw [editDensityEta_zero_outside w eta ht, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (editSize_nonneg w))
      (Real.exp_pos _).le) (releaseSquare_pos d).le


-- @@ L269-275 verbatim
theorem integral_Ioi_increment {f : ℝ → ℝ} (hf : Integrable f) (a y : ℝ) :
    (∫ t in Ioi y, f t) = (∫ t in Ioi a, f t) - ∫ t in a..y, f t := by
  have ha := intervalIntegral.integral_Iic_add_Ioi (b := a) hf.integrableOn hf.integrableOn
  have hy := intervalIntegral.integral_Iic_add_Ioi (b := y) hf.integrableOn hf.integrableOn
  have hd := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := y)
    hf.integrableOn hf.integrableOn
  linarith


-- @@ L277-283 verbatim
theorem correctedPi_increment {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (a y eta : ℝ) :
    correctedPi w y eta = correctedPi w a eta +
      (1 / 2) * ∫ t in a..y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  rw [correctedPi, integral_Ioi_increment (corrected_square_integrable w eta) a y,
    correctedPi]
  ring


-- @@ L285-287 verbatim
theorem correctedPi_eq_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    correctedPi w y eta = Pi d y eta := corrected_future_pressure_eq w hy eta


-- @@ L289-298 verbatim
theorem correctedPi_eq_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    correctedPi w y eta = Pi d y eta := by
  unfold correctedPi Pi
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [correctedAngular_unchanged d w.coefficients eta]
  intro hmem
  exact (not_lt_of_ge (hy.trans ht.le)) hmem.2


-- @@ L300-314 verbatim
theorem correctedPi_eq_partial {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    correctedPi w y eta = Pi d y eta +
      (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, eta) := by
  have hn : IntervalIntegrable (fun t => correctedAngular d w.coefficients (t, eta) ^ 2)
      volume (d.releaseStart - 4) y :=
    (corrected_square_integrable w eta).intervalIntegrable
  have ho : IntervalIntegrable (fun t => finalAngular d (t, eta) ^ 2)
      volume (d.releaseStart - 4) y :=
    (SchedulePressure.angular_square_integrable d eta).intervalIntegrable
  rw [correctedPi_increment w (d.releaseStart - 4) y eta,
    correctedPi_eq_before w le_rfl eta, Pi_increment d (d.releaseStart - 4) y eta]
  simp only [editDensity]
  rw [intervalIntegral.integral_sub hn ho]
  ring


-- @@ L316-318 verbatim
/-- Pressure change, given by `correctedPi w y eta - Pi d y eta`. -/
noncomputable def pressureChange {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : ℝ := correctedPi w y eta - Pi d y eta


-- @@ L320-324 verbatim
theorem pressureChange_eq_partial {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    pressureChange w y eta = (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, eta) := by
  rw [pressureChange, correctedPi_eq_partial]
  ring


-- @@ L326-328 verbatim
theorem pressureChange_zero_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    pressureChange w y eta = 0 := by rw [pressureChange, correctedPi_eq_before w hy, sub_self]


-- @@ L330-332 verbatim
theorem pressureChange_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    pressureChange w y eta = 0 := by rw [pressureChange, correctedPi_eq_after w hy, sub_self]


-- @@ L334-349 verbatim
/-- Joint smoothness of a finite integral with a variable upper limit. -/
theorem intervalPrimitive_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ∫ t in a..p.1, f (t, p.2)) := by
  let g : (ℝ × ℝ) × ℝ → ℝ := fun z => f (a + (z.1.1 - a) * z.2, z.1.2)
  have hg : ContDiff ℝ ∞ g := hf.comp
    ((contDiff_const.add ((contDiff_fst.fst.sub contDiff_const).mul contDiff_snd)).prodMk
      contDiff_fst.snd)
  have heq : (fun p : ℝ × ℝ => ∫ t in a..p.1, f (t, p.2)) =
      fun p : ℝ × ℝ => (p.1 - a) * ∫ u in (0 : ℝ)..1, g (p, u) := by
    funext p
    have h := intervalIntegral.smul_integral_comp_mul_add
      (f := fun t => f (t, p.2)) (a := (0 : ℝ)) (b := 1) (p.1 - a) a
    simpa [g, smul_eq_mul, add_comm] using h.symm
  rw [heq]
  exact (contDiff_fst.sub contDiff_const).mul
    (TransportPrimitive.parameterIntegral_contDiff hg 0 1)


-- @@ L351-359 verbatim
theorem cleanPi_joint_contDiff (d : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Pi d p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => Pi d p.1 p.2) = fun p : ℝ × ℝ =>
      Pi d 0 p.2 + (1 / 2) * ∫ t in (0 : ℝ)..p.1, finalAngular d (t, p.2) ^ 2 := by
    funext p
    exact Pi_increment d 0 p.1 p.2
  rw [heq]
  exact ((Pi_contDiff_eta d 0).comp contDiff_snd).add
    (contDiff_const.mul (intervalPrimitive_contDiff ((finalAngular_contDiff d).pow 2) 0))


-- @@ L361-368 verbatim
theorem pressureChange_joint_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureChange w p.1 p.2) := by
  have heq : (fun p : ℝ × ℝ => pressureChange w p.1 p.2) = fun p : ℝ × ℝ =>
      (1 / 2) * ∫ t in (d.releaseStart - 4)..p.1, editDensity w (t, p.2) := by
    funext p
    exact pressureChange_eq_partial w p.1 p.2
  rw [heq]
  exact contDiff_const.mul (intervalPrimitive_contDiff (editDensity_contDiff w) _)


-- @@ L370-374 verbatim
theorem correctedPi_joint_contDiff {d : TailData} {K : ℝ} (w : ResetWitness d K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => correctedPi w p.1 p.2) := by
  convert! (cleanPi_joint_contDiff d).add (pressureChange_joint_contDiff w) using 1
  funext p
  simp [pressureChange]


-- @@ L376-388 verbatim
theorem correctedPi_hasDerivAt_y {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (fun t => correctedPi w t eta)
      ((1 / 2) * correctedAngular d w.coefficients (y, eta) ^ 2) y := by
  have hc : Continuous (fun t => correctedAngular d w.coefficients (t, eta) ^ 2) :=
    (((correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2)
  have heq : (fun t => correctedPi w t eta) = fun t => correctedPi w 0 eta +
      (1 / 2) * primitive (fun v => correctedAngular d w.coefficients (v, eta) ^ 2) t := by
    funext t
    exact correctedPi_increment w 0 t eta
  rw [heq]
  exact ((primitive_hasDerivAt hc y).const_mul (1 / 2)).const_add _


-- @@ L390-412 verbatim
theorem pressureChange_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (pressureChange w y)
      ((1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensityEta w (t, eta)) eta := by
  have hc (q : ℝ) : Continuous (fun t => editDensity w (t, q)) :=
    (editDensity_contDiff w).continuous.comp (continuous_id.prodMk continuous_const)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q t => editDensity w (t, q)) (F' := fun q t => editDensityEta w (t, q))
    (x₀ := eta) (μ := volume) (a := d.releaseStart - 4) (b := y)
    (bound := fun _ => 6 * editSize d K * Real.exp 5 * releaseSquare d)
    (Metric.ball_mem_nhds eta (show (0 : ℝ) < 1 by norm_num))
    (Eventually.of_forall fun q => (hc q).aestronglyMeasurable)
    ((hc eta).intervalIntegrable _ _)
    ((editDensityEta_continuous_t w eta).aestronglyMeasurable)
    (Eventually.of_forall fun t _ q _ => by
      simpa only [Real.norm_eq_abs] using editDensityEta_abs_le w t q)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ q _ => editDensity_hasDerivAt_eta w t q)
  have heq : pressureChange w y = fun q =>
      (1 / 2) * ∫ t in (d.releaseStart - 4)..y, editDensity w (t, q) :=
    funext (pressureChange_eq_partial w y)
  rw [heq]
  exact h.2.const_mul (1 / 2)


-- @@ L414-424 verbatim
theorem correctedPi_hasDerivAt_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (correctedPi w y)
      (deriv (Pi d y) eta + (1 / 2) *
        ∫ t in (d.releaseStart - 4)..y, editDensityEta w (t, eta)) eta := by
  have heq : correctedPi w y = fun q => Pi d y q + pressureChange w y q := by
    funext q
    simp [pressureChange]
  rw [heq]
  exact ((Pi_contDiff_eta d y).differentiable (by simp) eta).hasDerivAt.add
    (pressureChange_hasDerivAt_eta w y eta)


-- @@ L426-430 verbatim
theorem correctedPi_deriv_eta {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    deriv (correctedPi w y) eta = deriv (Pi d y) eta + deriv (pressureChange w y) eta := by
  rw [(correctedPi_hasDerivAt_eta w y eta).deriv,
    (pressureChange_hasDerivAt_eta w y eta).deriv]


-- @@ L432-437 verbatim
theorem pressureChange_deriv_zero_before {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : y ≤ d.releaseStart - 4) (eta : ℝ) :
    deriv (pressureChange w y) eta = 0 := by
  have heq : pressureChange w y = fun _ => 0 := funext (pressureChange_zero_before w hy)
  rw [heq]
  simp


-- @@ L439-444 verbatim
theorem pressureChange_deriv_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    deriv (pressureChange w y) eta = 0 := by
  have heq : pressureChange w y = fun _ => 0 := funext (pressureChange_zero_after w hy)
  rw [heq]
  simp


-- @@ L446-452 verbatim
theorem cleanPi_eta_independent_after_flatten (d : TailData) {y : ℝ}
    (hy : d.flattenEnd ≤ y) (eta eta' : ℝ) : Pi d y eta = Pi d y eta' := by
  unfold Pi
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [finalAngular_eta_independent d eta eta' (hy.trans ht.le)]


-- @@ L454-458 verbatim
theorem correctedPi_eta_independent_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta eta' : ℝ) :
    correctedPi w y eta = correctedPi w y eta' := by
  rw [correctedPi_eq_after w hy, correctedPi_eq_after w hy]
  exact cleanPi_eta_independent_after_flatten d ((releaseStart_gt_flattenEnd d).le.trans hy) _ _


-- @@ L460-466 verbatim
theorem correctedPi_deriv_eta_zero_after {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y : ℝ} (hy : d.releaseStart ≤ y) (eta : ℝ) :
    deriv (correctedPi w y) eta = 0 := by
  have heq : correctedPi w y = fun _ => correctedPi w y 0 :=
    funext (fun q => correctedPi_eta_independent_after w hy q 0)
  rw [heq]
  simp


-- @@ L468-480 verbatim
theorem half_partial_integral_abs_le {f : ℝ → ℝ} {B r y : ℝ}
    (hB : 0 ≤ B) (hy : y ∈ Icc (r - 4) r) (hbound : ∀ t, |f t| ≤ B) :
    |(1 / 2 : ℝ) * ∫ t in (r - 4)..y, f t| ≤ 2 * B := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r - 4) (b := y) (f := f)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
  have hlen : |y - (r - 4)| ≤ 4 := by
    rw [abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.2]
  rw [Real.norm_eq_abs] at hi
  rw [abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith [mul_le_mul_of_nonneg_left hlen hB]


-- @@ L482-499 verbatim
theorem pressureChange_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |pressureChange w y eta| ≤ 10 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hsize := editSize_nonneg w
  have hR := releaseSquare_pos d
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_zero_after w hr, abs_zero]
    positivity
  rw [pressureChange_eq_partial]
  have h := half_partial_integral_abs_le
    (B := 5 * editSize d K * Real.exp 5 * releaseSquare d)
    (by positivity) ⟨(le_of_not_ge hl), (le_of_not_ge hr)⟩
    (fun t => editDensity_abs_le w t eta)
  convert! h using 1
  ring


-- @@ L501-519 verbatim
theorem pressureChange_deriv_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |deriv (pressureChange w y) eta| ≤
      12 * editSize d K * Real.exp 5 * releaseSquare d := by
  have hsize := editSize_nonneg w
  have hR := releaseSquare_pos d
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_deriv_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_deriv_zero_after w hr, abs_zero]
    positivity
  rw [(pressureChange_hasDerivAt_eta w y eta).deriv]
  have h := half_partial_integral_abs_le
    (B := 6 * editSize d K * Real.exp 5 * releaseSquare d)
    (by positivity) ⟨(le_of_not_ge hl), (le_of_not_ge hr)⟩
    (fun t => editDensityEta_abs_le w t eta)
  convert! h using 1
  ring


-- @@ L521-524 verbatim
theorem clean_square_le_corrected {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (p : ℝ × ℝ) :
    finalAngular d p ^ 2 ≤ 4 * correctedAngular d w.coefficients p ^ 2 := by
  linarith [(corrected_square_comparison w p).1]


-- @@ L526-545 verbatim
/-- The edit derivative is controlled by the actual local corrected field. -/
theorem pressureChange_deriv_abs_le_corrected {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |deriv (pressureChange w y) eta| ≤
      (48 * Real.exp 5 * editSize d K) * correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  by_cases hl : y ≤ d.releaseStart - 4
  · rw [pressureChange_deriv_zero_before w hl, abs_zero]
    positivity
  by_cases hr : d.releaseStart ≤ y
  · rw [pressureChange_deriv_zero_after w hr, abs_zero]
    positivity
  have hR : releaseSquare d ≤ 4 * correctedAngular d w.coefficients (y, eta) ^ 2 :=
    ((window_square_bounds d ⟨le_of_not_ge hl, le_of_not_ge hr⟩ eta).1).trans
      (clean_square_le_corrected w _)
  apply (pressureChange_deriv_abs_le w y eta).trans
  have h := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ 12 * editSize d K * Real.exp 5 by positivity)
  convert! h using 1
  ring


-- @@ L547-550 verbatim
theorem correctedPi_nonpos {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) : correctedPi w y eta ≤ 0 := by
  unfold correctedPi
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)


-- @@ L552-558 verbatim
theorem correctedPi_abs_eq {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    |correctedPi w y eta| = (1 / 2) *
      ∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  rw [abs_of_nonpos (correctedPi_nonpos w y eta)]
  unfold correctedPi
  ring


-- @@ L560-578 verbatim
theorem correctedPi_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ ((9 / 2) * envelopeConstant) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hi : (∫ t in Ioi y, correctedAngular d w.coefficients (t, eta) ^ 2) ≤
      (9 / 4) * ∫ t in Ioi y, finalAngular d (t, eta) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (corrected_square_integrable w eta).integrableOn
      ((SchedulePressure.angular_square_integrable d eta).const_mul (9 / 4)).integrableOn
      measurableSet_Ioi (fun t _ => (corrected_square_comparison w (t, eta)).2)
  have hI := hi.trans (mul_le_mul_of_nonneg_left (future_square_integral_le d hy heta)
    (show (0 : ℝ) ≤ 9 / 4 by norm_num))
  have he := mul_le_mul_of_nonneg_left (clean_square_le_corrected w (y, eta))
    envelopeConstant_pos.le
  have hI' := hI.trans (mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 9 / 4 by norm_num))
  rw [correctedPi_abs_eq]
  have h := mul_le_mul_of_nonneg_left hI' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert! h using 1
  ring


-- @@ L580-599 verbatim
theorem correctedPi_deriv_abs_le {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |deriv (correctedPi w y) eta| ≤
      (8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K) *
        correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hc : |deriv (Pi d y) eta| ≤ (8 * envelopeConstant * |eta|) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
    apply (Pi_deriv_abs_le d hy heta).trans
    have h := mul_le_mul_of_nonneg_left (clean_square_le_corrected w (y, eta))
      (show 0 ≤ (2 * envelopeConstant) * |eta| by
        exact mul_nonneg (mul_nonneg (by norm_num) envelopeConstant_pos.le) (abs_nonneg eta))
    convert! h using 1
    ring
  rw [correctedPi_deriv_eta]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ (8 * envelopeConstant * |eta|) * correctedAngular d w.coefficients (y, eta) ^ 2 +
        (48 * Real.exp 5 * editSize d K) * correctedAngular d w.coefficients (y, eta) ^ 2 :=
      add_le_add hc (pressureChange_deriv_abs_le_corrected w y eta)
    _ = _ := by ring


-- @@ L601-602 verbatim
/-- Corrected constant, given by `13 * envelopeConstant + 48 * Real.exp 5`. -/
noncomputable def correctedConstant : ℝ := 13 * envelopeConstant + 48 * Real.exp 5


-- @@ L604-607 verbatim
theorem correctedConstant_pos : 0 < correctedConstant := by
  have h := envelopeConstant_pos
  unfold correctedConstant
  positivity


-- @@ L609-629 verbatim
theorem corrected_bounds {d : TailData} {K : ℝ}
    (w : ResetWitness d K) {y eta : ℝ} (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ correctedConstant * (1 + editSize d K) *
      correctedAngular d w.coefficients (y, eta) ^ 2 ∧
    |deriv (correctedPi w y) eta| ≤ correctedConstant * (1 + editSize d K) *
      correctedAngular d w.coefficients (y, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  have hM := envelopeConstant_pos
  have he := Real.exp_pos (5 : ℝ)
  have hfirst : (9 / 2 : ℝ) * envelopeConstant ≤ correctedConstant * (1 + editSize d K) := by
    unfold correctedConstant
    linarith [mul_nonneg hM.le hsize, mul_nonneg he.le hsize]
  have hderiv : 8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K ≤
      correctedConstant * (1 + editSize d K) := by
    have hη := mul_le_mul_of_nonneg_left heta (show 0 ≤ 8 * envelopeConstant by positivity)
    unfold correctedConstant
    linarith [mul_nonneg hM.le hsize]
  exact ⟨(correctedPi_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hfirst (sq_nonneg _)),
    (correctedPi_deriv_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hderiv (sq_nonneg _))⟩


-- @@ L631-651 verbatim
theorem corrected_bounds_of_small {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (hsmall : editSize d K ≤ 1) {y eta : ℝ}
    (hy : 0 ≤ y) (heta : |eta| ≤ 1) :
    |correctedPi w y eta| ≤ correctedConstant * correctedAngular d w.coefficients (y, eta) ^ 2 ∧
    |deriv (correctedPi w y) eta| ≤ correctedConstant * correctedAngular d w.coefficients (y, eta)
        ^ 2 := by
  have hM := envelopeConstant_pos
  have he := Real.exp_pos (5 : ℝ)
  have hfirst : (9 / 2 : ℝ) * envelopeConstant ≤ correctedConstant := by
    unfold correctedConstant
    linarith
  have hderiv : 8 * envelopeConstant * |eta| + 48 * Real.exp 5 * editSize d K ≤
      correctedConstant := by
    have hη := mul_le_mul_of_nonneg_left heta (show 0 ≤ 8 * envelopeConstant by positivity)
    have hs := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 48 * Real.exp 5 by positivity)
    unfold correctedConstant
    linarith
  exact ⟨(correctedPi_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hfirst (sq_nonneg _)),
    (correctedPi_deriv_abs_le w hy heta).trans
      (mul_le_mul_of_nonneg_right hderiv (sq_nonneg _))⟩


-- @@ L653-667 verbatim
/-- The smallness condition follows from an explicit threshold depending only on K. -/
theorem exists_editSize_small_threshold (K : ℝ) (hK : 0 ≤ K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 → editSize d K ≤ 1 := by
  refine ⟨1 / (K + 1), by positivity, ?_⟩
  intro d hd
  have hLamOne : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
  have hp : d.core.lam ^ 28 ≤ d.core.lam := by
    rw [show (28 : ℕ) = 27 + 1 by rfl, pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n := 27) d.core.lam_pos.le hLamOne) d.core.lam_pos.le
  have hprod : d.core.lam * (K + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < K + 1)).mp hd.le
  have h := mul_le_mul_of_nonneg_left hp hK
  unfold editSize
  linarith [d.core.lam_pos]


-- @@ L669-684 verbatim
theorem releaseSquare_le_core_endpoint (d : TailData) {eta : ℝ} (heta : |eta| ≤ 1) :
    releaseSquare d ≤ (4 * Real.exp (6 / 5)) * finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have hER : d.core.endpoint ≤ d.releaseStart :=
    ((flattenEnd_gt_core d).trans (releaseStart_gt_flattenEnd d)).le
  have hclock := clock_future_bound d (SchedulePressure.endpoint_pos d).le hER
  have hexp : Real.exp (-(4 / 5) * (d.releaseStart - d.core.endpoint)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hER)
  change SchedulePressure.clockWeight d d.releaseStart ≤ _
  calc
    _ ≤ SchedulePressure.clockWeight d d.core.endpoint * Real.exp (6 / 5) :=
      hclock.trans (mul_le_of_le_one_right
        (mul_nonneg (SchedulePressure.clockWeight_pos d _).le (Real.exp_pos _).le) hexp)
    _ ≤ (4 * finalAngular d (d.core.endpoint, eta) ^ 2) * Real.exp (6 / 5) :=
      mul_le_mul_of_nonneg_right (clock_le_four_angular_square d _ heta) (Real.exp_pos _).le
    _ = _ := by ring


-- @@ L686-705 verbatim
theorem pressureChange_core_endpoint_bounds {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y : ℝ) {eta : ℝ} (heta : |eta| ≤ 1) :
    |pressureChange w y eta| ≤
      (40 * Real.exp 5 * Real.exp (6 / 5) * editSize d K) *
        finalAngular d (d.core.endpoint, eta) ^ 2 ∧
    |deriv (pressureChange w y) eta| ≤
      (48 * Real.exp 5 * Real.exp (6 / 5) * editSize d K) *
        finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have hsize := editSize_nonneg w
  constructor
  · apply (pressureChange_abs_le w y eta).trans
    have h := mul_le_mul_of_nonneg_left (releaseSquare_le_core_endpoint d heta)
      (show 0 ≤ 10 * editSize d K * Real.exp 5 by positivity)
    convert! h using 1
    ring
  · apply (pressureChange_deriv_abs_le w y eta).trans
    have h := mul_le_mul_of_nonneg_left (releaseSquare_le_core_endpoint d heta)
      (show 0 ≤ 12 * editSize d K * Real.exp 5 by positivity)
    convert! h using 1
    ring


-- @@ L707-717 verbatim
/-- Canonical forward pressure with the unchanged whole-axis pressure datum. -/
theorem correctedPi_eq_axisPressure_add {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    correctedPi w y eta = SchedulePressure.axisPressure d eta + (1 / 2) *
      ∫ t in Iic y, correctedAngular d w.coefficients (t, eta) ^ 2 := by
  have hi := corrected_square_integrable w eta
  have hz := w.pressure_neutral eta
  rw [integral_sub hi (SchedulePressure.angular_square_integrable d eta)] at hz
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := y) hi.integrableOn hi.integrableOn
  unfold correctedPi SchedulePressure.axisPressure
  linarith


-- @@ L719-724 verbatim
theorem pressureChange_hasDerivAt_y {d : TailData} {K : ℝ}
    (w : ResetWitness d K) (y eta : ℝ) :
    HasDerivAt (fun t => pressureChange w t eta) ((1 / 2) * editDensity w (y, eta)) y := by
  convert! (correctedPi_hasDerivAt_y w y eta).sub (Pi_hasDerivAt_y d y eta) using 1
  dsimp [editDensity]
  ring


-- @@ L726-726 verbatim
end NavierStokes.CorrectedPressureBounds


-- @@ L728-728 verbatim
end

-- @@ L729-729 verbatim
end


-- @@ L731-731 verbatim
end


-- @@ L733-733 verbatim
@[expose] public section


-- @@ L735-735 verbatim
noncomputable section


-- @@ L737-737 verbatim
open Set Filter Function MeasureTheory

-- @@ L738-738 verbatim
open scoped Topology ContDiff

-- @@ L739-739 verbatim
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

-- @@ L740-740 verbatim
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

-- @@ L741-741 verbatim
open NavierStokes.TailEnergyBounds


-- @@ L743-743 verbatim
namespace NavierStokes.TailCone


-- @@ L745-748 verbatim
theorem initialLag_ge_half_lambda (d : TailData) : d.core.lam / 2 ≤ initialLag d := by
  have hd : 0 < 1 - d.core.lam := by linarith [d.core.lam_lt]
  apply (le_div_iff₀ hd).mpr
  linarith [d.h_small, sq_nonneg d.core.lam]


-- @@ L750-759 verbatim
theorem release_rate_integral_bound_all (d : TailData) {t : ℝ}
    (_ht : 0 ≤ t) (ht' : t ≤ d.rampEnd) : primitive (releaseRate d) t ≤ 2 := by
  have hc := (releaseRate_contDiff d).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t d.rampEnd)
  have hn : 0 ≤ ∫ s in t..d.rampEnd, releaseRate d s :=
    intervalIntegral.integral_nonneg ht' (fun s _ => (release_rate_bounds d s).1)
  have hb := release_rate_integral_bound d
  unfold primitive at hb ⊢
  linarith


-- @@ L761-775 verbatim
theorem releaseLag_lower_all (d : TailData) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ d.rampEnd) :
    Real.exp (-2) * (d.core.lam / 2) ≤ releaseLag d t := by
  have hsource : 0 ≤ primitive
      (fun s => Real.exp (primitive (releaseRate d) s) * releaseSource d s) t :=
    intervalIntegral.integral_nonneg ht
      (fun s _ => mul_nonneg (Real.exp_pos _).le (release_source_nonneg d s))
  have he : Real.exp (-2) ≤ Real.exp (-primitive (releaseRate d) t) :=
    Real.exp_le_exp.mpr (by linarith [release_rate_integral_bound_all d ht ht'])
  have hq := initialLag_ge_half_lambda d
  have hq0 : 0 ≤ initialLag d := d.h_pos.le.trans (initialLag_gt_h d).le
  unfold releaseLag linearLag
  have h1 := mul_le_mul_of_nonneg_right he hq0
  have h2 := mul_le_mul_of_nonneg_left hq (Real.exp_pos (-2)).le
  linarith [mul_nonneg (Real.exp_pos (-primitive (releaseRate d) t)).le hsource]


-- @@ L777-782 verbatim
theorem tailDebt_ge_coefficient (d : TailData) : tailCoefficient * d.h ≤ tailDebt d := by
  have hd : 0 < 1 - d.rho := by linarith [d.rho_lt_half]
  have h : d.rho ≤ d.rho / (1 - d.rho) := by
    apply (le_div_iff₀ hd).mpr
    linarith [sq_nonneg d.rho]
  exact h.trans (tailDebt_bounds d).1


-- @@ L784-792 verbatim
theorem holdLag_lower (d : TailData) {t : ℝ} (ht : t ≤ decayHold d) :
    tailCoefficient * d.h ≤ holdLag d t := by
  have hq : 0 ≤ releaseLag d d.rampEnd :=
    (tailDebt_pos d).le.trans (releaseLag_gt_tailDebt d).le
  have he : Real.exp (-(1 - d.h) * decayHold d) ≤ Real.exp (-(1 - d.h) * t) :=
    Real.exp_le_exp.mpr (by nlinarith [d.one_sub_h_pos])
  have h := mul_le_mul_of_nonneg_left he hq
  rw [decayHold_hits_target] at h
  exact (tailDebt_ge_coefficient d).trans h


-- @@ L794-809 verbatim
theorem tailLag_first_half (d : TailData) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    tailLag d t = tailDebt d * Real.exp (-(1 - d.h) * t) := by
  have hi : primitive (weightedTailDerivative d) t = 0 := by
    unfold primitive
    calc
      _ = ∫ _s in (0 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' := uIcc_of_le ht ▸ hs
        have harg : (s - 1) / 2 < 0 := by linarith [hs'.2]
        simp [weightedTailDerivative, tailShapeDeriv, sigma_derivative_zero_left harg]
      _ = 0 := by simp
  unfold tailLag tailNumerator
  rw [hi, sub_zero, tailShape_early d (show t ≤ 1 by linarith)]
  unfold tailDebt primitive weightedTailDerivative
  ring


-- @@ L811-817 verbatim
theorem tailLag_first_half_lower (d : TailData) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    Real.exp (-1) * tailCoefficient * d.h ≤ tailLag d t := by
  rw [tailLag_first_half d ht ht']
  have he : Real.exp (-1) ≤ Real.exp (-(1 - d.h) * t) :=
    Real.exp_le_exp.mpr (by nlinarith [d.h_pos])
  have h := mul_le_mul (tailDebt_ge_coefficient d) he (Real.exp_pos (-1)).le (tailDebt_pos d).le
  linarith


-- @@ L819-820 verbatim
/-- Release lower constant, given by `min (Real.exp (-2)) (Real.exp (-1) * tailCoefficient)`. -/
noncomputable def releaseLowerConstant : ℝ := min (Real.exp (-2)) (Real.exp (-1) * tailCoefficient)


-- @@ L822-823 verbatim
theorem releaseLowerConstant_pos : 0 < releaseLowerConstant :=
  lt_min (Real.exp_pos _) (mul_pos (Real.exp_pos _) tailCoefficient_pos)


-- @@ L825-829 verbatim
theorem normalizedLag_release_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ d.releaseStart + d.rampEnd) :
    Real.exp (-2) * (d.core.lam / 2) ≤ ReleaseMoments.normalizedLag d w.coefficients eta y := by
  rw [ReleaseMoments.ResetWitness.normalizedLag_release w eta hy hy']
  exact releaseLag_lower_all d (by linarith) (by linarith)


-- @@ L831-852 verbatim
/-- Positivity of the actual angular-history lag through the first half tail unit. -/
theorem normalizedLag_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    releaseLowerConstant * d.h ≤ ReleaseMoments.normalizedLag d w.coefficients eta y := by
  by_cases h1 : y ≤ d.releaseStart + d.rampEnd
  · have h := normalizedLag_release_lower w eta hy h1
    have hc : releaseLowerConstant ≤ Real.exp (-2) := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hc d.h_pos.le
    linarith [mul_le_mul_of_nonneg_left d.h_small.le (Real.exp_pos (-2)).le]
  · by_cases h2 : y ≤ tailStart d
    · rw [ReleaseMoments.ResetWitness.normalizedLag_hold w eta (le_of_not_ge h1) h2]
      have ht : y - (d.releaseStart + d.rampEnd) ≤ decayHold d := by
        dsimp [tailStart] at h2
        linarith
      have h := holdLag_lower d ht
      have he : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have hc : releaseLowerConstant ≤ tailCoefficient :=
        (min_le_right _ _).trans (by nlinarith [tailCoefficient_pos])
      exact (mul_le_mul_of_nonneg_right hc d.h_pos.le).trans h
    · rw [ReleaseMoments.ResetWitness.normalizedLag_tail w eta (le_of_not_ge h2)]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) d.h_pos.le).trans
        (tailLag_first_half_lower d (by linarith) (by linarith))


-- @@ L854-857 verbatim
theorem normalizedLag_pos {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    0 < ReleaseMoments.normalizedLag d w.coefficients eta y :=
  (mul_pos releaseLowerConstant_pos d.h_pos).trans_le (normalizedLag_lower w eta hy hy')


-- @@ L859-859 verbatim
/-! ## The designed suppression of the actual field -/


-- @@ L861-884 verbatim
theorem finalAngular_release_formula (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    finalAngular d (y, eta) = finalAngular d (d.releaseStart, eta) *
      Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) *
      (tailShape d (y - tailStart d) / (1 - d.rho)) := by
  have hR : d.core.holdStart ≤ d.releaseStart := by
    linarith [coreEndpoint_ge_hold d, flattenEnd_gt_core d, releaseStart_gt_flattenEnd d]
  have hrad := radialAmplitude_hold d.core.dropLength_pos.le hR hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_uniform d eta ((releaseStart_gt_flattenEnd d).le.trans hy),
    finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl,
    carrier, hrad, releaseAdjustment_eq]
  have hex : Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
      Real.exp (releasePrimitive d (y - d.releaseStart) + d.core.lam * (y - d.releaseStart)) =
      Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam d.releaseStart / 2) *
      (Real.exp (-(1 / 2 + d.core.lam) * (y - d.releaseStart)) *
        Real.exp (releasePrimitive d (y - d.releaseStart) + d.core.lam * (y - d.releaseStart))) *
      (tailShape d (y - tailStart d) / (1 - d.rho)) := by ring
    _ = _ := by rw [hex]


-- @@ L886-888 verbatim
theorem tailShape_ratio_le_two (d : TailData) (t : ℝ) : tailShape d t / (1 - d.rho) ≤ 2 := by
  apply (div_le_iff₀ (show 0 < 1 - d.rho by linarith [d.rho_lt_half])).mpr
  linarith [(tailShape_bounds d t).2, d.rho_lt_half]


-- @@ L890-892 verbatim
theorem plateau_amplitude_suppression (d : TailData) : Real.exp (-d.longHold) = d.h ^ 4 := by
  have he := OutgoingPulseBounds.exp_log_inverse_nat d.h_pos 4
  simpa [TailData.longHold] using he


-- @@ L894-913 verbatim
theorem finalAngular_suppressed (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.secondRampStart ≤ y) :
    finalAngular d (y, eta) ≤ 2 * finalAngular d (d.releaseStart, eta) * d.h ^ 4 := by
  have ht : d.secondRampStart ≤ y - d.releaseStart := by linarith
  have h0 : 0 ≤ y - d.releaseStart := by
    dsimp [TailData.secondRampStart] at ht
    linarith [d.longHold_pos]
  have hp := releasePrimitive_late_le d ht
  have hex : Real.exp (releasePrimitive d (y - d.releaseStart) - (y - d.releaseStart) / 2) ≤
      d.h ^ 4 := by
    rw [← plateau_amplitude_suppression]
    apply Real.exp_le_exp.mpr
    linarith [mul_nonneg d.h_pos.le (sub_nonneg.mpr ht)]
  have hratio0 : 0 ≤ tailShape d (y - tailStart d) / (1 - d.rho) :=
    div_nonneg (tailShape_pos d _).le (by linarith [d.rho_lt_half])
  rw [finalAngular_release_formula d eta (by linarith)]
  have h := mul_le_mul hex (tailShape_ratio_le_two d (y - tailStart d)) hratio0
    (pow_nonneg d.h_pos.le 4)
  have h' := mul_le_mul_of_nonneg_left h (finalAngular_pos d (d.releaseStart, eta)).le
  linarith


-- @@ L915-920 verbatim
theorem finalAngular_div_h_suppressed (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart + d.secondRampStart ≤ y) :
    finalAngular d (y, eta) / d.h ≤ 2 * finalAngular d (d.releaseStart, eta) * d.h ^ 3 := by
  apply (div_le_iff₀ d.h_pos).mpr
  convert! finalAngular_suppressed d eta hy using 1
  ring


-- @@ L922-927 verbatim
theorem profileSlope_bounds (d : TailData) (y : ℝ) :
    -1 ≤ profileSlope d y ∧ profileSlope d y ≤ -(3 * d.h / 4) := by
  have hs := releaseSlope_bounds d (y - d.releaseStart)
  have ht := tail_taper_log_derivative d (y - tailStart d)
  dsimp [profileSlope]
  constructor <;> linarith


-- @@ L929-930 verbatim
/-- Release A, given by `2 - 2 * profileSlope d y`. -/
noncomputable def releaseA (d : TailData) (y : ℝ) : ℝ := 2 - 2 * profileSlope d y


-- @@ L932-935 verbatim
theorem releaseA_bounds (d : TailData) (y : ℝ) : 2 < releaseA d y ∧ releaseA d y ≤ 4 := by
  have h := profileSlope_bounds d y
  dsimp [releaseA]
  constructor <;> linarith [d.h_pos]


-- @@ L937-942 verbatim
theorem releaseA_eq_derivative (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    releaseA d y = 1 - 2 * deriv (fun t => Real.log (finalAngular d (t, eta))) y := by
  rw [(finalAngular_log_hasDerivAt_on_release d eta hy).deriv]
  dsimp [releaseA]
  ring


-- @@ L944-944 verbatim
/-! ## Future integrals on the uniform release -/


-- @@ L946-962 verbatim
theorem finalAngular_release_decay (d : TailData) (eta : ℝ) {y t : ℝ}
    (hy : d.releaseStart ≤ y) (hyt : y ≤ t) :
    finalAngular d (t, eta) ≤ finalAngular d (y, eta) *
      Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) := by
  have hf : ContDiff ℝ ∞ (fun s => Real.log (finalAngular d (s, eta))) :=
    ((finalAngular_contDiff d).comp (contDiff_id.prodMk contDiff_const)).log
      (fun s => (finalAngular_pos d (s, eta)).ne')
  have hi := (convex_Ici d.releaseStart).image_sub_le_mul_sub_of_deriv_le
    hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
    (fun z hz => show deriv (fun s => Real.log (finalAngular d (s, eta))) z ≤
        -(1 / 2 + 3 * d.h / 4) by
      rw [(finalAngular_log_hasDerivAt_on_release d eta (interior_subset hz)).deriv]
      linarith [(profileSlope_bounds d z).2]) y hy t (hy.trans hyt) hyt
  have he := Real.exp_le_exp.mpr hi
  rw [Real.exp_sub, Real.exp_log (finalAngular_pos d _), Real.exp_log (finalAngular_pos d _)] at he
  have he' := (div_le_iff₀ (finalAngular_pos d (y, eta))).mp he
  simpa only [mul_comm] using he'


-- @@ L964-981 verbatim
theorem weighted_square_release_decay (d : TailData) (eta : ℝ) {y t : ℝ}
    (hy : d.releaseStart ≤ y) (hyt : y ≤ t) :
    Real.exp (t - y) * finalAngular d (t, eta) ^ 2 ≤
      finalAngular d (y, eta) ^ 2 * Real.exp (-(3 * d.h / 2) * (t - y)) := by
  have he := finalAngular_release_decay d eta hy hyt
  have hs := pow_le_pow_left₀ (finalAngular_pos d (t, eta)).le he 2
  have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos (t - y)).le
  have hex : Real.exp (t - y) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) ^ 2 =
      Real.exp (-(3 * d.h / 2) * (t - y)) := by
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (t - y) *
        (finalAngular d (y, eta) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y))) ^ 2 := hm
    _ = finalAngular d (y, eta) ^ 2 *
        (Real.exp (t - y) * Real.exp (-(1 / 2 + 3 * d.h / 4) * (t - y)) ^ 2) := by ring
    _ = _ := by rw [hex]


-- @@ L983-994 verbatim
theorem weighted_square_release_integrable (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    IntegrableOn (fun t => Real.exp (t - y) * finalAngular d (t, eta) ^ 2) (Ioi y) := by
  have ha : 0 < 3 * d.h / 2 := div_pos (mul_pos (by norm_num) d.h_pos) (by norm_num)
  have hm := (integrableOn_shift_exp ha y).const_mul (finalAngular d (y, eta) ^ 2)
  have hc : Continuous (fun t => Real.exp (t - y) * finalAngular d (t, eta) ^ 2) :=
    (Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul
      (((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact weighted_square_release_decay d eta hy ht.le


-- @@ L996-1009 verbatim
theorem weighted_square_release_integral_le (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    d.h * (∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, eta) ^ 2) ≤
      finalAngular d (y, eta) ^ 2 := by
  have ha : 0 < 3 * d.h / 2 := div_pos (mul_pos (by norm_num) d.h_pos) (by norm_num)
  have hm := (integrableOn_shift_exp ha y).const_mul (finalAngular d (y, eta) ^ 2)
  have hi := setIntegral_mono_on (weighted_square_release_integrable d eta hy) hm
    measurableSet_Ioi (fun t ht => weighted_square_release_decay d eta hy ht.le)
  rw [integral_const_mul, integral_shift_exp ha] at hi
  have h := mul_le_mul_of_nonneg_left hi d.h_pos.le
  have heq : d.h * (finalAngular d (y, eta) ^ 2 * (1 / (3 * d.h / 2))) =
      (2 / 3) * finalAngular d (y, eta) ^ 2 := by field_simp [d.h_pos.ne']
  rw [heq] at h
  linarith [sq_nonneg (finalAngular d (y, eta))]


-- @@ L1011-1014 verbatim
/-- Release future energy, given by `∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^
2`. -/
noncomputable def releaseFutureEnergy (d : TailData) (y : ℝ) : ℝ :=
  ∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^ 2


-- @@ L1016-1018 verbatim
/-- Release future mass, given by `∫ t in Ioi y, finalAngular d (t, 0) ^ 2`. -/
noncomputable def releaseFutureMass (d : TailData) (y : ℝ) : ℝ :=
  ∫ t in Ioi y, finalAngular d (t, 0) ^ 2


-- @@ L1020-1023 verbatim
/-- The backward-energy numerator in the uniform region. Its identification
with the source primitive uses the actual zero total energy. -/
noncomputable def releaseNumerator (d : TailData) (eta y : ℝ) : ℝ :=
  2 * eta * (d.h * releaseFutureEnergy d y - (1 / 2 + d.h) * releaseFutureMass d y)


-- @@ L1025-1026 verbatim
/-- Numerator constant, given by `2 * (1 + FuturePressureBounds.envelopeConstant)`. -/
noncomputable def numeratorConstant : ℝ := 2 * (1 + FuturePressureBounds.envelopeConstant)


-- @@ L1028-1030 verbatim
theorem numeratorConstant_pos : 0 < numeratorConstant := by
  dsimp [numeratorConstant]
  linarith [FuturePressureBounds.envelopeConstant_pos]


-- @@ L1032-1057 verbatim
theorem releaseNumerator_abs_le (d : TailData) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) :
    |releaseNumerator d eta y| ≤ numeratorConstant * finalAngular d (y, 0) ^ 2 := by
  have he0 : 0 ≤ releaseFutureEnergy d y := integral_nonneg (fun t => by positivity)
  have hm0 : 0 ≤ releaseFutureMass d y := integral_nonneg (fun t => sq_nonneg _)
  have he : d.h * releaseFutureEnergy d y ≤ finalAngular d (y, 0) ^ 2 :=
    weighted_square_release_integral_le d 0 hy
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  have hm : releaseFutureMass d y ≤
      FuturePressureBounds.envelopeConstant * finalAngular d (y, 0) ^ 2 :=
    FuturePressureBounds.future_square_integral_le d hy0 (by norm_num)
  have hA : 0 ≤ 1 / 2 + d.h := by linarith [d.h_pos]
  have hA' : 1 / 2 + d.h ≤ 1 := by linarith [d.h_lt_half]
  have hmass := mul_le_mul_of_nonneg_right hA' hm0
  have hs : |d.h * releaseFutureEnergy d y - (1 / 2 + d.h) * releaseFutureMass d y| ≤
      (1 + FuturePressureBounds.envelopeConstant) * finalAngular d (y, 0) ^ 2 := by
    have h := abs_sub_le (d.h * releaseFutureEnergy d y) 0 ((1 / 2 + d.h) * releaseFutureMass d y)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg d.h_pos.le he0),
      abs_of_nonneg (mul_nonneg hA hm0)] at h
    linarith
  dsimp [releaseNumerator, numeratorConstant]
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := mul_le_mul (mul_le_mul_of_nonneg_left heta (by norm_num : (0 : ℝ) ≤ 2)) hs
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
  linarith


-- @@ L1059-1059 verbatim
/-! ## Uniform smallness after dividing by the actual controller -/


-- @@ L1061-1074 verbatim
theorem releaseAmplitude_le_pulse (d : TailData) (eta : ℝ) :
    finalAngular d (d.releaseStart, eta) ≤ pulseAmplitude d.core := by
  have hy : d.core.pulseStart ≤ d.releaseStart := by
    have hs := endpoint_le_releaseStart d
    dsimp [OutgoingSchedule.Parameters.endpoint] at hs
    linarith [d.core.pulseLength_pos]
  have hr := radialAmplitude_hold d.core.dropLength_pos.le d.core.pulseStart_ge_hold hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl, hr]
  change pulseAmplitude d.core * Real.exp (-(1 / 2 + d.core.lam) *
    (d.releaseStart - d.core.pulseStart)) / 2 ≤ pulseAmplitude d.core
  have he : Real.exp (-(1 / 2 + d.core.lam) * (d.releaseStart - d.core.pulseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.core.lam_pos])
  nlinarith [pulseAmplitude_pos d.core]


-- @@ L1076-1080 verbatim
theorem releaseAmplitude_small (d : TailData)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (eta : ℝ) :
    finalAngular d (d.releaseStart, eta) ≤
      (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) :=
  (releaseAmplitude_le_pulse d eta).trans (OutgoingPulseBounds.pulseAmplitude_small d.core hwait)


-- @@ L1082-1087 verbatim
theorem finalAngular_le_releaseAmplitude (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : finalAngular d (y, eta) ≤ finalAngular d (d.releaseStart, eta) := by
  have he := finalAngular_release_decay d eta le_rfl hy
  have hex : Real.exp (-(1 / 2 + 3 * d.h / 4) * (y - d.releaseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.h_pos])
  nlinarith [finalAngular_pos d (d.releaseStart, eta)]


-- @@ L1089-1092 verbatim
/-- Release velocity ratio, given by `releaseNumerator d eta y / (finalAngular d (y, 0) *
ReleaseMoments.normalizedLag d c eta y)`. -/
noncomputable def releaseVelocityRatio (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) : ℝ :=
  releaseNumerator d eta y / (finalAngular d (y, 0) * ReleaseMoments.normalizedLag d c eta y)


-- @@ L1094-1105 verbatim
theorem releaseVelocityRatio_abs_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients eta
          y := by
  have hQ := normalizedLag_pos w eta hy hy'
  have hden := mul_pos (finalAngular_pos d (y, 0)) hQ
  rw [releaseVelocityRatio, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) ^ 2 := releaseNumerator_abs_le d heta hy
    _ = _ := by field_simp [hQ.ne']


-- @@ L1107-1108 verbatim
/-- Early ratio constant, given by `2 * numeratorConstant / Real.exp (-2)`. -/
noncomputable def earlyRatioConstant : ℝ := 2 * numeratorConstant / Real.exp (-2)

-- @@ L1109-1110 verbatim
/-- Late ratio constant, given by `2 * numeratorConstant / releaseLowerConstant`. -/
noncomputable def lateRatioConstant : ℝ := 2 * numeratorConstant / releaseLowerConstant


-- @@ L1112-1113 verbatim
theorem earlyRatioConstant_pos : 0 < earlyRatioConstant :=
  div_pos (mul_pos (by norm_num) numeratorConstant_pos) (Real.exp_pos _)


-- @@ L1115-1116 verbatim
theorem lateRatioConstant_pos : 0 < lateRatioConstant :=
  div_pos (mul_pos (by norm_num) numeratorConstant_pos) releaseLowerConstant_pos


-- @@ L1118-1153 verbatim
theorem releaseVelocityRatio_early {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y)
    (hy' : y ≤ d.releaseStart + d.rampEnd) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      earlyRatioConstant * (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ)
          := by
  have hyend : y ≤ tailStart d + 1 / 2 := by
    dsimp [tailStart]
    linarith [decayHold_pos d]
  have hQ := normalizedLag_pos w eta hy hyend
  have hQl := normalizedLag_release_lower w eta hy hy'
  have hcl : 0 < Real.exp (-2) * (d.core.lam / 2) := by
    exact mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num))
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients
        eta y :=
      releaseVelocityRatio_abs_le w heta hy hyend
    _ ≤ numeratorConstant * finalAngular d (d.releaseStart, 0) /
        ReleaseMoments.normalizedLag d w.coefficients eta y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (finalAngular_le_releaseAmplitude d 0 hy)
            numeratorConstant_pos.le) hQ.le
    _ ≤ numeratorConstant * finalAngular d (d.releaseStart, 0) / (Real.exp (-2) * (d.core.lam / 2))
        :=
      div_le_div_of_nonneg_left (mul_nonneg numeratorConstant_pos.le (finalAngular_pos d _).le) hcl
          hQl
    _ ≤ numeratorConstant * ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 :
        ℕ)) /
        (Real.exp (-2) * (d.core.lam / 2)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (releaseAmplitude_small d hwait 0) numeratorConstant_pos.le)
            hcl.le
    _ = _ := by
      dsimp [earlyRatioConstant]
      field_simp [d.core.lam_pos.ne']


-- @@ L1155-1199 verbatim
theorem releaseVelocityRatio_late {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart + d.secondRampStart ≤ y)
    (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      lateRatioConstant * (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ) :=
          by
  have hyR : d.releaseStart ≤ y := by
    dsimp [TailData.secondRampStart] at hy
    linarith [d.longHold_pos]
  have hQ := normalizedLag_pos w eta hyR hy'
  have hQl := normalizedLag_lower w eta hyR hy'
  have hcl := mul_pos releaseLowerConstant_pos d.h_pos
  have hh : d.h ^ (3 : ℕ) ≤ 1 := pow_le_one₀ d.h_pos.le (by linarith [d.h_lt_half])
  have hlam : d.core.lam ^ (30 : ℕ) ≤ d.core.lam ^ (29 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left (show d.core.lam ≤ 1 by linarith [d.core.lam_lt])
      (pow_nonneg d.core.lam_pos.le 29)
    simpa only [← pow_succ, mul_one] using h
  calc
    _ ≤ numeratorConstant * finalAngular d (y, 0) / ReleaseMoments.normalizedLag d w.coefficients
        eta y :=
      releaseVelocityRatio_abs_le w heta hyR hy'
    _ ≤ numeratorConstant * (2 * finalAngular d (d.releaseStart, 0) * d.h ^ 4) /
        ReleaseMoments.normalizedLag d w.coefficients eta y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (finalAngular_suppressed d 0 hy) numeratorConstant_pos.le) hQ.le
    _ ≤ numeratorConstant * (2 * finalAngular d (d.releaseStart, 0) * d.h ^ 4) /
        (releaseLowerConstant * d.h) :=
      div_le_div_of_nonneg_left (mul_nonneg numeratorConstant_pos.le
        (mul_nonneg (mul_nonneg (by
            norm_num) (finalAngular_pos d _).le) (pow_nonneg d.h_pos.le 4))) hcl hQl
    _ = lateRatioConstant * finalAngular d (d.releaseStart, 0) * d.h ^ 3 := by
      dsimp [lateRatioConstant]
      field_simp [d.h_pos.ne', releaseLowerConstant_pos.ne']
    _ ≤ lateRatioConstant * finalAngular d (d.releaseStart, 0) := by
      exact mul_le_of_le_one_right (mul_nonneg lateRatioConstant_pos.le (finalAngular_pos d _).le)
          hh
    _ ≤ lateRatioConstant *
        ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ)) :=
      mul_le_mul_of_nonneg_left (releaseAmplitude_small d hwait 0) lateRatioConstant_pos.le
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlam
        (mul_nonneg lateRatioConstant_pos.le
          (mul_nonneg d.core.P_pos.le (Real.exp_pos (Real.exp d.core.m + 12)).le))
      simpa only [mul_assoc] using h


-- @@ L1201-1204 verbatim
/-- Release cone constant, given by `(earlyRatioConstant + lateRatioConstant) * (P * Real.exp
(Real.exp m + 12))`. -/
noncomputable def releaseConeConstant (P m : ℝ) : ℝ :=
  (earlyRatioConstant + lateRatioConstant) * (P * Real.exp (Real.exp m + 12))


-- @@ L1206-1207 verbatim
theorem releaseConeConstant_pos {P m : ℝ} (hP : 0 < P) : 0 < releaseConeConstant P m :=
  mul_pos (add_pos earlyRatioConstant_pos lateRatioConstant_pos) (mul_pos hP (Real.exp_pos _))


-- @@ L1209-1225 verbatim
theorem releaseVelocityRatio_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    |releaseVelocityRatio d w.coefficients eta y| ≤
      releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) := by
  have hP : 0 ≤ (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (29 : ℕ) := by
    exact mul_nonneg (mul_nonneg d.core.P_pos.le (Real.exp_pos _).le) (pow_nonneg d.core.lam_pos.le
        _)
  dsimp [releaseConeConstant]
  by_cases h1 : y ≤ d.releaseStart + d.rampEnd
  · have h := releaseVelocityRatio_early w hwait heta hy h1
    linarith [mul_nonneg lateRatioConstant_pos.le hP]
  · have hb : d.releaseStart + d.secondRampStart ≤ y := by
      dsimp [TailData.rampEnd] at h1
      linarith
    have h := releaseVelocityRatio_late w hwait heta hb hy'
    linarith [mul_nonneg earlyRatioConstant_pos.le hP]


-- @@ L1227-1227 verbatim
/-! ## Actual slopes and the finite stress cone -/


-- @@ L1229-1240 verbatim
theorem corrected_release_eventuallyEq (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    (fun t => correctedAngular d c (t, eta)) =ᶠ[𝓝 y] (fun t => finalAngular d (t, eta)) := by
  have hcut : correctionCenter d + 43 / 20 < y := by
    dsimp [correctionCenter]
    linarith
  filter_upwards [lt_mem_nhds hcut] with t ht
  have hr : relative (c eta) (t - correctionCenter d) = 0 := by
    by_contra hn
    have h := relative_support (c eta) hn
    linarith [h.2]
  simp [correctedAngular, hr]


-- @@ L1242-1248 verbatim
theorem corrected_releaseA (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) :
    1 - 2 * deriv (fun t => Real.log (correctedAngular d c (t, eta))) y = releaseA d y := by
  have he := (corrected_release_eventuallyEq d c eta hy).fun_comp Real.log
  dsimp only [Function.comp_def] at he
  rw [he.deriv_eq]
  exact (releaseA_eq_derivative d eta hy).symm


-- @@ L1250-1257 verbatim
theorem corrected_bs_zero (d : TailData) (c : ℝ → Coeff) (Amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint < y) :
    2 * deriv (fun t => axial d.core Amp (t, eta)) y / correctedAngular d c (y, eta) = 0 := by
  have he : (fun t => axial d.core Amp (t, eta)) =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
    filter_upwards [lt_mem_nhds hy] with t ht
    exact axial_after_pulse d.core Amp eta ht.le
  rw [he.deriv_eq]
  simp


-- @@ L1259-1272 verbatim
theorem cone_of_zero_bs {a r p : ℝ} (ha : 2 < a) (ha' : a ≤ 4)
    (hr : |r| ≤ 1 / 2) (hp : 16 < p) :
    2 < p ∧ 2 < a ∧ a < ConeAlgebra.coneBound p (p * r) := by
  have hr2 : r ^ 2 ≤ 1 / 4 := by
    have h := abs_le.mp hr
    nlinarith only [h.1, h.2]
  have hmargin : 3 / 2 ≤ 2 - (a - 2) * r ^ 2 := by
    linarith only [hr2, mul_nonneg (sub_nonneg.mpr ha') (sq_nonneg r)]
  refine ⟨by linarith only [hp], ha, ?_⟩
  have h := ConeAlgebra.finite_amplitude_cone (c := 1) (j := r) (v := a) (p := p)
    (by linarith only [hp]) (by linarith only [hp]) (by linarith only [ha', hp]) ?_
  · simpa using h
  · have hmul := mul_le_mul_of_nonneg_left hmargin (show 0 ≤ p by linarith only [hp])
    linarith only [hmul, hp, ha']


-- @@ L1274-1277 verbatim
/-- Release P1, given by `XR * Real.exp y * ReleaseMoments.normalizedLag d c eta y /
CoordinateAlgebra.L d.h eta`. -/
noncomputable def releaseP1 (d : TailData) (c : ℝ → Coeff) (XR eta y : ℝ) : ℝ :=
  XR * Real.exp y * ReleaseMoments.normalizedLag d c eta y / CoordinateAlgebra.L d.h eta


-- @@ L1279-1282 verbatim
/-- Release radius threshold, given by `16 / (Real.exp d.releaseStart * (releaseLowerConstant *
d.h))`. -/
noncomputable def releaseRadiusThreshold (d : TailData) : ℝ :=
  16 / (Real.exp d.releaseStart * (releaseLowerConstant * d.h))


-- @@ L1284-1285 verbatim
theorem releaseRadiusThreshold_pos (d : TailData) : 0 < releaseRadiusThreshold d :=
  div_pos (by norm_num) (mul_pos (Real.exp_pos _) (mul_pos releaseLowerConstant_pos d.h_pos))


-- @@ L1287-1304 verbatim
theorem releaseP1_large {d : TailData} {K : ℝ} (w : ResetWitness d K) {XR eta y : ℝ}
    (hXR : releaseRadiusThreshold d < XR) (heta : eta ^ 2 ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    16 < releaseP1 d w.coefficients XR eta y := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  have hL1 : CoordinateAlgebra.L d.h eta ≤ 1 := by
    dsimp [CoordinateAlgebra.L]
    linarith [mul_nonneg d.h_pos.le (sq_nonneg eta)]
  have hXR0 := (releaseRadiusThreshold_pos d).trans hXR
  have hscale : 16 < XR * (Real.exp d.releaseStart * (releaseLowerConstant * d.h)) := by
    exact (div_lt_iff₀ (mul_pos (Real.exp_pos _) (mul_pos releaseLowerConstant_pos d.h_pos))).mp hXR
  have he := Real.exp_le_exp.mpr hy
  have hq := normalizedLag_lower w eta hy hy'
  have hprod := mul_le_mul he hq (mul_pos releaseLowerConstant_pos d.h_pos).le (Real.exp_pos y).le
  have hprod' := mul_le_mul_of_nonneg_left hprod hXR0.le
  unfold releaseP1
  apply (lt_div_iff₀ hL).mpr
  linarith


-- @@ L1306-1317 verbatim
theorem release_true_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {XR eta y : ℝ} (hXR : releaseRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    2 < releaseP1 d w.coefficients XR eta y ∧ 2 < releaseA d y ∧
      releaseA d y < ConeAlgebra.coneBound (releaseP1 d w.coefficients XR eta y)
        (releaseP1 d w.coefficients XR eta y * releaseVelocityRatio d w.coefficients eta y) := by
  have heta2 : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).2 heta
  exact cone_of_zero_bs (releaseA_bounds d y).1 (releaseA_bounds d y).2
    ((releaseVelocityRatio_uniform w hwait heta hy hy').trans hsmall)
    (releaseP1_large w hXR heta2 hy hy')


-- @@ L1319-1336 verbatim
theorem exists_release_cone_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m →
      d.core.lam < lam0 → releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) < 1 / 2 :=
          by
  have hC := releaseConeConstant_pos (m := m) hP
  refine ⟨(1 / 2) / releaseConeConstant P m, div_pos (by norm_num) hC, ?_⟩
  intro d hdP hdm hd
  rw [hdP, hdm]
  have hp : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := by
    have h := pow_le_one₀ d.core.lam_pos.le (show d.core.lam ≤ 1 by linarith [d.core.lam_lt])
      (n := 28)
    calc
      _ = d.core.lam * d.core.lam ^ (28 : ℕ) := by ring
      _ ≤ d.core.lam * 1 := mul_le_mul_of_nonneg_left h d.core.lam_pos.le
      _ = _ := mul_one _
  have hsmall := (lt_div_iff₀ hC).mp hd
  have h := mul_le_mul_of_nonneg_left hp hC.le
  linarith


-- @@ L1338-1338 verbatim
/-! ## Identification with the actual global histories -/


-- @@ L1340-1344 verbatim
theorem actualI_eq_releaseHistory {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    OutgoingHistories.I w (y, eta) = ReleaseMoments.history d w.coefficients eta y := by
  rw [OutgoingHistories.I_eq_integral, ReleaseMoments.ResetWitness.history_eq_integral w eta hy]
  rfl


-- @@ L1346-1356 verbatim
theorem actualI_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.dEta (OutgoingHistories.I w) (y, eta) = 0 := by
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.I_smooth w)]
  have he : (fun q => OutgoingHistories.I w (y, q)) =
      (fun q => ReleaseMoments.history d w.coefficients q y) :=
    funext (fun q => actualI_eq_releaseHistory w q hy0)
  rw [he]
  exact ReleaseMoments.ResetWitness.history_deriv_eta_zero w hy eta


-- @@ L1358-1370 verbatim
theorem actualQs_eq_normalizedLag {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.Qs w Amp (y, eta) = ReleaseMoments.normalizedLag d w.coefficients eta y := by
  have hyS := (endpoint_le_releaseStart d).trans hy
  have hy0 : 0 ≤ y := (UniformAngularReset.flattenEnd_pos d).le.trans
    ((releaseStart_gt_flattenEnd d).le.trans hy)
  rw [OutgoingHistories.Qs_after_endpoint w ha eta hyS, actualI_eta_zero w eta hy,
    mul_zero, sub_zero, actualI_eq_releaseHistory w eta hy0]
  change -1 + (1 - d.h) * ReleaseMoments.history d w.coefficients eta y /
    (Real.exp (3 * y / 2) * correctedAngular d w.coefficients (y, eta)) = _
  rw [ReleaseMoments.corrected_eq_release d w.coefficients eta hy]
  unfold ReleaseMoments.normalizedLag ReleaseMoments.releaseWeight
  ring


-- @@ L1372-1377 verbatim
theorem actual_energyWeight_eq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (eta t : ℝ) :
    Real.exp t * (OutgoingHistories.U d Amp (t, eta) ^ 2 - OutgoingHistories.E w (t, eta) ^ 2 / 2) =
      CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta t := by
  dsimp [OutgoingHistories.U, OutgoingHistories.E, CorrectedPulseAmplitude.energyIntegrand]
  rw [PulseAmplitude.axial_eq_of_amplitude_eq d.core Amp (fun _ => Amp eta) eta t rfl]


-- @@ L1379-1407 verbatim
/-- Zero actual total energy fixes the future energy term, including the reset. -/
theorem actualS_backward {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (y, eta) =
      (1 / 2 : ℝ) * ∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2 := by
  have hS : OutgoingHistories.S w Amp (y, eta) =
      ∫ t in Iic y, CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta t := by
    rw [OutgoingHistories.S_eq_integral w ha]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t _
    exact actual_energyWeight_eq w Amp eta t
  have hf : (∫ t in Ioi y, CorrectedPulseAmplitude.energyIntegrand d w.coefficients (Amp eta) eta
      t) =
      -(1 / 2 : ℝ) * ∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold CorrectedPulseAmplitude.energyIntegrand
    rw [axial_after_pulse d.core (fun _ => Amp eta) eta (hy.trans ht.le)]
    ring
  have hsplit := integral_add_compl measurableSet_Iic
    (CorrectedPulseAmplitude.energyIntegrand_integrable d w.coefficients (Amp eta) eta)
    (s := Iic y)
  rw [compl_Iic, ← hS, hf] at hsplit
  change _ = CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta at hsplit
  rw [hz] at hsplit
  linarith


-- @@ L1409-1430 verbatim
theorem actualS_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (y, eta) =
      (Real.exp y / 2) * releaseFutureEnergy d y := by
  rw [actualS_backward w ha eta ((endpoint_le_releaseStart d).trans hy) hz]
  unfold releaseFutureEnergy
  have he : (∫ t in Ioi y, Real.exp t * correctedAngular d w.coefficients (t, eta) ^ 2) =
      Real.exp y * ∫ t in Ioi y, Real.exp (t - y) * finalAngular d (t, 0) ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ReleaseMoments.corrected_eq_release d w.coefficients eta (hy.trans ht.le)]
    have hex : Real.exp y * Real.exp (t - y) = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hex]
  rw [he]
  ring


-- @@ L1432-1442 verbatim
theorem actualS_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta) = 0 := by
  have he : (fun q => OutgoingHistories.S w Amp (y, q)) =ᶠ[𝓝 eta]
      (fun _ => (Real.exp y / 2) * releaseFutureEnergy d y) := by
    filter_upwards [hz] with q hq
    exact actualS_uniform w ha q hy hq
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.S_smooth w ha), he.deriv_eq]
  simp


-- @@ L1444-1450 verbatim
theorem actualPi_eq_correctedPi {d : TailData} {K : ℝ} (w : ResetWitness d K) (y eta : ℝ) :
    OutgoingHistories.Pi w (y, eta) = CorrectedPressureBounds.correctedPi w y eta := by
  rw [OutgoingHistories.Pi_eq_past_integral,
      CorrectedPressureBounds.correctedPi_eq_axisPressure_add]
  rw [integral_div]
  dsimp [OutgoingHistories.E]
  ring


-- @@ L1452-1457 verbatim
theorem actualPi_uniform {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.Pi w (y, eta) = -(1 / 2 : ℝ) * releaseFutureMass d y := by
  rw [actualPi_eq_correctedPi, CorrectedPressureBounds.correctedPi_eta_independent_after w hy eta 0,
    CorrectedPressureBounds.correctedPi_eq_after w hy]
  rfl


-- @@ L1459-1466 verbatim
theorem actualPi_eta_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.releaseStart ≤ y) :
    OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta) = 0 := by
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Pi_smooth w)]
  have he : (fun q => OutgoingHistories.Pi w (y, q)) = CorrectedPressureBounds.correctedPi w y :=
    funext (fun q => actualPi_eq_correctedPi w y q)
  rw [he]
  exact CorrectedPressureBounds.correctedPi_deriv_eta_zero_after w hy eta


-- @@ L1468-1480 verbatim
theorem actualNs_eq_releaseNumerator {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.Ns w Amp (y, eta) = releaseNumerator d eta y := by
  have hz0 : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0 :=
    Filter.Eventually.self_of_nhds (x := eta)
      (p := fun q => CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) hz
  rw [OutgoingHistories.Ns_after_endpoint w ha eta ((endpoint_le_releaseStart d).trans hy),
    actualS_uniform w ha eta hy hz0, actualS_eta_zero w ha eta hy hz,
    actualPi_uniform w eta hy, actualPi_eta_zero w eta hy]
  dsimp [releaseNumerator, StressAlgebra.velocityExponent]
  field_simp; ring


-- @@ L1482-1489 verbatim
theorem amplitude_energy_zero_germ {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ)
    (hneg : CorrectedPulseAmplitude.constantTerm d w.coefficients eta < -(1 / 5)) :
    ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients
      (CorrectedPulseAmplitude.amplitude d w.coefficients q) q = 0 := by
  have hc : ContinuousAt (CorrectedPulseAmplitude.constantTerm d w.coefficients) eta :=
    (CorrectedPulseAmplitude.constantTerm_contDiff d w.smooth).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hneg)] with q hq
  exact CorrectedPulseAmplitude.amplitude_totalEnergy_zero d w.coefficients q hq.le


-- @@ L1491-1503 verbatim
theorem actualRatio_eq_releaseVelocityRatio {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.Ns w Amp (y, eta) /
      (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta)) =
        releaseVelocityRatio d w.coefficients eta y := by
  rw [actualNs_eq_releaseNumerator w ha eta hy hz, actualQs_eq_normalizedLag w ha eta hy]
  change releaseNumerator d eta y /
      (correctedAngular d w.coefficients (y, eta) * ReleaseMoments.normalizedLag d w.coefficients
          eta y) = _
  rw [ReleaseMoments.corrected_eq_release d w.coefficients eta hy]
  rfl


-- @@ L1505-1522 verbatim
theorem actual_release_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {XR eta y : ℝ} (hXR : releaseRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.releaseStart ≤ y) (hy' : y ≤ tailStart d + 1 / 2)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    0 < OutgoingHistories.Qs w Amp (y, eta) ∧
    2 < releaseA d y ∧
    2 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta ∧
    releaseA d y < ConeAlgebra.coneBound
      (XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta)
      ((XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta) *
        (OutgoingHistories.Ns w Amp (y, eta) /
          (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta)))) := by
  rw [actualRatio_eq_releaseVelocityRatio w ha eta hy hz, actualQs_eq_normalizedLag w ha eta hy]
  have hc := release_true_cone w hwait hsmall hXR heta hy hy'
  exact ⟨normalizedLag_pos w eta hy hy', hc.2.1, hc.1, hc.2.2⟩


-- @@ L1524-1524 verbatim
/-! ## Actual logarithmic derivatives through flattening and reset -/


-- @@ L1526-1528 verbatim
/-- Reset relative, given by `relative (w.coefficients eta) (y - correctionCenter d)`. -/
noncomputable def resetRelative {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) : ℝ :=
  relative (w.coefficients eta) (y - correctionCenter d)


-- @@ L1530-1533 verbatim
/-- Reset radial derivative, given by `deriv (relative (w.coefficients eta)) (y -
correctionCenter d)`. -/
noncomputable def resetRadialDerivative {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := deriv (relative (w.coefficients eta)) (y - correctionCenter d)


-- @@ L1535-1538 verbatim
/-- Reset eta derivative, given by `relative (deriv w.coefficients eta) (y - correctionCenter
d)`. -/
noncomputable def resetEtaDerivative {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := relative (deriv w.coefficients eta) (y - correctionCenter d)


-- @@ L1540-1544 verbatim
/-- Corrected flat slope, given by `flatteningSlope d y eta + resetRadialDerivative w eta y / (1
+ resetRelative w eta y)`. -/
noncomputable def correctedFlatSlope {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := flatteningSlope d y eta + resetRadialDerivative w eta y / (1 + resetRelative
        w eta y)


-- @@ L1546-1549 verbatim
/-- Corrected eta slope, given by `etaRate d eta y + resetEtaDerivative w eta y / (1 +
resetRelative w eta y)`. -/
noncomputable def correctedEtaSlope {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) : ℝ := etaRate d eta y + resetEtaDerivative w eta y / (1 + resetRelative w eta y)


-- @@ L1551-1555 verbatim
theorem resetFactor_ge_half {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    1 / 2 ≤ 1 + resetRelative w eta y := by
  have h := (abs_le.mp (w.small_jets eta (y - correctionCenter d)).1).1
  dsimp [resetRelative]
  linarith


-- @@ L1557-1575 verbatim
theorem correctedFlat_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    HasDerivAt (fun t => OutgoingHistories.E w (t, eta))
      (OutgoingHistories.E w (y, eta) * (correctedFlatSlope w eta y - 1 / 2)) y := by
  have he : (fun t => finalAngular d (t, eta)) =ᶠ[𝓝 y] (fun t => flattened d (t, eta)) := by
    filter_upwards [gt_mem_nhds hy'] with t ht
    exact UniformAngularReset.finalAngular_before_release d eta ht.le
  have hc : HasDerivAt (fun t => finalAngular d (t, eta))
      (finalAngular d (y, eta) * (flatteningSlope d y eta - 1 / 2)) y := by
    rw [UniformAngularReset.finalAngular_before_release d eta hy'.le]
    exact (flattened_hasDerivAt d eta hy).congr_of_eventuallyEq he
  have hr := (((relative_contDiff (w.coefficients eta)).differentiable (by simp)
    (y - correctionCenter d)).hasDerivAt).comp y ((hasDerivAt_id y).sub_const (correctionCenter d))
  have hd := hc.mul (hr.const_add 1)
  have hn : 1 + resetRelative w eta y ≠ 0 := by linarith [resetFactor_ge_half w eta y]
  convert! hd using 1
  dsimp [OutgoingHistories.E, correctedAngular, correctedFlatSlope, resetRelative,
      resetRadialDerivative] at *
  field_simp [hn]; ring


-- @@ L1577-1592 verbatim
theorem correctedEta_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    HasDerivAt (fun q => OutgoingHistories.E w (y, q))
      (OutgoingHistories.E w (y, eta) * correctedEtaSlope w eta y) eta := by
  have hc : HasDerivAt (fun q => finalAngular d (y, q))
      (finalAngular d (y, eta) * etaRate d eta y) eta := by
    convert! finalAngular_hasDerivAt_eta d eta y using 1
    dsimp [etaRate]
    ring
  have hr := ResetEnergyBounds.relative_coeff_hasDerivAt
    ((w.smooth.differentiable (by simp) eta).hasDerivAt) (y - correctionCenter d)
  have hd := hc.mul (hr.const_add 1)
  have hn : 1 + resetRelative w eta y ≠ 0 := by linarith [resetFactor_ge_half w eta y]
  convert! hd using 1
  dsimp [OutgoingHistories.E, correctedAngular, correctedEtaSlope, resetRelative,
      resetEtaDerivative] at *
  field_simp [hn]


-- @@ L1594-1604 verbatim
theorem correctedFlat_dY_H {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    OutgoingHistories.dY (OutgoingHistories.H w) (y, eta) =
      OutgoingHistories.H w (y, eta) * correctedFlatSlope w eta y := by
  have hh := (((hasDerivAt_id y).div_const 2).exp).mul (correctedFlat_hasDerivAt w eta hy hy')
  have he : HasDerivAt (fun t => OutgoingHistories.H w (t, eta))
      (OutgoingHistories.H w (y, eta) * correctedFlatSlope w eta y) y := by
    convert! hh using 1
    dsimp [OutgoingHistories.H]
    ring
  exact (OutgoingHistories.dY_hasDerivAt (OutgoingHistories.H_smooth w) (y, eta)).unique he


-- @@ L1606-1615 verbatim
theorem corrected_dEta_H {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    OutgoingHistories.dEta (OutgoingHistories.H w) (y, eta) =
      OutgoingHistories.H w (y, eta) * correctedEtaSlope w eta y := by
  have hh := (correctedEta_hasDerivAt w eta y).const_mul (Real.exp (y / 2))
  have he : HasDerivAt (fun q => OutgoingHistories.H w (y, q))
      (OutgoingHistories.H w (y, eta) * correctedEtaSlope w eta y) eta := by
    convert! hh using 1
    dsimp [OutgoingHistories.H]
    ring
  exact (OutgoingHistories.dEta_hasDerivAt (OutgoingHistories.H_smooth w) (y, eta)).unique he


-- @@ L1617-1627 verbatim
theorem correctedFlat_Sq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    OutgoingHistories.Sq w Amp (y, eta) = -correctedFlatSlope w eta y - d.h -
      StressAlgebra.axialExponent d.h * eta * correctedEtaSlope w eta y := by
  unfold OutgoingHistories.Sq OutgoingHistories.angularSource
  rw [OutgoingHistories.W_after_endpoint d ha eta hy, OutgoingHistories.U_after_endpoint d Amp eta
      hy,
    correctedFlat_dY_H w eta hy hy', corrected_dEta_H]
  dsimp only
  field_simp [(OutgoingHistories.H_pos w (y, eta)).ne']; ring


-- @@ L1629-1630 verbatim
/-- Reset jet constant, given by `Classical.choose relative_first_jet_bound`. -/
noncomputable def resetJetConstant : ℝ := Classical.choose relative_first_jet_bound


-- @@ L1632-1633 verbatim
theorem resetJetConstant_pos : 0 < resetJetConstant := (Classical.choose_spec
    relative_first_jet_bound).1


-- @@ L1635-1637 verbatim
theorem relative_radial_bound (c : Coeff) (y : ℝ) :
    |deriv (relative c) y| ≤ resetJetConstant * ‖c‖ :=
  ((Classical.choose_spec relative_first_jet_bound).2 c y).2


-- @@ L1639-1641 verbatim
/-- Reset source error, given by `(2 * resetJetConstant + 2) * (K * d.core.lam ^ (28 : ℕ))`. -/
noncomputable def resetSourceError (d : TailData) (K : ℝ) : ℝ :=
  (2 * resetJetConstant + 2) * (K * d.core.lam ^ (28 : ℕ))


-- @@ L1643-1655 verbatim
theorem reset_radial_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    |resetRadialDerivative w eta y / (1 + resetRelative w eta y)| ≤
      2 * resetJetConstant * (K * d.core.lam ^ (28 : ℕ)) := by
  have hden : 0 < 1 + resetRelative w eta y := by linarith [resetFactor_ge_half w eta y]
  have hr := (relative_radial_bound (w.coefficients eta) (y - correctionCenter d)).trans
    (mul_le_mul_of_nonneg_left (w.coefficient_bound eta) resetJetConstant_pos.le)
  change |resetRadialDerivative w eta y| ≤ _ at hr
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_le_mul_of_nonneg_left (resetFactor_ge_half w eta y)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) resetJetConstant_pos.le)
      (ResetEnergyBounds.coefficient_scale_nonneg w))
  linarith


-- @@ L1657-1667 verbatim
theorem reset_eta_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta y : ℝ) :
    |resetEtaDerivative w eta y / (1 + resetRelative w eta y)| ≤ 4 * (K * d.core.lam ^ (28 : ℕ)) :=
        by
  have hden : 0 < 1 + resetRelative w eta y := by linarith [resetFactor_ge_half w eta y]
  have hr := ResetEnergyBounds.relative_eta_bound w eta (y - correctionCenter d)
  change |resetEtaDerivative w eta y| ≤ _ at hr
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hprod := mul_le_mul_of_nonneg_left (resetFactor_ge_half w eta y)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (ResetEnergyBounds.coefficient_scale_nonneg w))
  linarith


-- @@ L1669-1675 verbatim
theorem eta_times_etaRate_nonpos (d : TailData) (eta y : ℝ) : eta * etaRate d eta y ≤ 0 := by
  have hp : 0 ≤ 2 * eta ^ 2 / (1 + eta ^ 2) := by positivity
  have hs := sigma_le_one ((y - d.core.endpoint) / flattenLength)
  calc
    eta * etaRate d eta y = (sigma ((y - d.core.endpoint) / flattenLength) - 1) *
        (2 * eta ^ 2 / (1 + eta ^ 2)) := by dsimp [etaRate]; ring
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hp


-- @@ L1677-1685 verbatim
theorem correctedFlatSlope_bounds {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta y : ℝ) (heta : eta ^ 2 ≤ 1) :
    -d.core.lam - 1 / 10 - resetSourceError d K ≤ correctedFlatSlope w eta y ∧
      correctedFlatSlope w eta y ≤ -d.core.lam + resetSourceError d K := by
  have hf := flatteningSlope_bounds d y eta heta
  have hr := abs_le.mp (reset_radial_ratio_bound w eta y)
  have hs := ResetEnergyBounds.coefficient_scale_nonneg w
  dsimp [correctedFlatSlope, resetSourceError]
  constructor <;> linarith


-- @@ L1687-1710 verbatim
theorem correctedFlat_source_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) (heta : |eta| ≤ 1) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    d.core.lam / 2 - resetSourceError d K ≤ OutgoingHistories.Sq w Amp (y, eta) := by
  have heta2 : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).2 heta
  have hf := flatteningSlope_bounds d y eta heta2
  have hr := abs_le.mp (reset_radial_ratio_bound w eta y)
  have hD : 0 ≤ StressAlgebra.axialExponent d.h := by
    dsimp [StressAlgebra.axialExponent]
    linarith [d.h_lt_half]
  have hD' : StressAlgebra.axialExponent d.h ≤ 1 / 2 := by
    dsimp [StressAlgebra.axialExponent]
    linarith [d.h_pos]
  have hbase := mul_nonpos_of_nonneg_of_nonpos hD (eta_times_etaRate_nonpos d eta y)
  have hDEta : |StressAlgebra.axialExponent d.h * eta| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hD]
    linarith [mul_le_mul_of_nonneg_left heta hD]
  have he := mul_le_mul hDEta (reset_eta_ratio_bound w eta y) (abs_nonneg _) (by
      norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← abs_mul] at he
  have he' := (le_abs_self _).trans he
  rw [correctedFlat_Sq w ha eta hy hy']
  dsimp [correctedFlatSlope, correctedEtaSlope, resetSourceError]
  linarith [d.h_small]


-- @@ L1712-1721 verbatim
theorem correctedFlat_geometry {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hsmall : resetSourceError d K ≤ d.core.lam / 4) (eta y : ℝ) (heta : eta ^ 2 ≤ 1) :
    2 < 2 - 2 * correctedFlatSlope w eta y ∧ 2 - 2 * correctedFlatSlope w eta y ≤ 4 ∧
      1 + correctedFlatSlope w eta y ≤ 1 := by
  have h := correctedFlatSlope_bounds w eta y heta
  constructor
  · linarith [d.core.lam_pos]
  constructor
  · linarith [d.core.lam_lt]
  · linarith [d.core.lam_pos]


-- @@ L1723-1749 verbatim
theorem ode_constant_barrier {q a b : ℝ → ℝ} (hq : Continuous q) (ha : Continuous a)
    {lo hi B : ℝ} (hlh : lo ≤ hi) (hinit : B ≤ q lo)
    (hODE : ∀ t ∈ Ioo lo hi, HasDerivAt q (b t - a t * q t) t)
    (hsource : ∀ t ∈ Ioo lo hi, a t * B ≤ b t) : B ≤ q hi := by
  let g : ℝ → ℝ := fun t => Real.exp (primitive a t) * (q t - B)
  have hp : Continuous (primitive a) := continuous_iff_continuousAt.mpr
    (fun t => (primitive_hasDerivAt ha t).continuousAt)
  have hg : Continuous g := (Real.continuous_exp.comp hp).mul (hq.sub continuous_const)
  have hgd : ∀ t ∈ Ioo lo hi,
      HasDerivAt g (Real.exp (primitive a t) * (b t - a t * B)) t := by
    intro t ht
    have hd := ((primitive_hasDerivAt ha t).exp).mul ((hODE t ht).sub_const B)
    convert! hd using 1
    ring
  have hm : MonotoneOn g (Icc lo hi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc lo hi) hg.continuousOn
    · intro t ht
      have ht' : t ∈ Ioo lo hi := by simpa only [interior_Icc] using ht
      exact (hgd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo lo hi := by simpa only [interior_Icc] using ht
      rw [(hgd t ht').deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hsource t ht'))
  have hg0 : 0 ≤ g lo := mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hinit)
  have hg1 : 0 ≤ g hi := hg0.trans (hm ⟨le_rfl, hlh⟩ ⟨hlh, le_rfl⟩ hlh)
  change 0 ≤ Real.exp (primitive a hi) * (q hi - B) at hg1
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hg1)


-- @@ L1751-1782 verbatim
theorem flatten_Qs_lower_of_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : resetSourceError d K ≤ d.core.lam / 4) (eta : ℝ) (heta : |eta| ≤ 1)
    (hinit : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (d.core.endpoint, eta))
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta) := by
  have heta2 : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).2 heta
  let rate : ℝ → ℝ := fun t => 1 + OutgoingHistories.dY (OutgoingHistories.H w) (t, eta) /
    OutgoingHistories.H w (t, eta)
  have hr : Continuous rate := by
    apply continuous_const.add
    exact ((OutgoingHistories.dY_smooth (OutgoingHistories.H_smooth w)).continuous.comp
      (continuous_id.prodMk continuous_const)).div
      ((OutgoingHistories.H_smooth w).continuous.comp (continuous_id.prodMk continuous_const))
      (fun t => (OutgoingHistories.H_pos w (t, eta)).ne')
  apply ode_constant_barrier (b := fun t => OutgoingHistories.Sq w Amp (t, eta))
    ((OutgoingHistories.Qs_smooth w ha).continuous.comp (continuous_id.prodMk continuous_const)) hr
        hy hinit
  · intro t _
    exact OutgoingHistories.Qs_hasDerivAt w ha (t, eta)
  · intro t ht
    have htR : t < d.releaseStart := ht.2.trans_le hy'
    have hr_eq : rate t = 1 + correctedFlatSlope w eta t := by
      dsimp [rate]
      rw [correctedFlat_dY_H w eta ht.1.le htR]
      field_simp [(OutgoingHistories.H_pos w (t, eta)).ne']
    rw [hr_eq]
    have hrate := (correctedFlat_geometry w hsmall eta t heta2).2.2
    have hsource := correctedFlat_source_lower w ha eta heta ht.1.le htR
    have hm := mul_le_mul_of_nonneg_right hrate (div_nonneg d.core.lam_pos.le (by
        norm_num : (0 : ℝ) ≤ 4))
    linarith


-- @@ L1784-1795 verbatim
theorem corrected_flatten_Qs_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hpulse : PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8)
    (hh1 : d.h ≤ 1 / 100) (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hreset : resetSourceError d K ≤ d.core.lam / 4)
    (eta : ℝ) (heta : |eta| ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    d.core.lam / 4 ≤ OutgoingHistories.Qs w
      (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) := by
  exact flatten_Qs_lower_of_endpoint w (CorrectedPulseAmplitude.amplitude_contDiff d w.smooth)
    hreset eta heta
    (PulseCone.corrected_Qs_endpoint_lower w hK hwait hsmall hscale hpulse hh1 hhT heta) hy hy'


-- @@ L1797-1797 verbatim
/-! ## Energy and its parameter derivative on the finite post-pulse interval -/


-- @@ L1799-1812 verbatim
theorem corrected_density_prefix_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y)
    (hy' : y ≤ d.releaseStart) :
    Real.exp y * OutgoingHistories.E w (y, eta) ^ 2 ≤
      (9 / 4 : ℝ) * energyDensity d eta d.core.endpoint := by
  have hr := abs_le.mp (w.small_jets eta (y - correctionCenter d)).1
  have hr2 : (1 + relative (w.coefficients eta) (y - correctionCenter d)) ^ 2 ≤ 9 / 4 := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hr2 (energyDensity_pos d eta y).le
  have he := energyDensity_prefix_le d eta heta hy hy'
  change Real.exp y * (finalAngular d (y, eta) *
    (1 + relative (w.coefficients eta) (y - correctionCenter d))) ^ 2 ≤ _
  dsimp [energyDensity] at h he ⊢
  linarith


-- @@ L1814-1823 verbatim
theorem corrected_square_prefix_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) {y : ℝ} (hy : d.core.endpoint ≤ y)
    (hy' : y ≤ d.releaseStart) :
    OutgoingHistories.E w (y, eta) ^ 2 ≤ (9 / 4 : ℝ) * finalAngular d (d.core.endpoint, eta) ^ 2 :=
        by
  have hd := corrected_density_prefix_le w eta heta hy hy'
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy)
    (sq_nonneg (OutgoingHistories.E w (y, eta)))
  dsimp [energyDensity] at hd
  nlinarith [Real.exp_pos d.core.endpoint]


-- @@ L1825-1831 verbatim
theorem correctedEtaSlope_abs_le {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta y : ℝ) :
    |correctedEtaSlope w eta y| ≤ 5 := by
  exact (abs_add_le _ _).trans (by
    have h1 := etaRate_bound d eta y
    have h2 := reset_eta_ratio_bound w eta y
    linarith)


-- @@ L1833-1839 verbatim
theorem actualS_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    (hz : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0) :
    OutgoingHistories.S w Amp (d.core.endpoint, eta) =
      (1 / 2 : ℝ) * (postPulseEnergy d eta + ResetEnergyBounds.resetEnergy d w.coefficients eta) :=
          by
  rw [actualS_backward w ha eta le_rfl hz, ResetEnergyBounds.integral_corrected_energy]


-- @@ L1841-1856 verbatim
theorem actualS_eta_endpoint {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) :
    OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta) =
      (1 / 2 : ℝ) * (deriv (postPulseEnergy d) eta +
        deriv (ResetEnergyBounds.resetEnergy d w.coefficients) eta) := by
  have he : (fun q => OutgoingHistories.S w Amp (d.core.endpoint, q)) =ᶠ[𝓝 eta]
      (fun q => (1 / 2 : ℝ) * (postPulseEnergy d q + ResetEnergyBounds.resetEnergy d w.coefficients
          q)) := by
    filter_upwards [hz] with q hq
    exact actualS_endpoint w ha q hq
  have hd := (((postPulseEnergy_contDiff d).differentiable (by simp) eta).hasDerivAt.fun_add
    (((ResetEnergyBounds.resetEnergy_contDiff d w.smooth).differentiable (by
        simp) eta).hasDerivAt)).const_mul
      (1 / 2 : ℝ)
  rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.S_smooth w ha), he.deriv_eq, hd.deriv]


-- @@ L1858-1866 verbatim
theorem actualS_after_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => OutgoingHistories.S w Amp (t, eta))
      (-(Real.exp y * OutgoingHistories.E w (y, eta) ^ 2) / 2) y := by
  have hd := OutgoingHistories.S_hasDerivAt w ha (y, eta)
  dsimp [OutgoingHistories.X, OutgoingHistories.energyDensity] at hd
  rw [OutgoingHistories.U_after_endpoint d Amp eta hy] at hd
  convert! hd using 1
  ring


-- @@ L1868-1880 verbatim
theorem actualS_eta_after_hasDerivAt {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    HasDerivAt (fun t => OutgoingHistories.dEta (OutgoingHistories.S w Amp) (t, eta))
      (-(Real.exp y * OutgoingHistories.E w (y, eta) ^ 2) * correctedEtaSlope w eta y) y := by
  have hd := OutgoingHistories.dEta_S_hasDerivAt w ha (y, eta)
  have he : OutgoingHistories.dEta (OutgoingHistories.E w) (y, eta) =
      OutgoingHistories.E w (y, eta) * correctedEtaSlope w eta y :=
    (OutgoingHistories.dEta_hasDerivAt (OutgoingHistories.E_smooth w) (y, eta)).unique
      (correctedEta_hasDerivAt w eta y)
  rw [OutgoingHistories.U_after_endpoint d Amp eta hy, he] at hd
  dsimp [OutgoingHistories.X] at hd
  convert! hd using 1
  ring


-- @@ L1882-1888 verbatim
theorem abs_increment_le {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ C) : |f b - f a| ≤ C * (b - a) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1, ht.2.le⟩) b ⟨hab, le_rfl⟩
  simpa only [Real.norm_eq_abs] using h


-- @@ L1890-1893 verbatim
/-- Finite energy budget, given by `flattenLength + releaseConstant + 40 + 20 * (d.releaseStart
- d.core.endpoint)`. -/
noncomputable def finiteEnergyBudget (d : TailData) : ℝ :=
  flattenLength + releaseConstant + 40 + 20 * (d.releaseStart - d.core.endpoint)


-- @@ L1895-1897 verbatim
theorem finiteEnergyBudget_pos (d : TailData) : 0 < finiteEnergyBudget d := by
  dsimp [finiteEnergyBudget]
  linarith [flattenLength_pos, releaseConstant_pos, endpoint_le_releaseStart d]


-- @@ L1899-1955 verbatim
theorem actualS_finite_bounds {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : eta ^ 2 ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    |OutgoingHistories.S w Amp (y, eta)| ≤ finiteEnergyBudget d * energyDensity d eta
        d.core.endpoint ∧
    |OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta)| ≤
      finiteEnergyBudget d * energyDensity d eta d.core.endpoint := by
  have hz0 : CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta = 0 :=
    Filter.Eventually.self_of_nhds (x := eta)
      (p := fun q => CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0) hz
  have hD := (energyDensity_pos d eta d.core.endpoint).le
  have hL : 0 ≤ d.releaseStart - d.core.endpoint := sub_nonneg.mpr (endpoint_le_releaseStart d)
  have hSI : |OutgoingHistories.S w Amp (d.core.endpoint, eta)| ≤
      ((d.releaseStart - d.core.endpoint + releaseConstant) / 2 + 12) * energyDensity d eta
          d.core.endpoint := by
    rw [actualS_endpoint w ha eta hz0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsum := abs_add_le (postPulseEnergy d eta) (ResetEnergyBounds.resetEnergy d w.coefficients
        eta)
    rw [abs_of_nonneg (postPulseEnergy_nonneg d eta)] at hsum
    have hR := ResetEnergyBounds.resetEnergy_abs_le w eta heta
    have hs := mul_le_mul_of_nonneg_right hsmall hD
    linarith [postPulseEnergy_le_length d eta heta]
  have hSEI : |OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta)| ≤
      (flattenLength + 12) * energyDensity d eta d.core.endpoint := by
    rw [actualS_eta_endpoint w ha eta hz, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsum := abs_add_le (deriv (postPulseEnergy d) eta)
      (deriv (ResetEnergyBounds.resetEnergy d w.coefficients) eta)
    have hs := mul_le_mul_of_nonneg_right hsmall hD
    linarith [abs_deriv_postPulseEnergy_le d eta heta, ResetEnergyBounds.resetEnergy_deriv_abs_le
        w eta heta]
  have hSD := abs_increment_le hy (fun t ht => actualS_after_hasDerivAt w ha eta ht.1)
    (C := 2 * energyDensity d eta d.core.endpoint) (fun t ht => by
      rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      norm_num
      have hd := corrected_density_prefix_le w eta heta ht.1 (ht.2.trans hy')
      linarith)
  have hSED := abs_increment_le hy (fun t ht => actualS_eta_after_hasDerivAt w ha eta ht.1)
    (C := 12 * energyDensity d eta d.core.endpoint) (fun t ht => by
      rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      have hd := corrected_density_prefix_le w eta heta ht.1 (ht.2.trans hy')
      have hs := mul_le_mul_of_nonneg_left (correctedEtaSlope_abs_le w hsmall eta t)
        (mul_nonneg (Real.exp_pos t).le (sq_nonneg (OutgoingHistories.E w (t, eta))))
      linarith)
  have hlen := mul_le_mul_of_nonneg_right (show y - d.core.endpoint ≤ d.releaseStart -
      d.core.endpoint by
      linarith) hD
  have hS := abs_sub_le (OutgoingHistories.S w Amp (y, eta))
    (OutgoingHistories.S w Amp (d.core.endpoint, eta)) 0
  have hSE := abs_sub_le (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y, eta))
    (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (d.core.endpoint, eta)) 0
  simp only [sub_zero] at hS hSE
  dsimp [finiteEnergyBudget]
  constructor <;> linarith [mul_nonneg flattenLength_pos.le hD, mul_nonneg releaseConstant_pos.le
      hD,
    mul_nonneg hL hD]


-- @@ L1957-1960 verbatim
/-- Finite numerator budget, given by `5 * finiteEnergyBudget d + 12 *
CorrectedPressureBounds.correctedConstant`. -/
noncomputable def finiteNumeratorBudget (d : TailData) : ℝ :=
  5 * finiteEnergyBudget d + 12 * CorrectedPressureBounds.correctedConstant


-- @@ L1962-1966 verbatim
theorem finiteNumeratorBudget_pos (d : TailData) : 0 < finiteNumeratorBudget d := by
  dsimp [finiteNumeratorBudget]
  have := finiteEnergyBudget_pos d
  have := CorrectedPressureBounds.correctedConstant_pos
  positivity


-- @@ L1968-2052 verbatim
theorem actualNs_finite_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : |eta| ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    |OutgoingHistories.Ns w Amp (y, eta)| ≤
      finiteNumeratorBudget d * finalAngular d (d.core.endpoint, eta) ^ 2 := by
  have heta2 : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).2 heta
  have hS := actualS_finite_bounds w ha hsmall eta heta2 hz hy hy'
  have hB := (finiteEnergyBudget_pos d).le
  have hF := sq_nonneg (finalAngular d (d.core.endpoint, eta))
  have hdiv : ∀ z : ℝ, |z| ≤ finiteEnergyBudget d * energyDensity d eta d.core.endpoint →
      |z / Real.exp y| ≤ finiteEnergyBudget d * finalAngular d (d.core.endpoint, eta) ^ 2 := by
    intro z hz
    rw [abs_div, abs_of_pos (Real.exp_pos y)]
    apply (div_le_iff₀ (Real.exp_pos y)).mpr
    have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) (mul_nonneg hB hF)
    dsimp [energyDensity] at hz
    linarith only [hz, hm]
  have hs0 := hdiv _ hS.1
  have hs1 := hdiv _ hS.2
  have hP := CorrectedPressureBounds.corrected_bounds_of_small w hsmall
    ((SchedulePressure.endpoint_pos d).le.trans hy) heta
  have hP0 : |OutgoingHistories.Pi w (y, eta)| ≤
      CorrectedPressureBounds.correctedConstant * OutgoingHistories.E w (y, eta) ^ 2 := by
    rw [actualPi_eq_correctedPi]
    exact hP.1
  have hP1 : |OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta)| ≤
      CorrectedPressureBounds.correctedConstant * OutgoingHistories.E w (y, eta) ^ 2 := by
    rw [OutgoingHistories.dEta_eq_deriv (OutgoingHistories.Pi_smooth w)]
    have he : (fun q => OutgoingHistories.Pi w (y, q)) = CorrectedPressureBounds.correctedPi w y :=
      funext (actualPi_eq_correctedPi w y)
    rw [he]
    exact hP.2
  have hE := mul_le_mul_of_nonneg_left (corrected_square_prefix_le w eta heta2 hy hy')
    CorrectedPressureBounds.correctedConstant_pos.le
  have hd : |StressAlgebra.coordinateFactor eta| ≤ 1 := by
    dsimp [StressAlgebra.coordinateFactor]
    rw [abs_of_nonneg (by linarith only [heta2] : 0 ≤ 1 - eta ^ 2)]
    linarith only [sq_nonneg eta]
  have hh : |4 * d.h * eta| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos d.h_pos]
    have hm := mul_le_mul_of_nonneg_left heta (show 0 ≤ 4 * d.h by linarith only [d.h_pos])
    linarith only [hm, d.h_lt_half]
  have ha0 : 0 ≤ StressAlgebra.velocityExponent d.h := by
    dsimp [StressAlgebra.velocityExponent]; linarith only [d.h_pos]
  have ha1 : StressAlgebra.velocityExponent d.h ≤ 1 := by
    dsimp [StressAlgebra.velocityExponent]; linarith only [d.h_lt_half]
  have hav : |4 * StressAlgebra.velocityExponent d.h * eta| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg ha0]
    have hm := mul_le_mul_of_nonneg_left heta (show 0 ≤ 4 * StressAlgebra.velocityExponent d.h by
        positivity)
    linarith only [hm, ha1]
  have h1 := mul_le_mul hh hs0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul hd hs1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h3 := mul_le_mul hav (hP0.trans hE) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  have h4 := mul_le_mul hd (hP1.trans hE) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [← abs_mul] at h1 h2 h3 h4
  rw [OutgoingHistories.Ns_after_endpoint w ha eta hy]
  rw [show (4 * d.h * eta * OutgoingHistories.S w Amp (y, eta) -
      StressAlgebra.coordinateFactor eta * OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta)) /
      Real.exp y = 4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) /
        Real.exp y) by ring]
  have ht1 := abs_sub_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y)) 0
    (StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
        eta) / Real.exp y))
  have ht2 := abs_add_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) / Real.exp y))
    (4 * StressAlgebra.velocityExponent d.h * eta * OutgoingHistories.Pi w (y, eta))
  have ht3 := abs_sub_le
    (4 * d.h * eta * (OutgoingHistories.S w Amp (y, eta) / Real.exp y) -
      StressAlgebra.coordinateFactor eta * (OutgoingHistories.dEta (OutgoingHistories.S w Amp) (y,
          eta) / Real.exp y) +
      4 * StressAlgebra.velocityExponent d.h * eta * OutgoingHistories.Pi w (y, eta)) 0
    (StressAlgebra.coordinateFactor eta * OutgoingHistories.dEta (OutgoingHistories.Pi w) (y, eta))
  simp only [sub_zero, zero_sub, abs_neg] at ht1 ht3
  dsimp [finiteNumeratorBudget]
  linarith only [h1, h2, h3, h4, ht1, ht2, ht3, mul_nonneg hB hF,
    mul_nonneg CorrectedPressureBounds.correctedConstant_pos.le hF]


-- @@ L2054-2060 verbatim
theorem lambda_log_bound (d : TailData) : d.core.lam * Real.log (1 / d.core.lam) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr d.core.lam_pos)
  have hm := mul_le_mul_of_nonneg_left h d.core.lam_pos.le
  have hid : d.core.lam * (1 / d.core.lam - 1) = 1 - d.core.lam := by
    field_simp [d.core.lam_pos.ne']
  rw [hid] at hm
  linarith [d.core.lam_pos]


-- @@ L2062-2068 verbatim
theorem lambda_finite_length_bound (d : TailData) :
    d.core.lam * (d.releaseStart - d.core.endpoint) ≤ flattenLength + 30 := by
  have hf := mul_le_mul_of_nonneg_right (show d.core.lam ≤ 1 by
      linarith [d.core.lam_lt]) flattenLength_pos.le
  have hl := lambda_log_bound d
  dsimp [TailData.releaseStart, TailData.flattenEnd, TailData.uniformWait]
  linarith


-- @@ L2070-2074 verbatim
/-- Finite numerator constant, given by `5 * (flattenLength + releaseConstant + 40 + 20 *
(flattenLength + 30)) + 12 * CorrectedPressureBounds.correctedConstant`. -/
noncomputable def finiteNumeratorConstant : ℝ :=
  5 * (flattenLength + releaseConstant + 40 + 20 * (flattenLength + 30)) +
    12 * CorrectedPressureBounds.correctedConstant


-- @@ L2076-2081 verbatim
theorem finiteNumeratorConstant_pos : 0 < finiteNumeratorConstant := by
  dsimp [finiteNumeratorConstant]
  have := flattenLength_pos
  have := releaseConstant_pos
  have := CorrectedPressureBounds.correctedConstant_pos
  positivity


-- @@ L2083-2092 verbatim
theorem finiteNumeratorBudget_bound (d : TailData) :
    d.core.lam * finiteNumeratorBudget d ≤ finiteNumeratorConstant := by
  have hl : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
  have hbase := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ flattenLength + releaseConstant + 40 by
        linarith [flattenLength_pos, releaseConstant_pos])
  have hP := mul_le_mul_of_nonneg_right hl CorrectedPressureBounds.correctedConstant_pos.le
  have hlen := lambda_finite_length_bound d
  dsimp [finiteNumeratorBudget, finiteEnergyBudget, finiteNumeratorConstant]
  linarith


-- @@ L2094-2098 verbatim
/-! ## A lower amplitude bound up to release

The finite waiting interval loses only eighteen powers of `lam`, whereas the
earlier scheduled wait has already supplied thirty powers.
-/


-- @@ L2100-2110 verbatim
theorem flattenFactor_ge_half (d : TailData) (eta y : ℝ) : 1 / 2 ≤ flattenFactor d (y, eta) := by
  have hJ : 0 ≤ logShape eta := Real.log_nonneg (by linarith [sq_nonneg eta])
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right (sigma_le_one ((y - d.core.endpoint) / flattenLength)) hlog
  have hp := mul_nonneg (sigma_nonneg ((y - d.core.endpoint) / flattenLength)) hJ
  have hh : -Real.log 2 ≤ sigma ((y - d.core.endpoint) / flattenLength) * (logShape eta - Real.log
      2) := by
    linarith
  have he := Real.exp_le_exp.mpr hh
  simp only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at he
  exact he


-- @@ L2112-2113 verbatim
/-- Finite amplitude constant, given by `Real.exp (-(3 / 5 : ℝ) * flattenLength) / 4`. -/
noncomputable def finiteAmplitudeConstant : ℝ := Real.exp (-(3 / 5 : ℝ) * flattenLength) / 4


-- @@ L2115-2116 verbatim
theorem finiteAmplitudeConstant_pos : 0 < finiteAmplitudeConstant := div_pos (Real.exp_pos _) (by
    norm_num)


-- @@ L2118-2161 verbatim
theorem corrected_amplitude_finite_lower {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart) :
    finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18 : ℕ) ≤
      OutgoingHistories.E w (y, eta) := by
  have hE := finalAngular_pos d (d.core.endpoint, eta)
  have hr := radialAmplitude_hold d.core.dropLength_pos.le (coreEndpoint_ge_hold d) hy
    (P := d.core.P) (lam := d.core.lam)
  have hang : angular d.core.P d.core.dropLength d.core.lam (y, eta) =
      finalAngular d (d.core.endpoint, eta) * Real.exp (-(1 / 2 + d.core.lam) * (y -
          d.core.endpoint)) := by
    rw [finalAngular_before d eta le_rfl]
    dsimp [angular]
    rw [hr]
    ring
  have hpow : Real.exp (-(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint)) =
      Real.exp (-(3 / 5 : ℝ) * flattenLength) * d.core.lam ^ (18 : ℕ) := by
    have h18 : Real.exp (-(18 : ℝ) * Real.log (1 / d.core.lam)) = d.core.lam ^ (18 : ℕ) := by
      simpa using OutgoingPulseBounds.exp_log_inverse_nat d.core.lam_pos 18
    rw [show -(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint) =
      -(3 / 5 : ℝ) * flattenLength + -(18 : ℝ) * Real.log (1 / d.core.lam) by
        dsimp [TailData.releaseStart, TailData.flattenEnd, TailData.uniformWait]; ring,
      Real.exp_add, h18]
  have hrate : -(3 / 5 : ℝ) * (d.releaseStart - d.core.endpoint) ≤
      -(1 / 2 + d.core.lam) * (y - d.core.endpoint) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 / 2 + d.core.lam ≤ (3 / 5 : ℝ) by
        linarith only [d.core.lam_lt])
      (sub_nonneg.mpr hy)
    linarith only [hm, hy']
  have he := Real.exp_le_exp.mpr hrate
  rw [hpow] at he
  have hflat := flattenFactor_ge_half d eta y
  have hrel := resetFactor_ge_half w eta y
  have he1 := mul_le_mul_of_nonneg_left he hE.le
  have he2 := mul_le_mul he1 hflat (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg hE.le (Real.exp_pos _).le)
  have he3 := mul_le_mul he2 hrel (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (mul_nonneg (mul_nonneg hE.le (Real.exp_pos _).le)
      ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hflat))
  change _ ≤ finalAngular d (y, eta) * (1 + resetRelative w eta y)
  rw [TailEnergyBounds.finalAngular_before_release d eta hy']
  dsimp only [flattened]
  rw [hang]
  dsimp [finiteAmplitudeConstant]
  linarith only [he3]


-- @@ L2163-2185 verbatim
theorem endpointAmplitude_le_pulse (d : TailData) (eta : ℝ) :
    finalAngular d (d.core.endpoint, eta) ≤ pulseAmplitude d.core := by
  have hy : d.core.pulseStart ≤ d.core.endpoint := by
    dsimp [OutgoingSchedule.Parameters.endpoint]
    linarith [d.core.pulseLength_pos]
  have hr := radialAmplitude_hold d.core.dropLength_pos.le d.core.pulseStart_ge_hold hy
    (P := d.core.P) (lam := d.core.lam)
  rw [finalAngular_before d eta le_rfl]
  dsimp [angular]
  rw [hr]
  change pulseAmplitude d.core * Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint -
      d.core.pulseStart)) *
    shape eta ≤ pulseAmplitude d.core
  have he : Real.exp (-(1 / 2 + d.core.lam) * (d.core.endpoint - d.core.pulseStart)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [d.core.lam_pos])
  have hs : shape eta ≤ 1 := by
    dsimp [shape]
    rw [← one_div]
    apply (div_le_one (by positivity)).mpr
    linarith [sq_nonneg eta]
  have hm := mul_le_mul he hs (shape_pos eta).le (by norm_num : (0 : ℝ) ≤ 1)
  have hp := mul_le_mul_of_nonneg_left hm (pulseAmplitude_pos d.core).le
  linarith


-- @@ L2187-2190 verbatim
/-- Finite cone constant, given by `(4 * finiteNumeratorConstant / finiteAmplitudeConstant) * (P
* Real.exp (Real.exp m + 12))`. -/
noncomputable def finiteConeConstant (P m : ℝ) : ℝ :=
  (4 * finiteNumeratorConstant / finiteAmplitudeConstant) * (P * Real.exp (Real.exp m + 12))


-- @@ L2192-2196 verbatim
theorem finiteConeConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < finiteConeConstant P m := by
  dsimp [finiteConeConstant]
  exact mul_pos (div_pos (mul_pos (by
      norm_num) finiteNumeratorConstant_pos) finiteAmplitudeConstant_pos)
    (mul_pos hP (Real.exp_pos _))


-- @@ L2198-2249 verbatim
theorem actual_finite_ratio_bound {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : K * d.core.lam ^ (28 : ℕ) ≤ 1) (eta : ℝ) (heta : |eta| ≤ 1)
    (hz : ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp q) q = 0)
    {y : ℝ} (hy : d.core.endpoint ≤ y) (hy' : y ≤ d.releaseStart)
    (hQ : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta)) :
    |OutgoingHistories.Ns w Amp (y, eta) /
      (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))| ≤
      finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) := by
  have he := corrected_amplitude_finite_lower w eta hy hy'
  have hq : 0 < OutgoingHistories.Qs w Amp (y, eta) := lt_of_lt_of_le (by
      linarith [d.core.lam_pos]) hQ
  have hden := mul_pos (OutgoingHistories.E_pos w (y, eta)) hq
  have hnum := actualNs_finite_bound w ha hsmall eta heta hz hy hy'
  have hbud : finiteNumeratorBudget d ≤ finiteNumeratorConstant / d.core.lam :=
    (le_div_iff₀ d.core.lam_pos).mpr (by linarith [finiteNumeratorBudget_bound d])
  have hend := (endpointAmplitude_le_pulse d eta).trans (OutgoingPulseBounds.pulseAmplitude_small
      d.core hwait)
  have hE := finalAngular_pos d (d.core.endpoint, eta)
  have he0 : 0 < finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18
      : ℕ) :=
    mul_pos (mul_pos finiteAmplitudeConstant_pos hE) (pow_pos d.core.lam_pos _)
  have hdl := mul_le_mul he hQ (by linarith [d.core.lam_pos] : (0 : ℝ) ≤ d.core.lam / 4)
    (OutgoingHistories.E_pos w (y, eta)).le
  have hdl0 : 0 < finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) *
      d.core.lam ^ (18 : ℕ) * (d.core.lam / 4) := mul_pos he0 (by linarith [d.core.lam_pos])
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ (finiteNumeratorConstant / d.core.lam * finalAngular d (d.core.endpoint, eta) ^ 2) /
        (finiteAmplitudeConstant * finalAngular d (d.core.endpoint, eta) * d.core.lam ^ (18 : ℕ) *
            (d.core.lam / 4)) :=
      div_le_div₀ (mul_nonneg (div_nonneg finiteNumeratorConstant_pos.le d.core.lam_pos.le)
          (sq_nonneg _))
        (hnum.trans (mul_le_mul_of_nonneg_right hbud (sq_nonneg _))) hdl0 hdl
    _ = (4 * finiteNumeratorConstant / finiteAmplitudeConstant) *
        (finalAngular d (d.core.endpoint, eta) / d.core.lam ^ (20 : ℕ)) := by
      field_simp [d.core.lam_pos.ne', hE.ne', finiteAmplitudeConstant_pos.ne']
    _ ≤ (4 * finiteNumeratorConstant / finiteAmplitudeConstant) *
        ((d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20
            : ℕ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hend (pow_pos d.core.lam_pos _).le)
        (div_nonneg (mul_nonneg (by
            norm_num) finiteNumeratorConstant_pos.le) finiteAmplitudeConstant_pos.le)
    _ = _ := by
      have hp : d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20 : ℕ) = d.core.lam ^ (10 : ℕ) := by
        field_simp [d.core.lam_pos.ne']
      rw [show (d.core.P * Real.exp (Real.exp d.core.m + 12)) * d.core.lam ^ (30 : ℕ) /
          d.core.lam ^ (20 : ℕ) = (d.core.P * Real.exp (Real.exp d.core.m + 12)) *
            (d.core.lam ^ (30 : ℕ) / d.core.lam ^ (20 : ℕ)) by ring, hp]
      dsimp [finiteConeConstant]
      ring


-- @@ L2251-2251 verbatim
/-! ## Cone quantities of the actual corrected profile -/


-- @@ L2253-2255 verbatim
/-- Actual A, given by `1 - 2 * deriv (fun t => Real.log (OutgoingHistories.E w (t, eta))) y`. -/
noncomputable def actualA {d : TailData} {K : ℝ} (w : ResetWitness d K) (y eta : ℝ) : ℝ :=
  1 - 2 * deriv (fun t => Real.log (OutgoingHistories.E w (t, eta))) y


-- @@ L2257-2261 verbatim
/-- Actual bs, given by `2 * deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y /
OutgoingHistories.E w (y, eta)`. -/
noncomputable def actualBs {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (y eta : ℝ) : ℝ :=
  2 * deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y / OutgoingHistories.E w (y, eta)


-- @@ L2263-2271 verbatim
theorem actualA_finite {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : d.core.endpoint ≤ y) (hy' : y < d.releaseStart) :
    actualA w y eta = 2 - 2 * correctedFlatSlope w eta y := by
  have hd := (correctedFlat_hasDerivAt w eta hy hy').log (OutgoingHistories.E_pos w (y, eta)).ne'
  unfold actualA
  rw [hd.deriv]
  change 1 - 2 * (OutgoingHistories.E w (y, eta) * (correctedFlatSlope w eta y - 1 / 2) /
    OutgoingHistories.E w (y, eta)) = _
  field_simp [(OutgoingHistories.E_pos w (y, eta)).ne']; ring


-- @@ L2273-2275 verbatim
theorem actualA_release {d : TailData} {K : ℝ} (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : d.releaseStart ≤ y) : actualA w y eta = releaseA d y :=
  corrected_releaseA d w.coefficients eta hy


-- @@ L2277-2291 verbatim
theorem actualBs_zero {d : TailData} {K : ℝ} (w : ResetWitness d K)
    {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    actualBs w Amp y eta = 0 := by
  have hf : Differentiable ℝ (fun t => OutgoingHistories.U d Amp (t, eta)) :=
    ((OutgoingHistories.U_smooth d ha).comp (contDiff_id.prodMk contDiff_const)).differentiable (by
        simp)
  have hz : HasDerivWithinAt (fun t => OutgoingHistories.U d Amp (t, eta)) 0 (Ici y) y := by
    apply (hasDerivWithinAt_const y (Ici y) (0 : ℝ)).congr
    · intro t ht
      exact OutgoingHistories.U_after_endpoint d Amp eta (hy.trans ht)
    · exact OutgoingHistories.U_after_endpoint d Amp eta hy
  have hd : deriv (fun t => OutgoingHistories.U d Amp (t, eta)) y = 0 :=
    (uniqueDiffOn_Ici y y (show y ∈ Ici y from le_refl y)).eq_deriv _ (hf
        y).hasDerivAt.hasDerivWithinAt hz
  simp [actualBs, hd]


-- @@ L2293-2302 verbatim
theorem actualP2_eq {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (XR eta y : ℝ) (heta : eta ^ 2 ≤ 1)
    (hQ : 0 < OutgoingHistories.Qs w Amp (y, eta)) :
    OutgoingHistories.p2 XR w Amp (y, eta) = OutgoingHistories.p1 XR w Amp (y, eta) *
      (OutgoingHistories.Ns w Amp (y, eta) /
        (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))) := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  change 0 < 1 - 2 * d.h * eta ^ 2 at hL
  dsimp [OutgoingHistories.p1, OutgoingHistories.p2]
  field_simp [hL.ne', hQ.ne', (OutgoingHistories.E_pos w (y, eta)).ne']


-- @@ L2304-2306 verbatim
/-- Finite radius threshold, given by `16 / (Real.exp d.core.endpoint * (d.core.lam / 4))`. -/
noncomputable def finiteRadiusThreshold (d : TailData) : ℝ :=
  16 / (Real.exp d.core.endpoint * (d.core.lam / 4))


-- @@ L2308-2309 verbatim
theorem finiteRadiusThreshold_pos (d : TailData) : 0 < finiteRadiusThreshold d :=
  div_pos (by norm_num) (mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num)))


-- @@ L2311-2327 verbatim
theorem actualP1_finite_large {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (Amp : ℝ → ℝ) {XR eta y : ℝ} (hXR : finiteRadiusThreshold d < XR) (heta : eta ^ 2 ≤ 1)
    (hy : d.core.endpoint ≤ y) (hQ : d.core.lam / 4 ≤ OutgoingHistories.Qs w Amp (y, eta)) :
    16 < OutgoingHistories.p1 XR w Amp (y, eta) := by
  have hL := CoordinateAlgebra.L_pos d.h_pos.le d.h_lt_half heta
  have hL1 : CoordinateAlgebra.L d.h eta ≤ 1 := by
    dsimp [CoordinateAlgebra.L]
    linarith [mul_nonneg d.h_pos.le (sq_nonneg eta)]
  have hXR0 := (finiteRadiusThreshold_pos d).trans hXR
  have hscale : 16 < XR * (Real.exp d.core.endpoint * (d.core.lam / 4)) :=
    (div_lt_iff₀ (mul_pos (Real.exp_pos _) (div_pos d.core.lam_pos (by norm_num)))).mp hXR
  have hprod := mul_le_mul (Real.exp_le_exp.mpr hy) hQ
    (div_nonneg d.core.lam_pos.le (by norm_num : (0 : ℝ) ≤ 4)) (Real.exp_pos y).le
  have hp := mul_le_mul_of_nonneg_left hprod hXR0.le
  change 16 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h eta
  apply (lt_div_iff₀ hL).mpr
  linarith


-- @@ L2329-2340 verbatim
theorem corrected_amplitude_energy_zero_germ {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (eta : ℝ) (heta : eta ^ 2 ≤ 1) :
    ∀ᶠ q in 𝓝 eta, CorrectedPulseAmplitude.totalEnergy d w.coefficients
      (CorrectedPulseAmplitude.amplitude d w.coefficients q) q = 0 := by
  have h := CorrectedPulseAmplitude.numerical_coefficient_bounds d w.coefficients eta
    (CorrectedPulseAmplitude.combinedScale d K) heta
    (CorrectedPulseAmplitude.old_error_bounds d K hK hsmall hwait eta heta)
    (CorrectedPulseAmplitude.energyShift_bounds w hK eta heta).1 hscale
  apply amplitude_energy_zero_germ w eta
  linarith [h.2.2.2.2]


-- @@ L2342-2347 verbatim
theorem reset_scale_le_one {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hreset : resetSourceError d K ≤ d.core.lam / 4) : K * d.core.lam ^ (28 : ℕ) ≤ 1 := by
  have h0 := ResetEnergyBounds.coefficient_scale_nonneg w
  have hp := mul_nonneg resetJetConstant_pos.le h0
  dsimp [resetSourceError] at hreset
  linarith [d.core.lam_lt]


-- @@ L2349-2351 verbatim
/-- Tail radius threshold, given by `max (finiteRadiusThreshold d) (releaseRadiusThreshold d)`. -/
noncomputable def tailRadiusThreshold (d : TailData) : ℝ :=
  max (finiteRadiusThreshold d) (releaseRadiusThreshold d)


-- @@ L2353-2354 verbatim
theorem tailRadiusThreshold_pos (d : TailData) : 0 < tailRadiusThreshold d :=
  (finiteRadiusThreshold_pos d).trans_le (le_max_left _ _)


-- @@ L2356-2419 verbatim
/-- All quantities are those of the corrected profile and its actual integral
histories. The scalar smallness conditions are arranged by the thresholds below. -/
theorem corrected_tail_cone {d : TailData} {K : ℝ} (w : ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hpulse : PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8)
    (hh1 : d.h ≤ 1 / 100) (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    (hreset : resetSourceError d K ≤ d.core.lam / 4)
    (hfinite : finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) ≤ 1 / 2)
    (hrelease : releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2)
    {XR eta y : ℝ} (hXR : tailRadiusThreshold d < XR) (heta : |eta| ≤ 1)
    (hy : d.core.endpoint ≤ y) (hy' : y ≤ tailStart d + 1 / 2) :
    0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualBs w (CorrectedPulseAmplitude.amplitude d w.coefficients) y eta = 0 ∧
    2 < actualA w y eta ∧ actualA w y eta ≤ 4 ∧
    2 < OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualA w y eta < ConeAlgebra.coneBound
      (OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))
      (OutgoingHistories.p2 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta)) :=
          by
  let Amp := CorrectedPulseAmplitude.amplitude d w.coefficients
  have ha : ContDiff ℝ ∞ Amp := CorrectedPulseAmplitude.amplitude_contDiff d w.smooth
  have heta2 : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).2 heta
  have hz := corrected_amplitude_energy_zero_germ w hK hwait hsmall hscale eta heta2
  have hb := actualBs_zero w ha eta hy
  by_cases hyr : y < d.releaseStart
  · have hQ := corrected_flatten_Qs_lower w hK hwait hsmall hscale hpulse hh1 hhT hreset eta heta
      hy hyr.le
    have hQ0 : 0 < OutgoingHistories.Qs w Amp (y, eta) := by
      change 0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y,
          eta)
      linarith [d.core.lam_pos]
    have har := correctedFlat_geometry w hreset eta y heta2
    have hAw := actualA_finite w eta hy hyr
    have hratio := (actual_finite_ratio_bound w ha hwait (reset_scale_le_one w hreset) eta heta hz
        hy hyr.le hQ).trans hfinite
    have hp := actualP1_finite_large w Amp ((le_max_left _ _).trans_lt hXR) heta2 hy hQ
    have hc := cone_of_zero_bs (a := actualA w y eta) (by rw [hAw]; exact har.1)
      (by rw [hAw]; exact har.2.1) hratio hp
    refine ⟨hQ0, hb, hc.2.1, ?_, hc.1, ?_⟩
    · rw [hAw]; exact har.2.1
    · rw [actualP2_eq w Amp XR eta y heta2 hQ0]
      exact hc.2.2
  · have hR : d.releaseStart ≤ y := le_of_not_gt hyr
    have hQ : 0 < OutgoingHistories.Qs w Amp (y, eta) := by
      rw [actualQs_eq_normalizedLag w ha eta hR]
      exact normalizedLag_pos w eta hR hy'
    have hratio : |OutgoingHistories.Ns w Amp (y, eta) /
        (OutgoingHistories.E w (y, eta) * OutgoingHistories.Qs w Amp (y, eta))| ≤ 1 / 2 := by
      rw [actualRatio_eq_releaseVelocityRatio w ha eta hR hz]
      exact (releaseVelocityRatio_uniform w hwait heta hR hy').trans hrelease
    have hp : 16 < OutgoingHistories.p1 XR w Amp (y, eta) := by
      change 16 < XR * Real.exp y * OutgoingHistories.Qs w Amp (y, eta) / CoordinateAlgebra.L d.h
          eta
      rw [actualQs_eq_normalizedLag w ha eta hR]
      exact releaseP1_large w ((le_max_right _ _).trans_lt hXR) heta2 hR hy'
    have har := releaseA_bounds d y
    have hAw := actualA_release w eta hR
    have hc := cone_of_zero_bs (a := actualA w y eta) (by rw [hAw]; exact har.1)
      (by rw [hAw]; exact har.2) hratio hp
    refine ⟨hQ, hb, hc.2.1, ?_, hc.1, ?_⟩
    · rw [hAw]; exact har.2
    · rw [actualP2_eq w Amp XR eta y heta2 hQ]
      exact hc.2.2


-- @@ L2421-2421 verbatim
/-! ## Simultaneous parameter choice, uniform in the terminal parameter -/


-- @@ L2423-2427 verbatim
theorem lambda_power_le_self (d : TailData) (n : ℕ) : d.core.lam ^ (n + 1) ≤ d.core.lam := by
  have hp := pow_le_one₀ d.core.lam_pos.le (show d.core.lam ≤ 1 by
      linarith [d.core.lam_lt]) (n := n)
  rw [pow_succ]
  nlinarith [d.core.lam_pos]


-- @@ L2429-2439 verbatim
theorem exists_finite_cone_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m →
      d.core.lam < lam0 → finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) < 1 / 2 := by
  have hC := finiteConeConstant_pos hP m
  refine ⟨(1 / 2) / finiteConeConstant P m, div_pos (by norm_num) hC, ?_⟩
  intro d hdP hdm hlam
  rw [hdP, hdm]
  have hpow : d.core.lam ^ (10 : ℕ) ≤ d.core.lam := lambda_power_le_self d 9
  have hsmall := (lt_div_iff₀ hC).mp hlam
  have hp := mul_le_mul_of_nonneg_left hpow hC.le
  linarith


-- @@ L2441-2456 verbatim
theorem exists_reset_source_threshold (K : ℝ) (hK : 0 < K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 →
      resetSourceError d K ≤ d.core.lam / 4 := by
  let C : ℝ := (2 * resetJetConstant + 2) * K
  have hC : 0 < C := mul_pos (by linarith [resetJetConstant_pos]) hK
  refine ⟨(1 / 4) / C, div_pos (by norm_num) hC, ?_⟩
  intro d hlam
  have hpow : d.core.lam ^ (27 : ℕ) ≤ d.core.lam := lambda_power_le_self d 26
  have hc := (lt_div_iff₀ hC).mp hlam
  have hp := mul_le_mul_of_nonneg_left hpow hC.le
  have hb : C * d.core.lam ^ (27 : ℕ) ≤ 1 / 4 := by linarith
  calc
    resetSourceError d K = d.core.lam * (C * d.core.lam ^ (27 : ℕ)) := by
      dsimp [resetSourceError, C]; ring
    _ ≤ d.core.lam * (1 / 4) := mul_le_mul_of_nonneg_left hb d.core.lam_pos.le
    _ = _ := by ring


-- @@ L2458-2503 verbatim
theorem exists_tail_smallness_threshold (P m K : ℝ) (hP : 0 < P) (hK : 0 < K) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.P = P → d.core.m = m → d.core.lam < lam0 →
      d.core.lam ≤ 1 / 120 ∧ CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000 ∧
      PulseCone.sourceConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 8 ∧
      d.h ≤ 1 / 100 ∧ d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8 ∧
      resetSourceError d K ≤ d.core.lam / 4 ∧
      finiteConeConstant d.core.P d.core.m * d.core.lam ^ (10 : ℕ) ≤ 1 / 2 ∧
      releaseConeConstant d.core.P d.core.m * d.core.lam ^ (29 : ℕ) ≤ 1 / 2 := by
  obtain ⟨rate, hrate, Hrate⟩ := PulseAmplitude.exists_rate_threshold
      (CorrectedPulseAmplitude.combinedConstant P m K)
  obtain ⟨finite, hfinite, Hfinite⟩ := exists_finite_cone_threshold P m hP
  obtain ⟨release, hrelease, Hrelease⟩ := exists_release_cone_threshold P m hP
  obtain ⟨reset, hreset, Hreset⟩ := exists_reset_source_threshold K hK
  let source : ℝ := (1 / 8) / PulseCone.sourceConstant P m
  let incoming : ℝ := Real.exp (-(Real.exp m + 12 + 3 / 5)) / 4
  have hsource : 0 < source := div_pos (by norm_num) (PulseCone.sourceConstant_pos hP m)
  have hincoming : 0 < incoming := div_pos (Real.exp_pos _) (by norm_num)
  refine ⟨min rate (min finite (min release (min reset (min source (min (1 / 120) incoming))))),
    lt_min hrate (lt_min hfinite (lt_min hrelease (lt_min hreset (lt_min hsource (lt_min (by
        norm_num) hincoming))))), ?_⟩
  intro d hdP hdm hlam
  rcases lt_min_iff.mp hlam with ⟨hlrate, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlfinite, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlrelease, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlreset, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlsource, hlam⟩
  rcases lt_min_iff.mp hlam with ⟨hlnum, hlincoming⟩
  refine ⟨hlnum.le, ?_, ?_, ?_, ?_, Hreset d hlreset, (Hfinite d hdP hdm hlfinite).le,
    (Hrelease d hdP hdm hlrelease).le⟩
  · unfold CorrectedPulseAmplitude.combinedScale
    rw [hdP, hdm]
    exact Hrate _ d.core.lam_pos hlrate
  · rw [hdP, hdm]
    have hs : d.core.lam * PulseCone.sourceConstant P m < 1 / 8 :=
      (lt_div_iff₀ (PulseCone.sourceConstant_pos hP m)).mp hlsource
    have hp : d.core.lam ^ (29 : ℕ) ≤ d.core.lam := lambda_power_le_self d 28
    have hm := mul_le_mul_of_nonneg_left hp (PulseCone.sourceConstant_pos hP m).le
    linarith
  · linarith [d.h_small]
  · have hhold : d.core.holdStart = Real.exp m + 12 := by
      dsimp [OutgoingSchedule.Parameters.holdStart, OutgoingSchedule.Parameters.dropLength]
      rw [hdm]
      ring
    rw [hhold]
    dsimp [incoming] at hlincoming
    linarith [d.h_small]


-- @@ L2505-2514 verbatim
/-- The post-pulse pointwise cone for the exact corrected schedule. -/
noncomputable def PostPulseCone {d : TailData} {K : ℝ} (w : ResetWitness d K) (XR : ℝ) : Prop :=
  ∀ eta : ℝ, |eta| ≤ 1 → ∀ y : ℝ, d.core.endpoint ≤ y → y ≤ tailStart d + 1 / 2 →
    0 < OutgoingHistories.Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualBs w (CorrectedPulseAmplitude.amplitude d w.coefficients) y eta = 0 ∧
    2 < actualA w y eta ∧ actualA w y eta ≤ 4 ∧
    2 < OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta) ∧
    actualA w y eta < ConeAlgebra.coneBound
      (OutgoingHistories.p1 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))
      (OutgoingHistories.p2 XR w (CorrectedPulseAmplitude.amplitude d w.coefficients) (y, eta))


-- @@ L2516-2541 verbatim
/-- A common positive `lam` threshold works for every `0 < 2*h < lam`.
The entrance radius is chosen only after the full schedule, including `h`.
No energy, pressure, angular-lag, or cone inequality is assumed as input. -/
theorem exists_scheduled_tail_cone (P m : ℝ) (hP : 0 < P) :
    ∃ lam0 K : ℝ, 0 < lam0 ∧ 0 < K ∧ ∀ d : TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam0 → ∃ w : ResetWitness d K,
        ContDiff ℝ ∞ (CorrectedPulseAmplitude.amplitude d w.coefficients) ∧
        (∀ eta : ℝ, eta ^ 2 ≤ 1 → CorrectedPulseAmplitude.totalEnergy d w.coefficients
          (CorrectedPulseAmplitude.amplitude d w.coefficients eta) eta = 0) ∧
        ∃ R0 : ℝ, 0 < R0 ∧ ∀ XR : ℝ, R0 < XR → PostPulseCone w XR := by
  obtain ⟨resetLam, K, hresetLam, hK, Hreset⟩ := exists_scheduled_reset
  obtain ⟨smallLam, hsmallLam, Hsmall⟩ := exists_tail_smallness_threshold P m K hP hK
  refine ⟨min resetLam smallLam, K, lt_min hresetLam hsmallLam, hK, ?_⟩
  intro d hdP hdm hwait hlam
  have hr := lt_of_lt_of_le hlam (min_le_left _ _)
  have hs := lt_of_lt_of_le hlam (min_le_right _ _)
  obtain ⟨w⟩ := Hreset d hr
  obtain ⟨hsmall, hscale, hpulse, hh1, hhT, hreset, hfinite, hrelease⟩ := Hsmall d hdP hdm hs
  have ha := CorrectedPulseAmplitude.amplitude_spec w hK hsmall hwait hscale
  refine ⟨w, ha.1, ?_, tailRadiusThreshold d, tailRadiusThreshold_pos d, ?_⟩
  · intro eta heta
    exact (ha.2 eta heta).2.2.1
  · intro XR hXR eta heta y hy hy'
    exact corrected_tail_cone w hK hwait hsmall hscale hpulse hh1 hhT hreset hfinite hrelease hXR
        heta hy hy'


-- @@ L2543-2543 verbatim
end NavierStokes.TailCone
