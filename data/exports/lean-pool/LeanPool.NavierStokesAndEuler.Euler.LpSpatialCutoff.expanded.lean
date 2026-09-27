/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.NoncompactTransport
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit

import Mathlib.Analysis.Calculus.FDeriv.Mul


-- @@ L14-14 verbatim
/-! Expanding ordinary-space cutoffs and their actual first derivative controls. -/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
attribute [local instance] FiniteDimensional.hasContDiffBump



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerLpTranslation


-- @@ L25-25 verbatim
open MeasureTheory EulerSmoothLimit EulerNoncompactTransport Filter

-- @@ L26-26 verbatim
open scoped ContDiff Topology


-- @@ L28-29 verbatim
/-- Cutoff, given by `spatialBump (cutoffScale n • x)`. -/
def cutoff (n : ℕ) (x : Space) : ℝ := spatialBump (cutoffScale n • x)


-- @@ L31-32 verbatim
theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  spatialBump.contDiff.comp (contDiff_id.const_smul (cutoffScale n))


-- @@ L34-35 verbatim
theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) :=
  spatialBump.hasCompactSupport.comp_smul (cutoffScale_pos n).ne'


-- @@ L37-38 verbatim
theorem cutoff_bounds (n : ℕ) (x : Space) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨spatialBump.nonneg, spatialBump.le_one⟩


-- @@ L40-42 verbatim
theorem cutoff_sub_one_norm (n : ℕ) (x : Space) : ‖cutoff n x - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cutoff_bounds n x]


-- @@ L44-47 verbatim
theorem cutoff_tendsto (x : Space) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have h := spatialBump.continuous.continuousAt.tendsto.comp (cutoffScale_tendsto.smul_const x)
  have hb : spatialBump (0 : Space) = 1 := spatialBump.one_of_mem_closedBall (by simp [spatialBump])
  simpa only [cutoff, zero_smul, hb, Function.comp_def] using h


-- @@ L49-69 verbatim
theorem cutoff_derivative_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ n x, ‖fderiv ℝ (cutoff n) x‖ ≤ M * cutoffScale n := by
  have hs : ContDiff ℝ ∞ (spatialBump : Space → ℝ) := spatialBump.contDiff
  obtain ⟨M, hM⟩ := (spatialBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hs.fderiv_right (m := ∞) (by simp)).continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, ?_⟩
  intro n x
  have hder := ((hs.differentiable (by simp)) (cutoffScale n • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (cutoffScale n))
  change HasFDerivAt (cutoff n)
    ((fderiv ℝ (spatialBump : Space → ℝ) (cutoffScale n • x)).comp
      (cutoffScale n • ContinuousLinearMap.id ℝ Space)) x at hder
  rw [hder.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (spatialBump : Space → ℝ) (cutoffScale n • x)‖ *
        ‖cutoffScale n • ContinuousLinearMap.id ℝ Space‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (spatialBump : Space → ℝ) (cutoffScale n • x)‖ * cutoffScale n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n), ContinuousLinearMap.norm_id,
          mul_one]
    _ ≤ M * cutoffScale n := mul_le_mul_of_nonneg_right (hM _) (cutoffScale_pos n).le


-- @@ L71-75 verbatim
theorem cutoff_derivative_tendsto (x : Space) :
    Tendsto (fun n => fderiv ℝ (cutoff n) x) atTop (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := cutoff_derivative_bound
  apply squeeze_zero_norm (fun n => hM n x)
  simpa only [mul_zero] using cutoffScale_tendsto.const_mul M


-- @@ L77-77 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L79-80 verbatim
/-- Cutoff field, given by `cutoff n x • f x`. -/
def cutoffField (f : Space → V) (n : ℕ) (x : Space) : V := cutoff n x • f x


-- @@ L82-83 verbatim
theorem cutoffField_smooth (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (cutoffField f n) := (cutoff_smooth n).smul hf


-- @@ L85-86 verbatim
theorem cutoffField_compact (f : Space → V) (n : ℕ) : HasCompactSupport (cutoffField f n) :=
  (cutoff_compact n).smul_right


-- @@ L88-91 verbatim
theorem cutoffField_fderiv (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : Space) :
    fderiv ℝ (cutoffField f n) x = cutoff n x • fderiv ℝ f x +
      (fderiv ℝ (cutoff n) x).smulRight (f x) :=
  fderiv_fun_smul ((cutoff_smooth n).differentiable (by simp) x) (hf.differentiable (by simp) x)


-- @@ L93-95 verbatim
theorem cutoffField_tendsto (f : Space → V) (x : Space) :
    Tendsto (fun n => cutoffField f n x) atTop (𝓝 (f x)) := by
  simpa only [one_smul, cutoffField] using (cutoff_tendsto x).smul_const (f x)


-- @@ L97-105 verbatim
theorem cutoffField_fderiv_tendsto (f : Space → V) (hf : ContDiff ℝ ∞ f) (x : Space) :
    Tendsto (fun n => fderiv ℝ (cutoffField f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  have hright : Tendsto (fun n => (fderiv ℝ (cutoff n) x).smulRight (f x)) atTop (𝓝 0) := by
    have hc : Continuous (fun L : Space →L[ℝ] ℝ => L.smulRight (f x)) := by fun_prop
    simpa only [ContinuousLinearMap.zero_smulRight, Function.comp_def] using
        hc.continuousAt.tendsto.comp
      (cutoff_derivative_tendsto x)
  simp_rw [cutoffField_fderiv f hf]
  simpa only [one_smul, add_zero] using ((cutoff_tendsto x).smul_const (fderiv ℝ f x)).add hright


-- @@ L107-107 verbatim
end EulerLpTranslation
