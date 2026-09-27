/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction


-- @@ L11-11 verbatim
/-! Genuine norm, trace, and divergence constraints persist under actual uniform Sobolev limits. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerSobolevPathLimits


-- @@ L20-20 verbatim
open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace

-- @@ L21-21 verbatim
open scoped Topology


-- @@ L23-23 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L25-26 verbatim
/-- The inherited normed group on the actual Sobolev path values. -/
local instance pathLimitGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance


-- @@ L28-29 verbatim
/-- The inherited real normed space on the actual Sobolev path values. -/
local instance pathLimitSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance


-- @@ L31-37 verbatim
/-- Actual Sobolev restriction is contractive for the uniform time-path norm. -/
theorem restrict_path_norm {s q : ℕ} (hq : q ≤ s) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s)) :
    ‖(restrictOperator period hq).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (restrictOperator_bound period hq (u t)).trans (u.norm_coe_le_norm t)


-- @@ L39-45 verbatim
/-- Uniform state bounds persist at the actual strong Sobolev limit. -/
theorem limit_norm_bound {q : ℕ} (T R : ℝ)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period q)) (v : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (h : Filter.Tendsto u Filter.atTop (𝓝 v)) (hu : ∀ n, ‖u n‖ ≤ R) : ‖v‖ ≤ R := by
  have hh : Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (𝓝 ‖v‖) :=
    (continuous_norm.tendsto v).comp h
  exact le_of_tendsto hh (Filter.Eventually.of_forall hu)


-- @@ L47-54 verbatim
/-- A fixed zero trace is preserved by actual uniform Sobolev convergence. -/
theorem limit_zero_trace {q : ℕ} (T : ℝ) (t : Icc (0 : ℝ) T)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period q)) (v : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (h : Filter.Tendsto u Filter.atTop (𝓝 v)) (hu : ∀ n, u n t = 0) : v t = 0 := by
  have hv := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto v).comp h
  have hz : Filter.Tendsto (fun n => u n t) Filter.atTop (𝓝 (0 : SobolevSpace period q)) :=
    tendsto_const_nhds.congr (fun n => (hu n).symm)
  exact tendsto_nhds_unique hv hz


-- @@ L56-65 verbatim
/-- The genuine lifted divergence constraint is closed under actual uniform Sobolev convergence. -/
theorem limit_divergenceFree {q : ℕ} (T : ℝ) (κ : ℝ) (m : Vector3)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period q)) (v : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (h : Filter.Tendsto u Filter.atTop (𝓝 v))
    (hu : ∀ n t, value period (u n t) ∈ divergenceFreeSpace period κ m) (t : Icc (0 : ℝ) T) :
    value period (v t) ∈ divergenceFreeSpace period κ m := by
  have hv := (valueOperator period q).continuous.tendsto (v t) |>.comp
    (((ContinuousMap.evalCLM ℝ t).continuous.tendsto v).comp h)
  exact (Submodule.isClosed_orthogonal (gradientSpace period κ m)).mem_of_tendsto hv
    (Filter.Eventually.of_forall (fun n => hu n t))


-- @@ L67-67 verbatim
end EulerSobolevPathLimits
