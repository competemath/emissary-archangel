/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel
import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatVolterra
import LeanPool.NavierStokesAndEuler.Euler.VolterraUniqueness


-- @@ L14-14 verbatim
/-! Positive-time existence for the actual projected quadratic cylinder correction equation. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerQuadraticSource


-- @@ L23-23 verbatim
open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat

-- @@ L24-24 verbatim
open scoped Topology


-- @@ L26-29 verbatim
/-- Inclusion of a shorter initial time interval into a prescribed positive interval. -/
def timeInclusion {T S : ℝ} (hTS : T ≤ S) : C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨t.val, t.property.1, t.property.2.trans hTS⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _


-- @@ L31-31 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L33-35 verbatim
/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

-- @@ L36-38 verbatim
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance


-- @@ L40-47 verbatim
/-- The genuine heat Duhamel expression for continuous projected quadratic coefficients. -/
def quadraticDuhamel {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (u₀ : SobolevSpace period (q + 1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (t : Icc (0 : ℝ) T) : SobolevSpace period (q+1) :=
  heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
    ∫ τ in (0 : ℝ)..t.val, heatKernel period q ν hν τ
      (C.apply (timeInclusion hTS (projIcc 0 T hT (t.val-τ))) (u (projIcc 0 T hT (t.val-τ))))


-- @@ L49-80 verbatim
/-- Continuous actual linear and quadratic coefficients yield a mild solution on a strictly positive
time interval. -/
theorem exists_local_quadratic_mild (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (u₀ : SobolevSpace period (q + 1))
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
        ‖u‖ ≤ ‖u₀‖+1 ∧ u ⟨0, le_rfl, hT.le⟩ = u₀ ∧
        ∀ t, u t = quadraticDuhamel period ν hν hT.le hTS C u₀ u t := by
  let R := ‖u₀‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨T, hT, hTS, hb, hs⟩ := exists_positive_time_budget ν (C.ballBound R) (C.ballLipschitz R)
      1 S (by
      norm_num) hS
  let F := (C.comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hFM (t : Icc (0 : ℝ) T) (u : SobolevSpace period (q+1)) (hu : ‖u‖ ≤ R) : ‖F t u‖ ≤
      C.ballBound R :=
    C.apply_bound R hR (timeInclusion hTS t) u hu
  have hFL (t : Icc (0 : ℝ) T) (u v : SobolevSpace period (q+1)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
      ‖F t u-F t v‖ ≤ C.ballLipschitz R*‖u-v‖ :=
    C.apply_sub_bound R hR (timeInclusion hTS t) u v hu hv
  have hbudget : ‖u₀‖+(T+2*parabolicConstant ν*Real.sqrt T)*C.ballBound R ≤ R := add_le_add
      (le_refl ‖u₀‖) hb.le
  obtain ⟨u, hu, hsol⟩ := exists_viscous_mild_solution period q ν hν T hT.le u₀ F hF R
    (C.ballBound R) (C.ballLipschitz R) hR (C.ballBound_nonneg R hR) (C.ballLipschitz_nonneg R hR)
    hFM hFL hbudget hs
  refine ⟨T, hT, hTS, u, hu, ?_, hsol⟩
  have hzero := hsol ⟨0, le_rfl, hT.le⟩
  simpa only [mul_zero, Real.toNNReal_zero, heatOperator_zero, intervalIntegral.integral_same,
      add_zero] using hzero


-- @@ L82-82 verbatim
end EulerQuadraticSource
