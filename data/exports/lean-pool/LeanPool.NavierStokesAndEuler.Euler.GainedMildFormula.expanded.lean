/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DuhamelDifferentiation
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatVolterra
import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge


-- @@ L13-13 verbatim
/-! Equivalence between genuine gained-derivative and ordinary heat-Duhamel solution formulas. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerGainedMildFormula


-- @@ L22-23 verbatim
open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerDuhamelDifferentiation EulerMildEquationBridge

-- @@ L24-24 verbatim
open scoped Topology


-- @@ L26-26 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L28-32 verbatim
/-- Forgetting a top derivative is injective on the actual compatible Sobolev arrays. -/
theorem truncate_injective (q : ℕ) : Function.Injective (truncateOperator period q) := by
  intro u v h
  apply value_injective period
  exact congrArg (value period (q := q)) h


-- @@ L34-42 verbatim
/-- The genuine heat-plus-gained-Duhamel construction as an actual continuous Sobolev path. -/
def mildPath (q : ℕ) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    C(Icc (0 : ℝ) T, SobolevSpace period (q+1)) :=
  freeHeatPath period (q+1) ν T u₀ +
    convolution T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
      (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
      (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
      (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f


-- @@ L44-54 verbatim
/-- The actual gained mild path has the original singular-kernel integral formula. -/
theorem mildPath_apply (q : ℕ) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (t : Icc (0 : ℝ) T) :
    mildPath period q ν hν T hT u₀ f t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)) := by
  change heatOperator period (q+1) (2*ν*t.val).toNNReal u₀+_ = _
  rw [convolution_eq_interval T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t]


-- @@ L56-65 verbatim
/-- The lower Sobolev restriction of the genuine gained path is precisely ordinary Duhamel
evolution. -/
theorem mildPath_truncate (q : ℕ) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (t : Icc (0 : ℝ) T) :
    truncateOperator period q (mildPath period q ν hν T hT u₀ f t) =
      heatFlow period q ν t.val (truncateOperator period q u₀)+duhamel period ν T hT f t.val := by
  change truncateOperator period q (heatOperator period (q+1) (2*ν*t.val).toNNReal u₀+_) = _
  rw [map_add,truncate_heatOperator,truncate_heatConvolution]
  rfl


-- @@ L67-85 verbatim
/-- The actual complete high-order path satisfies the singular mild formula exactly when its
restriction satisfies ordinary Duhamel. -/
theorem gained_mild_iff (q : ℕ) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (∀ t : Icc (0 : ℝ) T, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) ↔
    (∀ t : Icc (0 : ℝ) T, truncateOperator period q (u t) =
      heatFlow period q ν t.val (truncateOperator period q u₀)+duhamel period ν T hT f t.val) := by
  constructor
  · intro h t
    have he : u t = mildPath period q ν hν T hT u₀ f t :=
      (h t).trans (mildPath_apply period q ν hν T hT u₀ f t).symm
    exact (congrArg (truncateOperator period q) he).trans (mildPath_truncate period q ν hν T hT u₀
        f t)
  · intro h t
    have he : u t = mildPath period q ν hν T hT u₀ f t :=
      truncate_injective period q ((h t).trans (mildPath_truncate period q ν hν T hT u₀ f t).symm)
    exact he.trans (mildPath_apply period q ν hν T hT u₀ f t)


-- @@ L87-87 verbatim
end EulerGainedMildFormula
