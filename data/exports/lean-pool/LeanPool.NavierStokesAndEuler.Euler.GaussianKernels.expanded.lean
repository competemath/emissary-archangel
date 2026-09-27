/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Real


-- @@ L14-15 verbatim
/-! Explicit Gaussian kernels used by the heat operators. The probability theory needed to
establish their mass stays in the proofs, while the kernel formulas remain transparent. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerGaussianCylinderHeat


-- @@ L23-23 verbatim
open MeasureTheory

-- @@ L24-24 verbatim
open scoped NNReal


-- @@ L26-28 verbatim
/-- The real Gaussian density with mean `μ` and variance `v`. -/
def gaussianDensity (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))


-- @@ L30-33 verbatim
/-- The Gaussian measure, with a point mass when its variance is zero. -/
def gaussianMeasure (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity
    (fun x => ENNReal.ofReal (gaussianDensity μ v x))


-- @@ L35-36 verbatim
private theorem gaussianDensity_eq (μ : ℝ) (v : ℝ≥0) :
    gaussianDensity μ v = ProbabilityTheory.gaussianPDFReal μ v := rfl


-- @@ L38-39 verbatim
private theorem gaussianMeasure_eq (μ : ℝ) (v : ℝ≥0) :
    gaussianMeasure μ v = ProbabilityTheory.gaussianReal μ v := rfl


-- @@ L41-43 verbatim
instance (μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianMeasure μ v) := by
  rw [gaussianMeasure_eq]
  infer_instance


-- @@ L45-46 verbatim
@[simp] theorem gaussianMeasure_zero_var (μ : ℝ) : gaussianMeasure μ 0 = Measure.dirac μ :=
  ite_eq_left rfl


-- @@ L48-48 verbatim
end EulerGaussianCylinderHeat
