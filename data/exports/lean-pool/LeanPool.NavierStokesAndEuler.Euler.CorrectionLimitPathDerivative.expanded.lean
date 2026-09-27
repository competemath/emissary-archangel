/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticSourceLimit
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityCauchy
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction
import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge


-- @@ L15-15 verbatim
/-! The actual viscous derivative expressed using the identical lower-order nonlinear source. -/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
/-! The actual viscous derivative expressed using the identical lower-order nonlinear source. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerCorrectionLimitDerivative


-- @@ L27-32 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerQuadraticSource
    EulerVolterraConvolution EulerMildEquationBridge
      EulerSobolevHeatGenerator

-- @@ L33-33 verbatim
open scoped Topology


-- @@ L35-35 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L37-39 verbatim
/-- The inherited normed group on each actual Sobolev value space. -/
local instance limitDerivativeGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
    inferInstance


-- @@ L41-42 verbatim
/-- The inherited real normed space on each actual Sobolev value space. -/
local instance limitDerivativeSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance


-- @@ L44-70 verbatim
/-- The actual derivative of a high-order mild correction equals viscosity plus the literal
lower-order nonlinear source. -/
theorem lower_mild_value_derivative {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (ν : ℝ) (hν : 0 < ν) (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl
      (D.coefficients period (by omega : 6 ≤ q + 1)) 0 u t)
    (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period ((q+1)+1) (by omega) (u ⟨r,hr.1.le,hr.2.le⟩) +
        value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
          ⟨r,hr.1.le,hr.2.le⟩ (truncateOperator period (q+1) (u ⟨r,hr.1.le,hr.2.le⟩)))) r := by
  let τ : Icc (0 : ℝ) T := ⟨r,hr.1.le,hr.2.le⟩
  have hx := viscous_mild_hasDerivAt period (by omega : 2 ≤ q+1) ν hν T hT 0
    (D.coefficients period (by omega : 6 ≤ q+1)).apply
    (D.coefficients period (by omega : 6 ≤ q+1)).continuous u hsol r hr
  have hs := congrArg (value period (q := q)) (truncate_source period hq D KG KL KQ hG hL hQ τ (u
      τ))
  rw [value_truncateOperator] at hs
  apply hx.congr_deriv
  exact congrArg (fun v => ν • laplacianEvaluation period ((q+1)+1) (by omega) (u τ)+v) hs


-- @@ L72-72 verbatim
end EulerCorrectionLimitDerivative


-- @@ L74-74 verbatim
end

-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
section


-- @@ L81-81 verbatim
/-! A pointwise viscous derivative expressed as a continuous path. -/


-- @@ L83-83 verbatim
@[expose] public section


-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
namespace EulerViscousPathDerivative


-- @@ L89-90 verbatim
open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution


-- @@ L92-92 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L94-107 verbatim
/-- The actual pointwise viscous derivative equals evaluation of its continuous source path. -/
theorem hasDerivAt_path {s q : ℕ} (hs : 2 ≤ s) (ν T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (r : ℝ) (hr : r ∈ Ioo 0 T)
    (hd : HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period s hs (u ⟨r, hr.1.le, hr.2.le⟩) +
        value period (f ⟨r, hr.1.le, hr.2.le⟩)) r) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period hs ν T u + valuePath period T f) r) r := by
  apply hd.congr_deriv
  change _ = (viscousDefect period hs ν T u + valuePath period T f) (projIcc 0 T hT r)
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  rfl


-- @@ L109-109 verbatim
end EulerViscousPathDerivative


-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
end


-- @@ L116-116 verbatim
@[expose] public section


-- @@ L118-118 verbatim
noncomputable section


-- @@ L120-120 verbatim
namespace EulerCorrectionLimitPathDerivative


-- @@ L122-127 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
   EulerQuadraticSource EulerQuadraticSourceLimit
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution
      EulerSobolevHeatGenerator

-- @@ L128-128 verbatim
open scoped Topology


-- @@ L130-130 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L132-134 verbatim
/-- The inherited normed group on each actual Sobolev value space. -/
local instance limitDerivativeGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
    inferInstance


-- @@ L136-137 verbatim
/-- The inherited real normed space on each actual Sobolev value space. -/
local instance limitDerivativeSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance


-- @@ L139-162 verbatim
/-- The actual derivative of a high-order mild correction equals viscosity plus the literal
lower-order nonlinear source. -/
theorem lower_mild_path_derivative {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (ν : ℝ) (hν : 0 < ν) (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl
      (D.coefficients period (by omega : 6 ≤ q + 1)) 0 u t)
    (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period (by omega : 2 ≤ (q+1)+1) ν T u +
        valuePath period T (sourcePath ((lowerData period D KG KL KQ hG hL hQ).coefficients period
            hq)
          ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u))) r) r := by
  exact EulerViscousPathDerivative.hasDerivAt_path period (by omega : 2 ≤ (q+1)+1) ν T hT u
    (sourcePath ((lowerData period D KG KL KQ hG hL hQ).coefficients period hq)
      ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)) r hr
    (EulerCorrectionLimitDerivative.lower_mild_value_derivative period hq T hT D KG KL KQ hG hL hQ
        ν hν u hsol r hr)


-- @@ L164-164 verbatim
end EulerCorrectionLimitPathDerivative
