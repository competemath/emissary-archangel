/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionStabilityBudget
import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionUniqueness
import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction


-- @@ L13-13 verbatim
/-! Actual inviscid corrections agree across compatible Sobolev levels. -/


-- @@ L15-15 verbatim
section


-- @@ L17-17 verbatim
/-! Actual inviscid corrections agree across compatible Sobolev levels. -/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerInviscidCorrectionRestriction


-- @@ L25-28 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerQuadraticSource EulerVolterraConvolution


-- @@ L30-30 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L32-54 verbatim
/-- The literal inviscid equation is preserved by lowering the actual Sobolev order. -/
theorem inviscid_equation_restrict {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period (by omega : 6 ≤ q + 1)).apply
          ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩))) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT
      ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u) r))
      (value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
        ⟨t,ht.1.le,ht.2.le⟩ (truncateOperator period (q+1) (u ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  have hs := congrArg (value period (q := q))
    (truncate_source period hq D KG KL KQ hG hL hQ ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩))
  rw [value_truncateOperator] at hs
  exact (hu t ht).congr_deriv hs


-- @@ L56-56 verbatim
end EulerInviscidCorrectionRestriction


-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
@[expose] public section


-- @@ L65-65 verbatim
noncomputable section


-- @@ L67-67 verbatim
namespace EulerInviscidCorrectionCompatibility


-- @@ L69-73 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
   EulerQuadraticSource EulerVolterraConvolution
  EulerCorrectionStabilityBudget EulerInviscidCorrectionUniqueness


-- @@ L75-75 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L77-110 verbatim
/-- Actual inviscid corrections constructed at neighboring Sobolev orders coincide after
restriction. -/
theorem inviscid_corrections_compatible {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period (by omega : 6 ≤ q + 1)).apply
          ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩))) t)
    (B : StabilityBudget period hT (lowerData period D KG KL KQ hG hL hQ))
    (v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
          ⟨t, ht.1.le, ht.2.le⟩ (v ⟨t, ht.1.le, ht.2.le⟩))) t)
    (hi : truncateOperator period (q + 1) (u ⟨0, le_rfl, hT⟩) = v ⟨0, le_rfl, hT⟩)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction) :
    (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u = v := by
  let w := (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  apply inviscid_correction_unique period hq T hT (lowerData period D KG KL KQ hG hL hQ) B w v hi
  · exact EulerInviscidCorrectionRestriction.inviscid_equation_restrict period hq T hT D KG KL KQ
      hG hL hQ u hu
  · exact hv
  · exact hz
  · exact hud
  · exact hvd


-- @@ L112-112 verbatim
end EulerInviscidCorrectionCompatibility
