/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerGuards
import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSign
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraphGevrey
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffDifferenceBound
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialCutoffs
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowParity
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressureParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetParity
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldParityAlgebra
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteParity
import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressureBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import Mathlib.Analysis.Calculus.FDeriv.Add
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedPointwise
import LeanPool.NavierStokesAndEuler.Euler.CylinderClassicalSolenoidal
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderTerminalAmplitude
public import LeanPool.NavierStokesAndEuler.Euler.MeanCylinderSolenoidal
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftBudget
public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
import LeanPool.NavierStokesAndEuler.Euler.GevreyUniformConstants


-- @@ L73-75 verbatim
/-! The initial induction state is completely constructed from the
compact β-family. A single positive time and a single label constant
work for the family, with actual low-order guards and pressure sign. -/


-- @@ L77-77 verbatim
section


-- @@ L79-81 verbatim
/-! Actual constant coefficient towers for the ordinary Euler correction
equation: identity pressure metric, zero lower-order coefficients, spatial
scale one and angular direction zero. No solution is included in the data. -/


-- @@ L83-83 verbatim
@[expose] public section


-- @@ L85-85 verbatim
noncomputable section


-- @@ L87-87 verbatim
namespace EulerConstantCorrection


-- @@ L89-94 verbatim
open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerAllOrderCorrectionData EulerCorrectionEnergyData EulerJetProductBounds
  EulerH6Pressure EulerSobolevGevreyOperators EulerMetricTransport
  EulerTransportDerivatives EulerGevreyUniformConstants
  EulerVolterraConvolution

-- @@ L95-95 verbatim
open scoped ContDiff


-- @@ L97-97 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L99-101 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instConstantCorrectionData1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance

-- @@ L102-104 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instConstantCorrectionData2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L105-108 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →L[ℝ] Space →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instConstantCorrectionData3 : NormedAddCommGroup (LiftTangent →L[ℝ] Space →L[ℝ]
    Space) := inferInstance

-- @@ L109-112 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →L[ℝ] Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instConstantCorrectionData4 : NormedSpace ℝ (LiftTangent →L[ℝ] Space →L[ℝ] Space) :=
    inferInstance

-- @@ L113-117 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →L[ℝ] LiftTangent →L[ℝ] Space →L[ℝ]
Space)` instance to shorten typeclass synthesis. -/
local instance instConstantCorrectionData5 : NormedAddCommGroup (LiftTangent →L[ℝ] LiftTangent
    →L[ℝ] Space →L[ℝ] Space)
    := inferInstance

-- @@ L118-122 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →L[ℝ] LiftTangent →L[ℝ] Space →L[ℝ] Space)`
instance to shorten typeclass synthesis. -/
local instance instConstantCorrectionData6 : NormedSpace ℝ (LiftTangent →L[ℝ] LiftTangent →L[ℝ]
    Space →L[ℝ] Space) :=
    inferInstance


-- @@ L124-138 verbatim
/-- Coefficient, bundling `coefficient`, `smooth`, `bound`, `norm_bound` and the required
compatibility proofs. -/
def coefficient (A : Space →L[ℝ] Space) : SmoothCoefficient P where
  coefficient _ := A
  smooth _ := contDiff_const
  bound := ‖A‖₊
  norm_bound _ := le_rfl
  firstBound := 0
  norm_first _ := by
    change ‖fderiv ℝ (fun _ : LiftTangent => A) 0‖ ≤ 0
    simp only [fderiv_const_apply,norm_zero,le_refl]
  secondBound := 0
  norm_second _ y := by
    change ‖fderiv ℝ (fderiv ℝ (fun _ : LiftTangent => A)) y‖ ≤ 0
    simp only [fderiv_fun_const,fderiv_zero,Pi.zero_apply,norm_zero,le_refl]


-- @@ L140-147 verbatim
/-- Jet used in constant correction data. -/
def jet (A : Space →L[ℝ] Space) :
    (q : ℕ) → EulerSpatialSobolevInverse.CoefficientJet P standardDirection q (coefficient P A)
  | 0 => .zero _
  | q+1 => .succ (fun _ => coefficient P 0) (fun _ => jet 0 q)
      (fun i _ => by
        change (0 : Space →L[ℝ] Space)=(fderiv ℝ (fun _ : LiftTangent => A) 0) (standardDirection i)
        simp)


-- @@ L149-160 verbatim
omit [Fact (0 < P)] in
theorem jet_boundLevel (A : Space →L[ℝ] Space) (q r : ℕ) :
    boundLevel P (jet P A q) r = if r=0 then ‖A‖ else 0 := by
  induction q generalizing A r with
  | zero => cases r <;> simp [jet,boundLevel,coefficient]
  | succ q ih =>
    cases r with
    | zero => simp [jet, boundLevel, coefficient]
    | succ r =>
      simp only [jet]
      rw [boundLevel]
      simp [ih]


-- @@ L162-165 verbatim
omit [Fact (0 < P)] in
theorem jet_zero_coefficientBlock (q b n : ℕ) :
    coefficientBlock P (jet P (0 : Space →L[ℝ] Space) q) b n=0 := by
  simp only [coefficientBlock,jet_boundLevel,norm_zero,ite_self,Finset.sum_const_zero,mul_zero]


-- @@ L167-173 verbatim
omit [Fact (0 < P)] in
theorem jet_positive_coefficientBlock (A : Space →L[ℝ] Space) (q b n : ℕ) (hn : 0 < n) :
    coefficientBlock P (jet P A q) b n=0 := by
  unfold coefficientBlock
  have hz (r : ℕ) : boundLevel P (jet P A q) (n+r)=0 := by
    rw [jet_boundLevel,ite_eq_right (by omega)]
  simp only [hz,Finset.sum_const_zero,mul_zero]


-- @@ L175-178 verbatim
omit [Fact (0 < P)] in
theorem jet_zero_weightedCoefficient (q b N : ℕ) (ρ : ℝ) :
    weightedCoefficient P (jet P (0 : Space →L[ℝ] Space) q) b N ρ=0 := by
  simp only [weightedCoefficient,jet_zero_coefficientBlock,mul_zero,Finset.sum_const_zero]


-- @@ L180-187 verbatim
theorem coefficient_operator_id :
    (coefficient P (ContinuousLinearMap.id ℝ Space)).operator=ContinuousLinearMap.id ℝ (LiftL2 P)
        := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(coefficient P (ContinuousLinearMap.id ℝ Space)).operator_ae u] with x hx
  exact hx


-- @@ L189-196 verbatim
theorem coefficient_operator_zero :
    (coefficient P (0 : Space →L[ℝ] Space)).operator=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(coefficient P (0 : Space →L[ℝ] Space)).operator_ae u,
    Lp.coeFn_zero Space 2 (liftMeasure P)] with x hx hz
  exact hx.trans hz.symm


-- @@ L198-202 verbatim
/-- Tower, bundling `coefficient`, `jet`, `continuous`. -/
def tower (T : ℝ) (A : Space →L[ℝ] Space) : CoefficientTower P T where
  coefficient _ := coefficient P A
  jet q _ := jet P A q
  continuous _ := continuous_const


-- @@ L204-224 verbatim
/-- Data, bundling `κ`, `direction`, `scale_bound`, `direction_bound` and the required
compatibility proofs. -/
def data {T : ℝ} (F R : FieldTower P T) : EulerAllOrderCorrectionData.Data P T where
  κ := 1
  direction := 0
  scale_bound := by norm_num
  direction_bound := by simp only [norm_zero,zero_le_one]
  metric := tower P T (ContinuousLinearMap.id ℝ Space)
  metric_continuous := by
    change Continuous (fun _ : Icc (0 : ℝ) T => (coefficient P (ContinuousLinearMap.id ℝ
        Space)).operator)
    exact continuous_const
  coercivity := 1
  coercivity_pos := zero_lt_one
  metric_pos _ _ v := by
    change 1*‖v‖^2 ≤ ⟪v,v⟫_ℝ
    simp only [one_mul,real_inner_self_eq_norm_sq,le_refl]
  linear := tower P T 0
  quadratic _ := tower P T 0
  approximation := F
  residual := R


-- @@ L226-250 verbatim
/-- Metric budget, bundling `metric`, `continuous`, `derivative`, `hasDeriv` and the required
compatibility proofs. -/
def metricBudget {T : ℝ} (hT : 0 ≤ T) (F R : FieldTower P T) :
    MetricBudget P T hT ((data P F R).atOrder P 1) where
  metric _ := coefficient P (ContinuousLinearMap.id ℝ Space)
  continuous := continuous_const
  derivative := 0
  hasDeriv t _ := by
    change HasDerivAt (fun _ => (coefficient P (ContinuousLinearMap.id ℝ Space)).operator) 0 t
    exact hasDerivAt_const t _
  c := 1
  c_pos := zero_lt_one
  symmetric _ _ _ _ := rfl
  coercive _ _ v := by
      simp only [coefficient,id_apply,one_pow,one_mul,real_inner_self_eq_norm_sq,le_refl]
  inverse _ _ v := by change v=v; rfl
  bound := 1
  first := 0
  time := 0
  bound_nonneg := zero_le_one
  first_nonneg := le_rfl
  time_nonneg := le_rfl
  bound_le _ := by simp only [coefficient,coe_nnnorm]; exact norm_id_le
  first_le _ := le_rfl
  time_le _ := by simp only [ContinuousMap.zero_apply,norm_zero,le_refl]


-- @@ L252-253 verbatim
/-- Pressure bound, given by `9^729`. -/
def pressureBound : ℝ := 9^729


-- @@ L255-256 verbatim
theorem pressureBound_one_le : 1 ≤ pressureBound :=
  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)


-- @@ L258-264 verbatim
omit [Fact (0 < P)] in
theorem identity_base (q r : ℕ) :
    boundLevel P (jet P (ContinuousLinearMap.id ℝ Space) q) r ≤ 1 := by
  rw [jet_boundLevel]
  split_ifs
  · exact norm_id_le
  · exact zero_le_one


-- @@ L266-274 verbatim
omit [Fact (0 < P)] in
theorem identity_pressure (q : ℕ) (hq : 6 ≤ q) :
    (EulerH6Pressure.CoefficientJet.restrict (jet P (ContinuousLinearMap.id ℝ Space) q)
      5 (by omega)).pressureConstant 1 ≤ pressureBound ∧
    (EulerH6Pressure.CoefficientJet.restrict (jet P (ContinuousLinearMap.id ℝ Space) q)
      6 hq).pressureConstant 1 ≤ pressureBound := by
  simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq
    (jet P (ContinuousLinearMap.id ℝ Space) q) 1 1 zero_lt_one le_rfl (by norm_num)
    (fun r _ => identity_base P q r)


-- @@ L276-276 verbatim
end EulerConstantCorrection


-- @@ L278-278 verbatim
end

-- @@ L279-279 verbatim
end


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
section


-- @@ L285-287 verbatim
/-! The literal spatial convection of a small smooth cylinder field has
a quadratic residual envelope at every Sobolev order. No residual estimate
or differential equation is postulated. -/


-- @@ L289-289 verbatim
@[expose] public section


-- @@ L291-291 verbatim
noncomputable section


-- @@ L293-293 verbatim
namespace EulerSmallCorrection


-- @@ L295-298 verbatim
open Set Finset EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerPacketCylinderField EulerPacketProfileRecursion EulerGevrey
  EulerPacketWeights EulerH6Pressure EulerSobolevGevreyOperators
  EulerCylinderPathProduct EulerConstantCorrection EulerAllOrderCorrectionData


-- @@ L300-300 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L302-303 verbatim
/-- Residual cost, given by `1+108*productBlockConstant P*C^2*R`. -/
def residualCost (C R : ℝ) : ℝ := 1+108*productBlockConstant P*C^2*R


-- @@ L305-308 verbatim
theorem residualCost_pos (C R : ℝ) (hR : 0 ≤ R) : 0 < residualCost P C R := by
  have hp := productBlockConstant_nonneg P
  unfold residualCost
  positivity


-- @@ L310-310 verbatim
variable {P} {T : ℝ} {raw : VectorField} (G : Field P T raw)


-- @@ L312-313 verbatim
/-- Residual, given by `(G.smul ε).spatialTransport (G.smul ε)`. -/
def residual (ε : ℝ) := (G.smul ε).spatialTransport (G.smul ε)


-- @@ L315-317 verbatim
/-- Input, given by `data P (G.smul ε).toFieldTower (residual G ε).toFieldTower`. -/
def input (ε : ℝ) : Data P T :=
  data P (G.smul ε).toFieldTower (residual G ε).toFieldTower


-- @@ L319-330 verbatim
theorem weighted_shift_one {q : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A 1) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (s N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * R ≤ 1 / 2) (t : Icc (0 : ℝ) T) :
    weightedNorm P q N ρ (G.toFieldTower.realization s t) ≤ 12*A*R := by
  have h := hG.toFieldTower_weightedNorm_le s N hN ρ hρ t
  simp_rw [Field.weight_majorant_one] at h
  rw [← mul_sum] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (Field.square_geometric_le_twelve (ρ*R) (mul_nonneg hρ.le hR) hsmall (N+1)) hR)
    hA).trans_eq (by ring))


-- @@ L332-334 verbatim
theorem scaled_word {C R : ℝ} (hG : G.WordBound 6 R C 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (G.smul ε).WordBound 6 R (ε*C) 0 := by
  simpa only [abs_of_nonneg hε] using hG.smul ε


-- @@ L336-340 verbatim
theorem residual_word {C R : ℝ} (hG : G.WordBound 6 R C 0)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 ≤ ε) :
    (residual G ε).WordBound 6 R (9*productBlockConstant P*(ε*C)*(ε*C)) 1 :=
  (scaled_word G hG ε hε).spatialTransport (scaled_word G hG ε hε) hR
    (mul_nonneg hε hC) (mul_nonneg hε hC)


-- @@ L342-353 verbatim
theorem residual_weighted {C R : ℝ} (hG : G.WordBound 6 R C 0)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 ≤ ε)
    (s N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * R ≤ 1 / 2) (t : Icc (0 : ℝ) T) :
    weightedNorm P 6 N ρ ((residual G ε).toFieldTower.realization s t) ≤
      ε^2*residualCost P C R := by
  have hp := productBlockConstant_nonneg P
  have hh := weighted_shift_one (residual G ε) (residual_word G hG hC hR ε hε)
    hR (by positivity) s N hN ρ hρ hsmall t
  apply hh.trans
  unfold residualCost
  linarith only [sq_nonneg ε]


-- @@ L355-355 verbatim
end EulerSmallCorrection


-- @@ L357-357 verbatim
end

-- @@ L358-358 verbatim
end


-- @@ L360-360 verbatim
end


-- @@ L362-362 verbatim
section


-- @@ L364-367 verbatim
/-! An actual exact lifted Euler solution is constructed from any genuine
smooth solenoidal L² datum with factorial derivative bounds. The amplitude
is an explicit function of the supplied bounds and does not depend on the
particular datum realizing them. -/


-- @@ L369-369 verbatim
section


-- @@ L371-373 verbatim
/-! A genuine all-order correction budget for small smooth data with the
identity metric. Every field and coefficient estimate is derived from the
given datum's actual word bound; the amplitude is chosen explicitly. -/


-- @@ L375-375 verbatim
section


-- @@ L377-380 verbatim
/-! An explicit positive amplitude puts any finite Gevrey datum and
quadratic residual envelope in the all-order correction regime. The
growth constant belongs to the identity-metric equation, not to an
assumed solution. -/


-- @@ L382-382 verbatim
@[expose] public section


-- @@ L384-384 verbatim
noncomputable section


-- @@ L386-386 verbatim
namespace EulerSmallCorrection


-- @@ L388-388 verbatim
open Set EulerConstantCorrection EulerNonlinearEnergyConstants


-- @@ L390-390 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L392-393 verbatim
/-- Growth, given by `energyConstant P 0 0 1 1 pressureBound 1 1 0 0 1`. -/
def growth : ℝ := energyConstant P 0 0 1 1 pressureBound 1 1 0 0 1


-- @@ L395-398 verbatim
theorem growth_pos : 0 < growth P :=
  energyConstant_pos P 0 0 1 1 pressureBound 1 1 0 0 1 le_rfl le_rfl
    zero_le_one zero_le_one (zero_le_one.trans pressureBound_one_le)
    zero_le_one zero_le_one le_rfl le_rfl zero_lt_one


-- @@ L400-401 verbatim
/-- Initial radius, given by `1/(2*(R+1))`. -/
def initialRadius (R : ℝ) : ℝ := 1/(2*(R+1))


-- @@ L403-405 verbatim
theorem initialRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < initialRadius R := by
  unfold initialRadius
  positivity


-- @@ L407-413 verbatim
theorem initialRadius_mul (R : ℝ) (hR : 0 ≤ R) : initialRadius R*R ≤ 1/2 := by
  unfold initialRadius
  have hd : 0 < 2*(R+1) := by positivity
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ = R/(R+1) := by field_simp
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)


-- @@ L415-424 verbatim
/-- These are scalar smallness inequalities, obtained explicitly below. -/
structure Scale (C R E : ℝ) where
  /-- Value of `Scale`, of type `ℝ`. -/
  value : ℝ
  positive : 0 < value
  one : value ≤ 1
  background : 2*value*C ≤ 1
  derivative : 12*value*C*R ≤ 1
  shrink : 2*growth P*(8*value*C+value) ≤ initialRadius R/2
  residual : 2*(value^2*E)*Real.exp (3*growth P) ≤ value/2


-- @@ L426-458 verbatim
/-- Scale as an element of `Scale P C R E`. -/
def scale (C R E : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hE : 0 < E) : Scale P C R E := by
  let a := 1/(2*C+1)
  let b := 1/(12*C*R+1)
  let c := initialRadius R/(4*growth P*(8*C+1)+1)
  let d := 1/(4*E*Real.exp (3*growth P)+1)
  let v := min 1 (min a (min b (min c d)))
  have hG := growth_pos P
  have hr := initialRadius_pos R hR
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hv : 0 < v := lt_min zero_lt_one (lt_min ha (lt_min hb (lt_min hc hd)))
  have h1 : v ≤ 1 := min_le_left _ _
  have h2 : v ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : v ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : v ≤ c := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have h5 : v ≤ d := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have ha' : v*(2*C+1) ≤ 1 := (le_div_iff₀ (by positivity)).mp h2
  have hb' : v*(12*C*R+1) ≤ 1 := (le_div_iff₀ (by positivity)).mp h3
  have hc' : v*(4*growth P*(8*C+1)+1) ≤ initialRadius R :=
    (le_div_iff₀ (by positivity)).mp h4
  have hd' : v*(4*E*Real.exp (3*growth P)+1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp h5
  refine ⟨v,hv,h1,?_,?_,?_,?_⟩
  · linarith only [ha',hv]
  · linarith only [hb',hv]
  · linarith only [hc',hv]
  · have hh := mul_le_mul_of_nonneg_left hd' hv.le
    linarith only [hh,sq_nonneg v]


-- @@ L460-463 verbatim
/-- Radius as an element of `C(Icc (0 : ℝ) 1,ℝ)`. -/
def Scale.radius {C R E : ℝ} (S : Scale P C R E) : C(Icc (0 : ℝ) 1,ℝ) :=
  ⟨fun t => initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val,
    continuous_const.sub (continuous_const.mul continuous_subtype_val)⟩


-- @@ L465-476 verbatim
theorem Scale.radius_bounds {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C)
    (t : Icc (0 : ℝ) 1) :
    initialRadius R/2 ≤ S.radius P t ∧ S.radius P t ≤ initialRadius R := by
  have hG := growth_pos P
  have hv := S.positive
  have ha : 0 ≤ 2*growth P*(8*S.value*C+S.value) := by positivity
  have hb := mul_le_mul_of_nonneg_left t.property.2 ha
  have hc := mul_nonneg ha t.property.1
  have hd := S.shrink
  change initialRadius R/2 ≤ initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val ∧
    initialRadius R-2*growth P*(8*S.value*C+S.value)*t.val ≤ initialRadius R
  constructor <;> linarith only [hb,hc,hd]


-- @@ L478-480 verbatim
theorem Scale.radius_positive {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (t : Icc (0 : ℝ) 1) : 0 < S.radius P t :=
  (half_pos (initialRadius_pos R hR)).trans_le (S.radius_bounds P hC t).1


-- @@ L482-484 verbatim
theorem Scale.radius_small {C R E : ℝ} (S : Scale P C R E) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (t : Icc (0 : ℝ) 1) : S.radius P t*R ≤ 1/2 :=
  (mul_le_mul_of_nonneg_right (S.radius_bounds P hC t).2 hR).trans (initialRadius_mul R hR)


-- @@ L486-486 verbatim
end EulerSmallCorrection


-- @@ L488-488 verbatim
end

-- @@ L489-489 verbatim
end


-- @@ L491-491 verbatim
end


-- @@ L493-493 verbatim
@[expose] public section


-- @@ L495-495 verbatim
noncomputable section


-- @@ L497-497 verbatim
namespace EulerSmallCorrection


-- @@ L499-504 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerPacketCylinderField
  EulerPacketProfileRecursion EulerAllOrderCorrectionData EulerCorrectionEnergyData
  EulerCorrectionEnergyMajorants EulerConstantCorrection EulerSobolevGevreyOperators
  EulerQuadraticSource EulerSobolevDriftNorm EulerFunctionalVelocity EulerSobolevTransport
  EulerGevreyGrowthCoefficient EulerGevreyMetricEstimate EulerNonlinearEnergyConstants


-- @@ L506-508 verbatim
variable {P : ℝ} [Fact (0 < P)] {raw : VectorField}
  (G : Field P 1 raw) {C R : ℝ} (hG : G.WordBound 6 R C 0)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (S : Scale P C R (residualCost P C R))


-- @@ L510-557 verbatim
/-- Spatial budget, bundling `Rc`, `M`, `B`, `B0` and the required compatibility proofs. -/
def spatialBudget (q : ℕ) (hq : 6 ≤ q) :
    SpatialBudget P (by omega : 6 ≤ (q+1)+1)
      ((input G S.value).atOrder P ((q+1)+1)) (q-4) (S.radius P) where
  Rc := 0
  M := pressureBound
  B := 1
  B0 := 1
  B1 := 1
  A0 := 0
  A2 := 0
  residual := S.value^2*residualCost P C R
  Rc_nonneg := le_rfl
  M_one_le := pressureBound_one_le
  B_nonneg := zero_le_one
  B0_nonneg := zero_le_one
  B1_nonneg := zero_le_one
  A0_nonneg := le_rfl
  A2_nonneg := le_rfl
  residual_pos := mul_pos (sq_pos_of_pos S.positive) (residualCost_pos P C R hR)
  radius_pos := S.radius_positive P hC hR
  inverse_five _ := (identity_pressure P ((q+1)+1) (by omega)).1
  inverse_six _ := (identity_pressure P ((q+1)+1) (by omega)).2
  radius_small _ := by simp only [mul_zero,zero_le_one]
  metric_derivatives _ l hl _ := by
    change EulerH6Pressure.coefficientBlock P
      (jet P (ContinuousLinearMap.id ℝ Space) ((q+1)+1)) 6 l ≤ 0^l*(l.factorial : ℝ)^2
    rw [jet_positive_coefficientBlock P _ _ _ l (by omega)]
    positivity
  metric_base _ r _ := identity_base P ((q+1)+1) r
  background t := by
    have h := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedNorm_le_two
      hR (mul_nonneg S.positive.le hC) (((q+1)+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact h.trans (by simpa only [mul_assoc] using S.background)
  background_derivative t := by
    have h := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedDerivativeNorm_le_twelve
      hR (mul_nonneg S.positive.le hC) ((q+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact h.trans (by simpa only [mul_assoc] using S.derivative)
  linear _ := (jet_zero_weightedCoefficient P _ _ _ _).le
  quadratic _ := by
    change (∑ _i : Fin 3, weightedCoefficient P (jet P (0 : Space →L[ℝ] Space) ((q+1)+1))
      6 (q-4) _) ≤ 0
    simp only [jet_zero_weightedCoefficient,Finset.sum_const_zero,le_refl]
  residual_bound t := residual_weighted G hG hC hR S.value S.positive.le
    ((q+1)+1) (q-4) (by omega) (S.radius P t)
    (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t


-- @@ L559-575 verbatim
/-- Drift budget, bundling `full`, `drift`, `drift_nonneg`, `drift_bound` and the required
compatibility proofs. -/
def driftBudget (q : ℕ) (hq : 6 ≤ q) :
    EulerDriftCorrectionBudget.Budget P (by omega : 6 ≤ (q+1)+1)
      ((input G S.value).atOrder P ((q+1)+1)) (q-4) (S.radius P) where
  full := spatialBudget G hG hC hR S q hq
  drift := 8*S.value*C
  drift_nonneg := by have hv := S.positive; positivity
  drift_bound t := by
    have hh := weightedDriftNorm_velocityMap_le P 6 (q-4) (S.radius P t)
      (S.radius_positive P hC hR t) (velocityComponents 1 (0 : Space))
      (velocityComponents_norm 1 (0 : Space) (by norm_num) (by simp))
      ((G.smul S.value).toFieldTower.realization (((q+1)+1)+1) t)
    have hb := (scaled_word G hG S.value S.positive.le).toFieldTower_weightedNorm_le_two
      hR (mul_nonneg S.positive.le hC) (((q+1)+1)+1) (q-4) (by omega)
      (S.radius P t) (S.radius_positive P hC hR t) (S.radius_small P hC hR t) t
    exact hh.trans ((mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (by ring))


-- @@ L577-587 verbatim
theorem driftBudget_growth (q : ℕ) (hq : 6 ≤ q) :
    combinedConstant P (driftBudget G hG hC hR S q hq).full
      ((input G S.value).metricBudget P (by norm_num)
        (metricBudget P (by
            norm_num) (G.smul S.value).toFieldTower (residual G S.value).toFieldTower)
        (q+1)) = growth P := by
  change energyConstant P
    (growthBudgetBase 1 0 0+growthBudgetSlope 1 0*sobolevEmbeddingConstant P 6*1)
    (growthBudgetSlope 1 0*sobolevEmbeddingConstant P 6*metricAmplification 1)
    (1/1) 1 pressureBound 1 1 0 0 1 = growth P
  norm_num [growthBudgetBase,growthBudgetSlope,growth]


-- @@ L589-614 verbatim
/-- Budget, bundling `metric`, `radius`, `growthCoefficient`, `delta` and the required
compatibility proofs. -/
def budget (hdiv : ∀ t, G.path t ∈ divergenceFreeSpace P 1 (0 : Space)) :
    EulerAllOrderDriftCorrection.Budget P (by norm_num : (0 : ℝ) < 1) (input G S.value) where
  metric := metricBudget P (by
      norm_num) (G.smul S.value).toFieldTower (residual G S.value).toFieldTower
  radius := S.radius P
  growthCoefficient := growth P
  delta := S.value
  initialRadius := initialRadius R
  spatial := driftBudget G hG hC hR S
  growth_bound q hq := (driftBudget_growth G hG hC hR S q hq).le
  delta_pos := S.positive
  delta_le_one := S.one
  radius_pos := initialRadius_pos R hR
  decay _ _ := by
    change 2*growth P*(8*S.value*C+S.value)*1 ≤ initialRadius R/2
    simpa only [mul_one] using S.shrink
  scale _ _ := by
    change initialRadius R*0 ≤ 1
    simp only [mul_zero,zero_le_one]
  small _ _ := by
    change 2*(S.value^2*residualCost P C R)*Real.exp (3*growth P*1) ≤ S.value/2
    simpa only [mul_one] using S.residual
  radius_eq _ _ _ := rfl
  divergence t := (divergenceFreeSpace P 1 (0 : Space)).smul_mem S.value (hdiv t)


-- @@ L616-619 verbatim
/-- No scalar guard is required of the input: the amplitude is explicitly
chosen from its finite actual Gevrey constants. -/
def smallBudget (hdiv : ∀ t, G.path t ∈ divergenceFreeSpace P 1 (0 : Space)) :=
  budget G hG hC hR (scale P C R (residualCost P C R) hC hR (residualCost_pos P C R hR)) hdiv


-- @@ L621-621 verbatim
end EulerSmallCorrection


-- @@ L623-623 verbatim
end

-- @@ L624-624 verbatim
end


-- @@ L626-626 verbatim
end


-- @@ L628-628 verbatim
section


-- @@ L630-632 verbatim
/-! A genuine smooth spatial L² field, embedded as a time-independent,
angle-independent cylinder field. Tensor bounds give a fixed mixed Sobolev
word bound, and classical divergence zero gives the actual lifted constraint. -/


-- @@ L634-634 verbatim
@[expose] public section


-- @@ L636-636 verbatim
noncomputable section


-- @@ L638-638 verbatim
namespace EulerStaticCylinder


-- @@ L640-644 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpTranslation EulerLpCylinderTranslation EulerCylinderSpatialEmbedding
  EulerCylinderSpatialMean EulerMeanCylinderSolenoidal EulerCylinderClassicalSolenoidal
  EulerPacketCylinderField EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerGevrey EulerVolterraConvolution EulerCylinderSobolev

-- @@ L645-645 verbatim
open scoped ContDiff


-- @@ L647-647 verbatim
variable (P T : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space)


-- @@ L649-651 verbatim
/-- Spatial orbit, given by `EulerLpTranslation.translation a.1 u.toLp`. -/
def spatialOrbit (a : LiftTangent) : Lp Space 2 (volume : Measure Space) :=
  EulerLpTranslation.translation a.1 u.toLp


-- @@ L653-654 verbatim
theorem spatialOrbit_smooth : ContDiff ℝ ∞ (spatialOrbit u) :=
  u.translation_contDiff.comp contDiff_fst


-- @@ L656-663 verbatim
theorem embeddedOrbit_smooth : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a (embedding P
    u.toLp)) := by
  have he : (fun a : LiftTangent => translate P a (embedding P u.toLp)) =
      (embedding P) ∘ spatialOrbit u := by
    funext a
    exact embedding_translate P a u.toLp
  rw [he]
  exact (embedding P).contDiff.comp (spatialOrbit_smooth u)


-- @@ L665-672 verbatim
/-- Field, constructed using `Field.ofLifted`. -/
def field : Field P T (fun z => u.field z.2.1) :=
  Field.ofLifted (ContinuousMap.const (Icc (0 : ℝ) T) (embedding P u.toLp))
    (constantPath_orbit_contDiff P _ (embeddedOrbit_smooth P u))
    (fun _ z => u.field z.1)
    (fun _ => u.smooth.continuous.comp continuous_fst)
    (fun _ => embedding_representative P u.toLp u.field u.toLp_ae)
    (fun _ _ _ => rfl)


-- @@ L674-675 verbatim
@[simp] theorem field_path :
    (field P T u).path=ContinuousMap.const (Icc (0 : ℝ) T) (embedding P u.toLp) := rfl


-- @@ L677-680 verbatim
theorem field_time (hT : 0 ≤ T) : TimeDerivative hT (field P T u) (Field.zero P T) := by
  intro t
  change HasDerivWithinAt (fun _ : ℝ => embedding P u.toLp) 0 (Icc (0 : ℝ) T) t
  exact hasDerivWithinAt_const _ _ _


-- @@ L682-689 verbatim
theorem field_divergence (κ : ℝ) (m : Space)
    (hu : ∀ x, EulerSmoothLimit.divergence u.field x = 0) (t : Icc (0 : ℝ) T) :
    (field P T u).path t ∈ divergenceFreeSpace P κ m := by
  apply mem_of_classical P κ m (embedding P u.toLp) (fun z => u.field z.1)
    (embedding_representative P u.toLp u.field u.toLp_ae)
  · intro z
    exact u.smooth.comp (contDiff_const.add contDiff_fst)
  · exact lift_classical_divergence P κ m u.field u.smooth hu


-- @@ L691-705 verbatim
theorem spatialOrbit_derivative_norm (n : ℕ) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (spatialOrbit u) a‖ ≤ ‖u.jetLp n‖ := by
  let L := ContinuousLinearMap.fst ℝ Space ℝ
  have he : spatialOrbit u=(fun b : Space => EulerLpTranslation.translation b u.toLp) ∘ L := rfl
  rw [he,L.iteratedFDeriv_comp_right u.translation_contDiff a (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b u.toLp) a.1‖*
        ∏ _i : Fin n, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L)
        (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
    _ = ‖iteratedFDeriv ℝ n (fun b : Space => EulerLpTranslation.translation b u.toLp) a.1‖ := by
      simp only [Finset.prod_const_one,mul_one]
    _ ≤ ‖u.jetLp n‖ := u.norm_iteratedFDeriv_translation_le n a.1


-- @@ L707-737 verbatim
theorem field_wordBound (q : ℕ) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hb : u.HasJetBound C R) :
    (field P T u).WordBound q (sobolevCoefficientRadius (Fin 4) R)
      (Real.sqrt P*sobolevCoefficientAmplitude (Fin 4) q R C) 0 := by
  have hF := spatialOrbit_smooth u
  have hFb (n : ℕ) (a : LiftTangent) :
      ‖iteratedFDeriv ℝ n (spatialOrbit u) a‖ ≤ C*majorant R 0 n :=
    (spatialOrbit_derivative_norm u n a).trans (by
        simpa only [majorant,Nat.add_zero,mul_assoc] using hb n)
  have hB (n : ℕ) : block standardDirection q (spatialOrbit u) n 0 ≤
      sobolevCoefficientAmplitude (Fin 4) q R C*majorant (sobolevCoefficientRadius (Fin 4) R) 0 n
          := by
    have hh := coefficientBlock_of_tensor_bound standardDirection
      (fun i => by cases i using Fin.cases <;> simp [Prod.norm_def]) q (spatialOrbit u)
      hF R C hR hC hFb n 0
    have hp : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
    exact ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hp
      (block_nonneg standardDirection q (spatialOrbit u) n 0))).trans hh
  intro n
  have hc := constantPath_block_le (K := Icc (0 : ℝ) T) P standardDirection q
    (embedding P u.toLp) (embeddedOrbit_smooth P u) n 0
  have he : (fun a : LiftTangent => translate P a (embedding P u.toLp)) =
      (embedding P) ∘ spatialOrbit u := by
    funext a
    exact embedding_translate P a u.toLp
  have hc' := hc.trans_eq (congrArg (fun f => block standardDirection q f n 0) he)
  have hm := block_comp_clm_le standardDirection q (embedding (V := Space) P) (spatialOrbit u) hF n
      0
  apply hc'.trans (hm.trans _)
  exact (mul_le_mul (embedding_norm P) (hB n)
    (block_nonneg standardDirection q (spatialOrbit u) n 0) (Real.sqrt_nonneg P)).trans_eq (by ring)


-- @@ L739-739 verbatim
end EulerStaticCylinder


-- @@ L741-741 verbatim
end

-- @@ L742-742 verbatim
end


-- @@ L744-744 verbatim
end


-- @@ L746-746 verbatim
section


-- @@ L748-750 verbatim
/-! For a static approximation the prescribed residual is exactly its
spatial convection, at every finite Sobolev order. This verifies the
equation input to the correction theorem rather than assuming it. -/


-- @@ L752-752 verbatim
@[expose] public section


-- @@ L754-754 verbatim
noncomputable section


-- @@ L756-756 verbatim
namespace EulerSmallCorrection


-- @@ L758-764 verbatim
open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerCylinderSmoothOrbit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderPathProduct
  EulerCorrectionResidualCancellation EulerSobolevCoefficientPressure
  EulerConstantCorrection EulerVolterraConvolution EulerMetricTransport
  EulerLiftedWeakDerivative


-- @@ L766-766 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)


-- @@ L768-772 verbatim
theorem fieldTower_pointField (t : Icc (0 : ℝ) T) :
    G.toFieldTower.pointField t=pointField P G.path G.orbit t :=
  G.toFieldTower.pointField_unique t _
    (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t))
    (pointField_ae P G.path G.orbit t)


-- @@ L774-793 verbatim
theorem nonlinearity_eq_residual (ε : ℝ) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    nonlinearity P ((input G ε).atOrder P q) hq t
      ((G.smul ε).toFieldTower.realization (q+1) t) =
      (residual G ε).toFieldTower.realization q t := by
  apply value_injective P
  rw [(residual G ε).toFieldTower_value]
  apply Lp.ext
  have hn := EulerAllOrderDriftCorrection.nonlinearity_value_ae P (input G ε)
    (G.smul ε).toFieldTower q hq t
  have hr := advectionPath_ae P (G.smul ε).path (G.smul ε).path
    (G.smul ε).orbit (G.smul ε).orbit t
  filter_upwards [hn,hr] with x hn hr
  rw [hn]
  change _ = advectionPath P (G.smul ε).path (G.smul ε).path
    (G.smul ε).orbit (G.smul ε).orbit t x
  rw [hr]
  simp only [pointNonlinearity,input,data,tower,coefficient,
    zero_apply,zero_add,smul_zero,Finset.sum_const_zero,add_zero,
    transportDirection,one_smul,inner_zero_left]
  rw [fieldTower_pointField (G.smul ε)]


-- @@ L795-799 verbatim
theorem zero_tower (q : ℕ) (t : Icc (0 : ℝ) T) :
    (Field.zero P T).toFieldTower.realization q t=0 := by
  apply value_injective P
  rw [(Field.zero P T).toFieldTower_value]
  rfl


-- @@ L801-806 verbatim
theorem scaled_zero_tower (ε : ℝ) (q : ℕ) (t : Icc (0 : ℝ) T) :
    ((Field.zero P T).smul ε).toFieldTower.realization q t=0 := by
  apply value_injective P
  rw [((Field.zero P T).smul ε).toFieldTower_value]
  change ε • (0 : LiftL2 P)=0
  exact smul_zero ε


-- @@ L808-827 verbatim
/-- Approximation residual, bundling `pressure`, `gradient`, `equation`, `let` and the required
compatibility proofs. -/
def approximationResidual (hT : 0 < T) (ε : ℝ)
    (hstatic : TimeDerivative hT.le G (Field.zero P T)) :
    ApproximationResidual P hT (input G ε) where
  pressure := (Field.zero P T).toFieldTower
  gradient _ := (gradientSpace P 1 (0 : Space)).zero_mem
  equation q hq t ht := by
    let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := ((G.smul ε).toFieldTower_hasDerivWithinAt ((Field.zero P T).smul ε)
      hT.le (hstatic.smul ε) q s).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [scaled_zero_tower ε q s] at hd
    change HasDerivAt (extendPath T hT.le ((G.smul ε).toFieldTower.realization q))
      ((residual G ε).toFieldTower.realization q s -
        nonlinearity P ((input G ε).atOrder P q) hq s
          ((G.smul ε).toFieldTower.realization (q+1) s) -
        coefficientSobolevOperator P ((input G ε).metric.jet q s)
          ((Field.zero P T).toFieldTower.realization q s)) t
    simp only [nonlinearity_eq_residual G ε q hq s,zero_tower,sub_self,map_zero]
    exact hd


-- @@ L829-829 verbatim
end EulerSmallCorrection


-- @@ L831-831 verbatim
end

-- @@ L832-832 verbatim
end


-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
@[expose] public section


-- @@ L838-838 verbatim
noncomputable section


-- @@ L840-840 verbatim
namespace EulerStaticEuler


-- @@ L842-843 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerParameterWordGevrey
  EulerPacketCylinderField EulerAllOrderDriftCorrection EulerSmallCorrection EulerLpTranslation


-- @@ L845-845 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L847-848 verbatim
/-- Mixed radius, given by `sobolevCoefficientRadius (Fin 4) R`. -/
def mixedRadius (R : ℝ) : ℝ := sobolevCoefficientRadius (Fin 4) R

-- @@ L849-850 verbatim
/-- Mixed amplitude, given by `Real.sqrt P*sobolevCoefficientAmplitude (Fin 4) 6 R C`. -/
def mixedAmplitude (C R : ℝ) : ℝ := Real.sqrt P*sobolevCoefficientAmplitude (Fin 4) 6 R C


-- @@ L852-853 verbatim
theorem mixedRadius_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ mixedRadius R :=
  sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR


-- @@ L855-857 verbatim
omit [Fact (0 < P)] in
theorem mixedAmplitude_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : 0 ≤ mixedAmplitude P C R :=
  mul_nonneg (Real.sqrt_nonneg P) (sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 R C hR hC)


-- @@ L859-865 verbatim
/-- Scales, given by `scale P _ _ _ (mixedAmplitude_nonneg P C R hC hR) (mixedRadius_nonneg R
hR) (residualCost_pos P _ _ (mixedRadius_nonneg R hR))`. -/
def scales (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    Scale P (mixedAmplitude P C R) (mixedRadius R)
      (residualCost P (mixedAmplitude P C R) (mixedRadius R)) :=
  scale P _ _ _ (mixedAmplitude_nonneg P C R hC hR) (mixedRadius_nonneg R hR)
    (residualCost_pos P _ _ (mixedRadius_nonneg R hR))


-- @@ L867-868 verbatim
/-- Amplitude, given by `(scales P C R hC hR).value`. -/
def amplitude (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ := (scales P C R hC hR).value


-- @@ L870-871 verbatim
theorem amplitude_pos (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : 0 < amplitude P C R hC hR :=
  (scales P C R hC hR).positive


-- @@ L873-874 verbatim
theorem amplitude_le_one (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : amplitude P C R hC hR ≤ 1 :=
  (scales P C R hC hR).one


-- @@ L876-877 verbatim
variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L879-880 verbatim
/-- Input data, given by `input (EulerStaticCylinder.field P 1 u) (amplitude P C R hC hR)`. -/
def inputData := input (EulerStaticCylinder.field P 1 u) (amplitude P C R hC hR)


-- @@ L882-888 verbatim
/-- Correction budget, constructed using `budget`. -/
def correctionBudget :
    Budget P (by norm_num : (0 : ℝ) < 1) (inputData P u C R hC hR) :=
  budget (EulerStaticCylinder.field P 1 u) (EulerStaticCylinder.field_wordBound P 1 u 6 C R hC hR
      hu)
    (mixedAmplitude_nonneg P C R hC hR) (mixedRadius_nonneg R hR) (scales P C R hC hR)
    (EulerStaticCylinder.field_divergence P 1 u 1 0 hdiv)


-- @@ L890-895 verbatim
/-- Exact packet, constructed using `exactPacketOfResidual`. -/
def exactPacket : ExactLiftedPacket P (by norm_num : (0 : ℝ) < 1)
    (inputData P u C R hC hR) (correctionBudget P u C R hC hR hu hdiv) :=
  exactPacketOfResidual P (correctionBudget P u C R hC hR hu hdiv)
    (approximationResidual (EulerStaticCylinder.field P 1 u) (by norm_num)
      (amplitude P C R hC hR) (EulerStaticCylinder.field_time P 1 u (by norm_num)))


-- @@ L897-901 verbatim
theorem exactPacket_initial (q : ℕ) :
    (exactPacket P u C R hC hR hu hdiv).velocity.realization q ⟨0,le_rfl,by norm_num⟩ =
      ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.realization q
        ⟨0,le_rfl,by norm_num⟩ :=
  sub_eq_zero.mp ((exactPacket P u C R hC hR hu hdiv).zero_initial_correction q)


-- @@ L903-903 verbatim
end EulerStaticEuler


-- @@ L905-905 verbatim
end

-- @@ L906-906 verbatim
end


-- @@ L908-908 verbatim
end


-- @@ L910-910 verbatim
section


-- @@ L912-914 verbatim
/-! With spatial scale one and angular direction zero, the zero-angle
slice of the actual exact lifted solution solves ordinary three-dimensional
Euler. The scalar pressure is the canonical normalized graph potential. -/


-- @@ L916-916 verbatim
@[expose] public section


-- @@ L918-918 verbatim
noncomputable section


-- @@ L920-920 verbatim
namespace EulerConstantEuler


-- @@ L922-925 verbatim
open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerConstantCorrection EulerMetricTransport EulerGraphPressurePotential
  EulerVolterraConvolution EulerLagrangian EulerLpTranslation

-- @@ L926-926 verbatim
open scoped ContDiff


-- @@ L928-929 verbatim
/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instConstantEulerGraph1 : NormedAddCommGroup Space := inferInstance

-- @@ L930-931 verbatim
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instConstantEulerGraph2 : NormedSpace ℝ Space := inferInstance

-- @@ L932-933 verbatim
/-- Cache the standard `NormedAddCommGroup LiftTangent` instance to shorten typeclass synthesis. -/
local instance instConstantEulerGraph3 : NormedAddCommGroup LiftTangent := inferInstance

-- @@ L934-935 verbatim
/-- Cache the standard `NormedSpace ℝ LiftTangent` instance to shorten typeclass synthesis. -/
local instance instConstantEulerGraph4 : NormedSpace ℝ LiftTangent := inferInstance


-- @@ L937-940 verbatim
/-- Inclusion, given by `(ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.inl ℝ Space
ℝ)`. -/
def inclusion : (ℝ × Space) →L[ℝ] (ℝ × LiftTangent) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.inl ℝ Space ℝ)


-- @@ L942-942 verbatim
@[simp] theorem inclusion_apply (t : ℝ) (x : Space) : inclusion (t,x)=(t,(x,0)) := rfl


-- @@ L944-945 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 < T} {F R : FieldTower P T}
  {B : Budget P hT (data P F R)} (S : ExactLiftedPacket P hT (data P F R) B)


-- @@ L947-948 verbatim
/-- Velocity, given by `S.rawVelocity (q.1,(q.2,0))`. -/
def velocity (q : ℝ × Space) : Space := S.rawVelocity (q.1,(q.2,0))

-- @@ L949-950 verbatim
/-- Pressure, given by `S.rawGraphPotential 1 q`. -/
def pressure (q : ℝ × Space) : ℝ := S.rawGraphPotential 1 q

-- @@ L951-952 verbatim
/-- Force, given by `S.rawPressure (q.1,(q.2,0))`. -/
def force (q : ℝ × Space) : Space := S.rawPressure (q.1,(q.2,0))


-- @@ L954-960 verbatim
theorem velocity_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    HasFDerivAt (velocity S)
      ((fderiv ℝ S.rawVelocity (t,(x,0))).comp inclusion) (t,x) := by
  have hu := (S.rawVelocity_hasFDerivAt t ht (x,0)).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (inclusion : ℝ × Space → ℝ × LiftTangent) inclusion (t,x) :=
    inclusion.hasFDerivAt
  exact hu.comp (t,x) hi


-- @@ L962-969 verbatim
theorem velocity_joint_continuous : Continuous (velocity S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (Function.uncurry S.velocity.pointField ∘
    fun q : ℝ × Space => (projIcc 0 T hT.le q.1, coveringMap P (q.2,0)))
  exact S.velocity.pointField_joint_continuous.comp
    ((hc.comp continuous_fst).prodMk
      ((EulerLiftedGradientSpace.coveringMap_isOpenQuotient P).continuous.comp
        (continuous_snd.prodMk continuous_const)))


-- @@ L971-978 verbatim
theorem force_joint_continuous : Continuous (force S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (Function.uncurry S.pressure.pointField ∘
    fun q : ℝ × Space => (projIcc 0 T hT.le q.1, coveringMap P (q.2,0)))
  exact S.pressure.pointField_joint_continuous.comp
    ((hc.comp continuous_fst).prodMk
      ((EulerLiftedGradientSpace.coveringMap_isOpenQuotient P).continuous.comp
        (continuous_snd.prodMk continuous_const)))


-- @@ L980-986 verbatim
theorem pressure_joint_continuous : Continuous (pressure S) := by
  have hc : Continuous (projIcc 0 T hT.le) := continuous_projIcc
  change Continuous (fun q : ℝ × Space => S.graphPotential 1 (projIcc 0 T hT.le q.1) q.2)
  have hi : Continuous (fun q : ℝ × Space => (projIcc 0 T hT.le q.1,q.2)) :=
    (hc.comp continuous_fst).prodMk continuous_snd
  have hh := (S.graphPotential_joint_continuous 1).comp hi
  exact hh


-- @@ L988-989 verbatim
theorem pressure_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => pressure S (t,x)) :=
  S.rawGraphPotential_smooth 1 (by norm_num [data]) t


-- @@ L991-994 verbatim
theorem pressure_gradient (t : ℝ) (x : Space) :
    _root_.gradient (fun y => pressure S (t,y)) x=force S (t,x) := by
  have h := S.rawGraphPotential_gradient 1 (by norm_num [data]) t x
  simpa only [data,pressure,force,one_smul,inner_zero_left,mul_zero] using h


-- @@ L996-997 verbatim
theorem pressure_zero (t : ℝ) : pressure S (t,0)=0 :=
  S.graphPotential_zero 1 (projIcc 0 T hT.le t)


-- @@ L999-1004 verbatim
theorem velocity_divergence (t : ℝ) (x : Space) :
    divergence (fun y => velocity S (t,y)) x=0 := by
  rw [divergence_eq_coordinate_sum]
  have h := S.graphVelocity_divergence 1 (by norm_num [data]) (projIcc 0 T hT.le t) x
  simpa only [velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    cylinderGraph,coveringMap,data,inner_zero_left,mul_zero] using h


-- @@ L1006-1016 verbatim
theorem momentum (t : ℝ) (ht : t ∈ Ioo 0 T) (x : Space) :
    momentumResidual (velocity S) (pressure S) (t,x)=0 := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt S t ht x).fderiv,comp_apply,inclusion_apply,pressure_gradient]
  have h := S.raw_normalized_equation t ht (x,0)
  simp only [data,tower,coefficient,zero_apply,smul_zero,Finset.sum_const_zero,
    add_zero,transportDirection,one_smul,inner_zero_left,id_apply] at h
  have hd : (1,(velocity S (t,x),0)) =
      ((1,0) : ℝ × LiftTangent)+(0,(velocity S (t,x),0)) := by simp
  rw [hd,map_add]
  exact h


-- @@ L1018-1022 verbatim
/-- Field, bundling `field`, `smooth`, `integrable`. -/
def field (t : Icc (0 : ℝ) T) : SmoothL2Field Space where
  field := S.velocity.physicalPointField 1 0 t
  smooth := S.velocity.physicalPointField_smooth 1 0 t
  integrable n := S.velocity.physicalTensor_memLp 1 0 n t


-- @@ L1024-1028 verbatim
theorem field_apply (t : Icc (0 : ℝ) T) (x : Space) :
    (field S t).field x=velocity S (t,x) := by
  simp only [field,FieldTower.physicalPointField,EulerCylinderPhysicalTensor.physicalField,
    velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,cylinderGraph,
    coveringMap,projIcc_of_mem hT.le t.property,inner_zero_left,mul_zero]


-- @@ L1030-1033 verbatim
theorem field_jetLp (n : ℕ) (t : Icc (0 : ℝ) T) :
    (field S t).jetLp n=S.velocity.physicalTensorPath 1 0 n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans (S.velocity.physicalTensorPath_ae 1 0 n t).symm


-- @@ L1035-1037 verbatim
theorem field_jetLp_continuous (n : ℕ) : Continuous (fun t => (field S t).jetLp n) := by
  simp only [field_jetLp]
  exact (S.velocity.physicalTensorPath 1 0 n).continuous


-- @@ L1039-1044 verbatim
theorem velocity_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => velocity S (t,x)) := by
  have h := S.velocity.physicalPointField_smooth 1 0 (projIcc 0 T hT.le t)
  change ContDiff ℝ ∞ (fun x => S.velocity.pointField (projIcc 0 T hT.le t) (cylinderGraph P 1 0
      x)) at h
  simpa only [cylinderGraph,inner_zero_left,mul_zero,velocity,ExactLiftedPacket.rawVelocity,
    FieldTower.rawField,coveringMap] using h


-- @@ L1046-1051 verbatim
theorem force_smooth (t : ℝ) : ContDiff ℝ ∞ (fun x => force S (t,x)) := by
  have h := S.pressure.physicalPointField_smooth 1 0 (projIcc 0 T hT.le t)
  change ContDiff ℝ ∞ (fun x => S.pressure.pointField (projIcc 0 T hT.le t) (cylinderGraph P 1 0
      x)) at h
  simpa only [cylinderGraph,inner_zero_left,mul_zero,force,ExactLiftedPacket.rawPressure,
    FieldTower.rawField,coveringMap] using h


-- @@ L1053-1053 verbatim
end EulerConstantEuler


-- @@ L1055-1055 verbatim
end

-- @@ L1056-1056 verbatim
end


-- @@ L1058-1058 verbatim
end


-- @@ L1060-1060 verbatim
section


-- @@ L1062-1063 verbatim
/-! The genuine Euler time/amplitude scaling. A solution starting from
ε u₀ on [0,1] gives a solution starting from u₀ on [0,ε]. -/


-- @@ L1065-1065 verbatim
@[expose] public section


-- @@ L1067-1067 verbatim
noncomputable section


-- @@ L1069-1069 verbatim
namespace EulerTimeRescaling


-- @@ L1071-1071 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerLagrangian


-- @@ L1073-1073 verbatim
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L1075-1078 verbatim
/-- Coordinates, given by `((ε⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (fst ℝ ℝ E)).prod (snd ℝ ℝ
E)`. -/
def coordinates (ε : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  ((ε⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (fst ℝ ℝ E)).prod (snd ℝ ℝ E)


-- @@ L1080-1082 verbatim
omit [CompleteSpace E] in
@[simp] theorem coordinates_apply (ε : ℝ) (q : ℝ × E) :
    coordinates ε q=(ε⁻¹*q.1,q.2) := rfl


-- @@ L1084-1086 verbatim
/-- Velocity, given by `ε⁻¹ • u (coordinates ε q)`. -/
def velocity (ε : ℝ) (u : ℝ × E → E) (q : ℝ × E) : E :=
  ε⁻¹ • u (coordinates ε q)


-- @@ L1088-1090 verbatim
/-- Pressure, given by `(ε⁻¹)^2*p (coordinates ε q)`. -/
def pressure (ε : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E) : ℝ :=
  (ε⁻¹)^2*p (coordinates ε q)


-- @@ L1092-1097 verbatim
omit [CompleteSpace E] in
theorem velocity_hasFDerivAt (ε : ℝ) (u : ℝ × E → E) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q)) :
    HasFDerivAt (velocity ε u)
      (ε⁻¹ • (fderiv ℝ u (coordinates ε q)).comp (coordinates ε)) q :=
  (hu.hasFDerivAt.comp q (coordinates (E := E) ε).hasFDerivAt).const_smul ε⁻¹


-- @@ L1099-1109 verbatim
theorem pressure_gradient (ε : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹ * q.1, y)) q.2) :
    gradient (fun y => pressure ε p (q.1,y)) q.2 =
      (ε⁻¹)^2 • gradient (fun y => p (ε⁻¹*q.1,y)) q.2 := by
  have hs := hp.hasFDerivAt.const_smul ((ε⁻¹)^2)
  change HasFDerivAt (fun y => (ε⁻¹)^2 • p (ε⁻¹*q.1,y)) _ q.2 at hs
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (fun y => (ε⁻¹)^2 • p (ε⁻¹*q.1,y)) q.2) v = _
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,hs.fderiv]
  rfl


-- @@ L1111-1123 verbatim
theorem momentumResidual_eq (ε : ℝ) (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q))
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹ * q.1, y)) q.2) :
    momentumResidual (velocity ε u) (pressure ε p) q =
      (ε⁻¹)^2 • momentumResidual u p (coordinates ε q) := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt ε u q hu).fderiv,pressure_gradient ε p q hp]
  simp only [smul_apply,comp_apply]
  have hd : coordinates ε ((1 : ℝ),velocity ε u q) =
      ε⁻¹ • (1,u (coordinates ε q)) := by
    simp only [coordinates_apply,velocity,Prod.smul_mk,smul_eq_mul,mul_one]
  rw [hd,map_smul,smul_smul,← pow_two,← smul_add]
  rfl


-- @@ L1125-1130 verbatim
theorem momentumResidual_zero (ε : ℝ) (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q))
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹ * q.1, y)) q.2)
    (he : momentumResidual u p (coordinates ε q) = 0) :
    momentumResidual (velocity ε u) (pressure ε p) q=0 := by
  rw [momentumResidual_eq ε u p q hu hp,he,smul_zero]


-- @@ L1132-1137 verbatim
omit [CompleteSpace E] in
theorem spatial_derivative (ε : ℝ) (u : ℝ × E → E) (t : ℝ) (x : E)
    (hu : DifferentiableAt ℝ (fun y => u (ε⁻¹ * t, y)) x) :
    fderiv ℝ (fun y => velocity ε u (t,y)) x =
      ε⁻¹ • fderiv ℝ (fun y => u (ε⁻¹*t,y)) x :=
  (hu.hasFDerivAt.const_smul ε⁻¹).fderiv


-- @@ L1139-1142 verbatim
/-- Time map, bundling `toFun`, `continuous_toFun`. -/
def timeMap (ε : ℝ) (hε : 0 < ε) : C(Icc (0 : ℝ) ε,Icc (0 : ℝ) 1) where
  toFun t := ⟨t/ε,div_nonneg t.property.1 hε.le,(div_le_one hε).mpr t.property.2⟩
  continuous_toFun := (continuous_subtype_val.div_const ε).subtype_mk _


-- @@ L1144-1147 verbatim
theorem timeMap_initial (ε : ℝ) (hε : 0 < ε) :
    timeMap ε hε ⟨0,le_rfl,hε.le⟩=⟨0,le_rfl,by norm_num⟩ := by
  apply Subtype.ext
  exact zero_div ε


-- @@ L1149-1152 verbatim
theorem scaled_time_interior (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Ioo 0 ε) :
    ε⁻¹*t ∈ Ioo (0 : ℝ) 1 := by
  rw [mul_comm,← div_eq_mul_inv]
  exact ⟨div_pos ht.1 hε,(div_lt_one hε).mpr ht.2⟩


-- @@ L1154-1154 verbatim
end EulerTimeRescaling


-- @@ L1156-1156 verbatim
end

-- @@ L1157-1157 verbatim
end


-- @@ L1159-1159 verbatim
end


-- @@ L1161-1161 verbatim
section


-- @@ L1163-1166 verbatim
/-! A positive-time classical Euler solution constructed from a genuine
solenoidal Gevrey datum. The initial velocity is the original datum, not
its small multiple. All spatial derivative tensors remain continuous L²
paths after the actual Euler time/amplitude rescaling. -/


-- @@ L1168-1168 verbatim
@[expose] public section


-- @@ L1170-1170 verbatim
noncomputable section


-- @@ L1172-1172 verbatim
namespace EulerStaticEuler


-- @@ L1174-1176 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerVolterraConvolution EulerSobolevPointEvaluation EulerLagrangian

-- @@ L1177-1177 verbatim
open scoped ContDiff


-- @@ L1179-1180 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L1182-1186 verbatim
/-- Local velocity, given by `EulerTimeRescaling.velocity (amplitude P C R hC hR)
(EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv))`. -/
def localVelocity : ℝ × Space → Space :=
  EulerTimeRescaling.velocity (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv))


-- @@ L1188-1192 verbatim
/-- Local pressure, given by `EulerTimeRescaling.pressure (amplitude P C R hC hR)
(EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv))`. -/
def localPressure : ℝ × Space → ℝ :=
  EulerTimeRescaling.pressure (amplitude P C R hC hR)
    (EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv))


-- @@ L1194-1198 verbatim
/-- Local force as an element of `Space`. -/
def localForce (q : ℝ × Space) : Space :=
  ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q)


-- @@ L1200-1215 verbatim
theorem unit_initial (x : Space) :
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (0,x) =
      amplitude P C R hC hR • u.field x := by
  have hh := congrArg (pointEvaluation P (x,(0 : AddCircle P)))
    (exactPacket_initial P u C R hC hR hu hdiv 3)
  change (exactPacket P u C R hC hR hu hdiv).velocity.pointField
      ⟨0,le_rfl,by norm_num⟩ (x,0) =
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.pointField
      ⟨0,le_rfl,by norm_num⟩ (x,0) at hh
  have hr := ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC
      hR)).toFieldTower_pointField_raw
    ⟨0,le_rfl,by norm_num⟩ x 0
  change _ = amplitude P C R hC hR • u.field x at hr
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,by norm_num⟩
  simpa only [EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    projIcc_of_mem zero_le_one h0,coveringMap,AddCircle.coe_zero] using hh.trans hr


-- @@ L1217-1223 verbatim
theorem localVelocity_initial (x : Space) : localVelocity P u C R hC hR hu hdiv (0,x)=u.field x :=
    by
  change (amplitude P C R hC hR)⁻¹ •
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) (0,x)) = _
  rw [EulerTimeRescaling.coordinates_apply,mul_zero,unit_initial,smul_smul,
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne',one_smul]


-- @@ L1225-1235 verbatim
theorem localMomentum (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    momentumResidual (localVelocity P u C R hC hR hu hdiv)
      (localPressure P u C R hC hR hu hdiv) (t,x)=0 := by
  have hs := EulerTimeRescaling.scaled_time_interior (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) t ht
  exact EulerTimeRescaling.momentumResidual_zero (amplitude P C R hC hR) _ _ (t,x)
    (EulerConstantEuler.velocity_hasFDerivAt (exactPacket P u C R hC hR hu hdiv) _ hs
        x).differentiableAt
    ((EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
    (EulerConstantEuler.momentum (exactPacket P u C R hC hR hu hdiv) _ hs x)


-- @@ L1237-1244 verbatim
theorem localVelocity_differentiableAt (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    DifferentiableAt ℝ (localVelocity P u C R hC hR hu hdiv) (t,x) := by
  have hs := EulerTimeRescaling.scaled_time_interior (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) t ht
  exact (EulerTimeRescaling.velocity_hasFDerivAt (amplitude P C R hC hR) _ (t,x)
    (EulerConstantEuler.velocity_hasFDerivAt (exactPacket P u C R hC hR hu hdiv) _ hs
        x).differentiableAt).differentiableAt


-- @@ L1246-1259 verbatim
theorem localVelocity_divergence (t : ℝ) (x : Space) :
    divergence (fun y => localVelocity P u C R hC hR hu hdiv (t,y)) x=0 := by
  rw [divergence_eq_coordinate_sum]
  have hd := EulerTimeRescaling.spatial_derivative (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)) t x
    ((EulerConstantEuler.velocity_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
  change (∑ i : Fin 3, (fderiv ℝ (fun y => EulerTimeRescaling.velocity (amplitude P C R hC hR)
    (EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)) (t,y)) x
      (EuclideanSpace.single i 1)) i)=0
  rw [hd]
  simp only [smul_apply,PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum,
    ← divergence_eq_coordinate_sum]
  erw [EulerConstantEuler.velocity_divergence,mul_zero]


-- @@ L1261-1267 verbatim
theorem localVelocity_joint_continuous : Continuous (localVelocity P u C R hC hR hu hdiv) := by
  change Continuous (fun q => (amplitude P C R hC hR)⁻¹ •
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.velocity_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      ((amplitude P C R hC hR)⁻¹)


-- @@ L1269-1275 verbatim
theorem localPressure_joint_continuous : Continuous (localPressure P u C R hC hR hu hdiv) := by
  change Continuous (fun q => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.pressure_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      (((amplitude P C R hC hR)⁻¹)^2)


-- @@ L1277-1283 verbatim
theorem localForce_joint_continuous : Continuous (localForce P u C R hC hR hu hdiv) := by
  change Continuous (fun q => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.coordinates (amplitude P C R hC hR) q))
  exact ((EulerConstantEuler.force_joint_continuous (exactPacket P u C R hC hR hu hdiv)).comp
    (EulerTimeRescaling.coordinates (E := Space) (amplitude P C R hC hR)).continuous).const_smul
      (((amplitude P C R hC hR)⁻¹)^2)


-- @@ L1285-1293 verbatim
theorem localPressure_gradient (t : ℝ) (x : Space) :
    _root_.gradient (fun y => localPressure P u C R hC hR hu hdiv (t,y)) x =
      localForce P u C R hC hR hu hdiv (t,x) := by
  have h := EulerTimeRescaling.pressure_gradient (amplitude P C R hC hR)
    (EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv)) (t,x)
    ((EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).differentiable (by
        simp) x)
  erw [EulerConstantEuler.pressure_gradient] at h
  exact h


-- @@ L1295-1299 verbatim
theorem localPressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun x => localPressure P u C R hC hR hu hdiv (t,x)) := by
  change ContDiff ℝ ∞ (fun x => ((amplitude P C R hC hR)⁻¹)^2 •
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*t,x))
  exact (EulerConstantEuler.pressure_smooth (exactPacket P u C R hC hR hu hdiv) _).const_smul _


-- @@ L1301-1304 verbatim
theorem localPressure_zero (t : ℝ) : localPressure P u C R hC hR hu hdiv (t,0)=0 := by
  change ((amplitude P C R hC hR)⁻¹)^2 *
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (_,0)=0
  erw [EulerConstantEuler.pressure_zero,mul_zero]


-- @@ L1306-1310 verbatim
/-- Local field, constructed using `SmoothL2Field.mapField`. -/
def localField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField ((amplitude P C R hC hR)⁻¹ • ContinuousLinearMap.id ℝ Space)
    (EulerConstantEuler.field (exactPacket P u C R hC hR hu hdiv)
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))


-- @@ L1312-1321 verbatim
theorem localField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localField P u C R hC hR hu hdiv t).field x=localVelocity P u C R hC hR hu hdiv (t,x) := by
  change (amplitude P C R hC hR)⁻¹ •
    (EulerConstantEuler.field (exactPacket P u C R hC hR hu hdiv) _).field x = _
  erw [EulerConstantEuler.field_apply]
  change (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]


-- @@ L1323-1327 verbatim
theorem localField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (localField P u C R hC hR hu hdiv t).jetLp n) :=
  SmoothL2Field.continuous_jetLp_mapField _ _
    (fun n => (EulerConstantEuler.field_jetLp_continuous (exactPacket P u C R hC hR hu hdiv) n).comp
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)).continuous) n


-- @@ L1329-1335 verbatim
theorem localVelocity_smooth (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    ContDiff ℝ ∞ (fun x => localVelocity P u C R hC hR hu hdiv (t,x)) := by
  have he : (localField P u C R hC hR hu hdiv t).field =
      fun x => localVelocity P u C R hC hR hu hdiv (t,x) :=
    funext (localField_apply P u C R hC hR hu hdiv t)
  rw [← he]
  exact (localField P u C R hC hR hu hdiv t).smooth


-- @@ L1337-1337 verbatim
end EulerStaticEuler


-- @@ L1339-1339 verbatim
end

-- @@ L1340-1340 verbatim
end


-- @@ L1342-1342 verbatim
end


-- @@ L1344-1344 verbatim
section


-- @@ L1346-1349 verbatim
/-! The locally constructed ordinary Euler solution supplies a concrete
first parent, its label budget and its genuine particle inverse. All
constants and the positive common horizon depend only on the input
Gevrey envelope, not on the particular initial datum. -/


-- @@ L1351-1351 verbatim
section


-- @@ L1353-1355 verbatim
/-! Actual smooth coefficient paths and their true time derivatives under
the Euler amplitude/time scaling. The time interval is shortened by the
same positive amplitude used to normalize the initial velocity. -/


-- @@ L1357-1357 verbatim
@[expose] public section


-- @@ L1359-1359 verbatim
noncomputable section


-- @@ L1361-1361 verbatim
namespace EulerTimeRescaling


-- @@ L1363-1363 verbatim
open Set ContinuousLinearMap EulerVolterraConvolution

-- @@ L1364-1364 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1366-1367 verbatim
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L1369-1372 verbatim
/-- Coefficient, given by `(A.compTime (timeMap ε hε)).map (ε⁻¹ • ContinuousLinearMap.id ℝ V)`. -/
def coefficient (ε : ℝ) (hε : 0 < ε) (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) :
    SmoothTimeField (Icc (0 : ℝ) ε) E V :=
  (A.compTime (timeMap ε hε)).map (ε⁻¹ • ContinuousLinearMap.id ℝ V)


-- @@ L1374-1378 verbatim
/-- Derivative coefficient, given by `(A.compTime (timeMap ε hε)).map ((ε⁻¹)^2 •
ContinuousLinearMap.id ℝ V)`. -/
def derivativeCoefficient (ε : ℝ) (hε : 0 < ε) (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) :
    SmoothTimeField (Icc (0 : ℝ) ε) E V :=
  (A.compTime (timeMap ε hε)).map ((ε⁻¹)^2 • ContinuousLinearMap.id ℝ V)


-- @@ L1380-1406 verbatim
theorem coefficient_time (ε : ℝ) (hε : 0 < ε)
    (A A₁ : SmoothTimeField (Icc (0 : ℝ) 1) E V)
    (h : SmoothTimeField.TimeDerivative 1 zero_le_one A A₁) :
    SmoothTimeField.TimeDerivative ε hε.le (coefficient ε hε A) (derivativeCoefficient ε hε A₁) :=
        by
  intro t x
  have hmap : MapsTo (fun s : ℝ => s/ε) (Icc (0 : ℝ) ε) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hε.le,(div_le_one hε).mpr hs.2⟩
  have ho : HasDerivWithinAt (fun r => A.realField 1 zero_le_one r x)
      (A₁.field (timeMap ε hε t) x) (Icc (0 : ℝ) 1) ((t : ℝ)/ε) :=
    h (timeMap ε hε t) x
  have hi : HasDerivWithinAt (fun r : ℝ => r/ε) (1/ε) (Icc (0 : ℝ) ε) t := by
    simpa only [id_eq] using ((hasDerivAt_id (t : ℝ)).div_const ε).hasDerivWithinAt
  have hd : HasDerivWithinAt
      (fun r => ε⁻¹ • A.realField 1 zero_le_one (r/ε) x)
      (ε⁻¹ • ((1/ε) • A₁.field (timeMap ε hε t) x)) (Icc (0 : ℝ) ε) t :=
    (ho.scomp (h := fun r : ℝ => r / ε) (t : ℝ) hi hmap).const_smul ε⁻¹
  simp only [one_div,smul_smul,← pow_two] at hd
  have he (r : ℝ) (hr : r ∈ Icc (0 : ℝ) ε) :
      (coefficient ε hε A).realField ε hε.le r x =
        ε⁻¹ • A.realField 1 zero_le_one (r/ε) x := by
    simp only [coefficient,SmoothTimeField.realField,extendPath,projIcc_of_mem hε.le hr,
      SmoothTimeField.map_apply,smul_apply,id_apply,SmoothTimeField.compTime_apply,
      projIcc_of_mem zero_le_one (hmap hr)]
    rfl
  exact hd.congr_of_mem he t.property


-- @@ L1408-1408 verbatim
end EulerTimeRescaling


-- @@ L1410-1410 verbatim
end

-- @@ L1411-1411 verbatim
end


-- @@ L1413-1413 verbatim
end


-- @@ L1415-1415 verbatim
section


-- @@ L1417-1419 verbatim
/-! The constructed static-datum solution and its actual time derivative
have smooth bounded spatial jets continuous in time. This includes the
one-sided derivatives at both endpoints. -/


-- @@ L1421-1421 verbatim
@[expose] public section


-- @@ L1423-1423 verbatim
noncomputable section


-- @@ L1425-1425 verbatim
namespace EulerStaticEuler


-- @@ L1427-1429 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerPacketCylinderField EulerAllOrderDriftCorrection
  EulerAllOrderCorrectionData EulerVolterraConvolution

-- @@ L1430-1430 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1432-1433 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L1435-1439 verbatim
/-- Unit velocity coefficient as an element of `SmoothTimeField (Icc (0 : ℝ) 1) Space Space`. -/
def unitVelocityCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)


-- @@ L1441-1445 verbatim
/-- Unit derivative coefficient as an element of `SmoothTimeField (Icc (0 : ℝ) 1) Space Space`. -/
def unitDerivativeCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  ((correctionBudget P u C R hC hR hu hdiv).packetDerivativeCoefficient P
    ((Field.zero P 1).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)


-- @@ L1447-1451 verbatim
/-- Unit force coefficient, given by `(exactPacket P u C R hC hR hu
hdiv).pressure.toSmoothTimeField.precompLinear (ContinuousLinearMap.inl ℝ Space ℝ)`. -/
def unitForceCoefficient : SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  (exactPacket P u C R hC hR hu hdiv).pressure.toSmoothTimeField.precompLinear
    (ContinuousLinearMap.inl ℝ Space ℝ)


-- @@ L1453-1461 verbatim
theorem unitCoefficient_time :
    SmoothTimeField.TimeDerivative 1 zero_le_one
      (unitVelocityCoefficient P u C R hC hR hu hdiv)
      (unitDerivativeCoefficient P u C R hC hR hu hdiv) :=
  ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient_timeDerivative P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))
    ((Field.zero P 1).smul (amplitude P C R hC hR))
    ((EulerStaticCylinder.field_time P 1 u zero_le_one).smul (amplitude P C R hC hR))).precompLinear
      (ContinuousLinearMap.inl ℝ Space ℝ)


-- @@ L1463-1473 verbatim
theorem unitVelocityCoefficient_apply (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field t x =
      EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  have h := (correctionBudget P u C R hC hR hu hdiv).packetCoefficient_eq_corrected P
    ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)) rfl t (x,0)
  change ((correctionBudget P u C R hC hR hu hdiv).packetCoefficient P
      ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR))).field t (x,0) =
    ((correctionBudget P u C R hC hR hu hdiv).correctedFieldTower P).pointField
      (projIcc 0 1 zero_le_one t) (coveringMap P (x,0))
  rw [projIcc_of_mem zero_le_one t.property]
  exact h


-- @@ L1475-1480 verbatim
theorem unitForceCoefficient_apply (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitForceCoefficient P u C R hC hR hu hdiv).field t x =
      EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  simp only [unitForceCoefficient,SmoothTimeField.precompLinear_apply,inl_apply,
    FieldTower.toSmoothTimeField_apply,EulerConstantEuler.force,ExactLiftedPacket.rawPressure,
    FieldTower.rawField,projIcc_of_mem zero_le_one t.property]


-- @@ L1482-1486 verbatim
/-- Velocity coefficient, given by `EulerTimeRescaling.coefficient (amplitude P C R hC hR)
(amplitude_pos P C R hC hR) (unitVelocityCoefficient P u C R hC hR hu hdiv)`. -/
def velocityCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.coefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitVelocityCoefficient P u C R hC hR hu hdiv)


-- @@ L1488-1491 verbatim
/-- Derivative coefficient, constructed using `EulerTimeRescaling.derivativeCoefficient`. -/
def derivativeCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.derivativeCoefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitDerivativeCoefficient P u C R hC hR hu hdiv)


-- @@ L1493-1496 verbatim
/-- Force coefficient, constructed using `EulerTimeRescaling.derivativeCoefficient`. -/
def forceCoefficient : SmoothTimeField (Icc (0 : ℝ) (amplitude P C R hC hR)) Space Space :=
  EulerTimeRescaling.derivativeCoefficient (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (unitForceCoefficient P u C R hC hR hu hdiv)


-- @@ L1498-1502 verbatim
theorem coefficient_time :
    SmoothTimeField.TimeDerivative (amplitude P C R hC hR) (amplitude_pos P C R hC hR).le
      (velocityCoefficient P u C R hC hR hu hdiv) (derivativeCoefficient P u C R hC hR hu hdiv) :=
  EulerTimeRescaling.coefficient_time (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    _ _ (unitCoefficient_time P u C R hC hR hu hdiv)


-- @@ L1504-1504 verbatim
end EulerStaticEuler


-- @@ L1506-1506 verbatim
end

-- @@ L1507-1507 verbatim
end


-- @@ L1509-1509 verbatim
end


-- @@ L1511-1511 verbatim
section


-- @@ L1513-1516 verbatim
/-! Uniform source-only Gevrey bounds for the actual local Euler solution
and its genuine time derivative. The same spatial radius works for sup
and ordinary L² norms. All constants depend only on P,C,R, not on the
particular solenoidal datum realizing the input bounds. -/


-- @@ L1518-1518 verbatim
section


-- @@ L1520-1522 verbatim
/-! Explicit bounds for the constructed small-data solution. All constants
are functions of the datum's supplied Gevrey bounds and the fixed period;
none depends on which datum realizes those bounds. -/


-- @@ L1524-1524 verbatim
@[expose] public section


-- @@ L1526-1526 verbatim
noncomputable section


-- @@ L1528-1528 verbatim
namespace EulerStaticEuler


-- @@ L1530-1532 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpTranslation
  EulerAllOrderDriftCorrection EulerAllOrderCorrectionData EulerSobolevGevreyOperators
  EulerGevreyCorrectionSourceBounds EulerGevreyMetricEstimate EulerConstantCorrection


-- @@ L1534-1535 verbatim
/-- A fixed positive radius retained by the actual correction. -/
def retainedRadius (R : ℝ) : ℝ := EulerSmallCorrection.initialRadius (mixedRadius R)/4


-- @@ L1537-1538 verbatim
/-- Base error factor, given by `metricAmplification 1/2`. -/
def baseErrorFactor : ℝ := metricAmplification 1/2


-- @@ L1540-1541 verbatim
theorem retainedRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < retainedRadius R :=
  div_pos (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)) (by norm_num)


-- @@ L1543-1549 verbatim
theorem retainedRadius_small (R : ℝ) (hR : 0 ≤ R) :
    retainedRadius R*mixedRadius R ≤ 1/2 := by
  have h := EulerSmallCorrection.initialRadius_mul _ (mixedRadius_nonneg R hR)
  have hn := mul_nonneg (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)).le
    (mixedRadius_nonneg R hR)
  dsimp [retainedRadius]
  linarith


-- @@ L1551-1553 verbatim
theorem baseErrorFactor_nonneg : 0 ≤ baseErrorFactor :=
  div_nonneg (zero_le_one.trans (metricAmplification_one_le (by
      norm_num : (0 : ℝ) < 1))) (by norm_num)


-- @@ L1555-1555 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L1557-1561 verbatim
/-- Static source cost, given by `sourceBound P 1 1 0 0 1 baseErrorFactor
((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)`. -/
def staticSourceCost (R : ℝ) : ℝ :=
  sourceBound P 1 1 0 0 1 baseErrorFactor
    ((8/EulerSmallCorrection.initialRadius (mixedRadius R))*baseErrorFactor)


-- @@ L1563-1564 verbatim
/-- Static time cost, given by `(1+2*pressureBound*(448*1+1))*staticSourceCost P R`. -/
def staticTimeCost (R : ℝ) : ℝ := (1+2*pressureBound*(448*1+1))*staticSourceCost P R


-- @@ L1566-1567 verbatim
/-- Static pressure cost, given by `2*pressureBound*staticSourceCost P R`. -/
def staticPressureCost (R : ℝ) : ℝ := 2*pressureBound*staticSourceCost P R


-- @@ L1569-1573 verbatim
theorem staticSourceCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticSourceCost P R :=
  sourceBound_nonneg P zero_le_one zero_le_one le_rfl le_rfl zero_le_one baseErrorFactor_nonneg
    (mul_nonneg (div_nonneg (by norm_num)
      (EulerSmallCorrection.initialRadius_pos _ (mixedRadius_nonneg R hR)).le)
          baseErrorFactor_nonneg)


-- @@ L1575-1579 verbatim
theorem staticTimeCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticTimeCost P R := by
  have hS := staticSourceCost_nonneg P R hR
  have hP := zero_le_one.trans pressureBound_one_le
  unfold staticTimeCost
  positivity


-- @@ L1581-1585 verbatim
theorem staticPressureCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ staticPressureCost P R := by
  have hS := staticSourceCost_nonneg P R hR
  have hP := zero_le_one.trans pressureBound_one_le
  unfold staticPressureCost
  positivity


-- @@ L1587-1588 verbatim
variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L1590-1591 verbatim
theorem budget_retainedRadius :
    (correctionBudget P u C R hC hR hu hdiv).reducedRadius P=retainedRadius R := rfl


-- @@ L1593-1594 verbatim
theorem budget_staticTimeCost (q : ℕ) (hq : 6 ≤ q) :
    (correctionBudget P u C R hC hR hu hdiv).timeDerivativeCost P q hq=staticTimeCost P R := rfl


-- @@ L1596-1597 verbatim
theorem budget_staticPressureCost (q : ℕ) (hq : 6 ≤ q) :
    (correctionBudget P u C R hC hR hu hdiv).pressureCost P q hq=staticPressureCost P R := rfl


-- @@ L1599-1605 verbatim
theorem correction_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).fieldTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*baseErrorFactor := by
  have h := (correctionBudget P u C R hC hR hu hdiv).fieldTower_reducedNorm P (n+6) n le_rfl t
  change _ ≤ metricAmplification 1*(amplitude P C R hC hR/2) at h
  exact h.trans_eq (by unfold baseErrorFactor; ring)


-- @@ L1607-1623 verbatim
theorem exact_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      ((exactPacket P u C R hC hR hu hdiv).velocity.realization (n+6) t) ≤
      amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor) := by
  have hw := EulerSmallCorrection.scaled_word (EulerStaticCylinder.field P 1 u)
    (EulerStaticCylinder.field_wordBound P 1 u 6 C R hC hR hu)
    (amplitude P C R hC hR) (amplitude_pos P C R hC hR).le
  have hb := hw.toFieldTower_weightedNorm_le_two (mixedRadius_nonneg R hR)
    (mul_nonneg (amplitude_pos P C R hC hR).le (mixedAmplitude_nonneg P C R hC hR))
    (n+6) n le_rfl (retainedRadius R) (retainedRadius_pos R hR) (retainedRadius_small R hR) t
  change weightedNorm P 6 n (retainedRadius R)
    (((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.realization
        (n+6) t +
      ((correctionBudget P u C R hC hR hu hdiv).fieldTower P).realization (n+6) t) ≤ _
  apply (weightedNorm_add_le P 6 n le_rfl (retainedRadius R) (retainedRadius_pos R hR) _ _).trans
  exact (add_le_add hb (correction_weighted P u C R hC hR hu hdiv n t)).trans_eq (by
      unfold mixedAmplitude; ring)


-- @@ L1625-1632 verbatim
theorem time_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*staticTimeCost P R := by
  have h := (correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower_reducedNorm_delta
    P (n+6) (by omega) n (by omega) (n+6) le_rfl t
  rw [budget_retainedRadius,budget_staticTimeCost] at h
  exact h.trans_eq (mul_comm _ _)


-- @@ L1634-1641 verbatim
theorem pressure_weighted (n : ℕ) (t : Icc (0 : ℝ) 1) :
    weightedNorm P 6 n (retainedRadius R)
      (((correctionBudget P u C R hC hR hu hdiv).pressureTower P).realization (n+6) t) ≤
      amplitude P C R hC hR*staticPressureCost P R := by
  have h := (correctionBudget P u C R hC hR hu hdiv).pressureTower_reducedNorm_delta
    P (n+6) (by omega) n (by omega) (n+6) le_rfl t
  rw [budget_retainedRadius,budget_staticPressureCost] at h
  exact h.trans_eq (mul_comm _ _)


-- @@ L1643-1643 verbatim
end EulerStaticEuler


-- @@ L1645-1645 verbatim
end

-- @@ L1646-1646 verbatim
end


-- @@ L1648-1648 verbatim
end


-- @@ L1650-1650 verbatim
section


-- @@ L1652-1653 verbatim
/-! Quantitative spatial jet bounds under actual Euler time/amplitude
rescaling. The constants are explicit and the spatial radius is unchanged. -/


-- @@ L1655-1655 verbatim
@[expose] public section


-- @@ L1657-1657 verbatim
noncomputable section


-- @@ L1659-1659 verbatim
namespace EulerTimeRescaling


-- @@ L1661-1661 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation

-- @@ L1662-1662 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1664-1665 verbatim
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L1667-1670 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L1671-1673 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeAmplitudeBounds2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L1674-1677 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))
    := inferInstance

-- @@ L1678-1681 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeAmplitudeBounds4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance


-- @@ L1683-1686 verbatim
theorem smul_id_norm_le (a : ℝ) (ha : 0 ≤ a) : ‖a • ContinuousLinearMap.id ℝ V‖ ≤ a := by
  apply opNorm_le_bound _ ha
  intro v
  simp only [smul_apply,id_apply,norm_smul,Real.norm_of_nonneg ha,le_refl]


-- @@ L1688-1694 verbatim
theorem coefficient_jet_norm (ε : ℝ) (hε : 0 < ε)
    (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) (n : ℕ) :
    ‖(coefficient ε hε A).jet n‖ ≤ ε⁻¹*‖A.jet n‖ := by
  apply ((A.compTime (timeMap ε hε)).map_jet_norm_le
    (ε⁻¹ • ContinuousLinearMap.id ℝ V) n).trans
  exact mul_le_mul (smul_id_norm_le ε⁻¹ (inv_nonneg.mpr hε.le))
    (A.compTime_jet_norm (timeMap ε hε) n) (norm_nonneg _) (inv_nonneg.mpr hε.le)


-- @@ L1696-1702 verbatim
theorem derivativeCoefficient_jet_norm (ε : ℝ) (hε : 0 < ε)
    (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) (n : ℕ) :
    ‖(derivativeCoefficient ε hε A).jet n‖ ≤ (ε⁻¹)^2*‖A.jet n‖ := by
  apply ((A.compTime (timeMap ε hε)).map_jet_norm_le
    ((ε⁻¹)^2 • ContinuousLinearMap.id ℝ V) n).trans
  exact mul_le_mul (smul_id_norm_le ((ε⁻¹)^2) (sq_nonneg _))
    (A.compTime_jet_norm (timeMap ε hε) n) (norm_nonneg _) (sq_nonneg _)


-- @@ L1704-1710 verbatim
theorem mapField_hasJetBound (a : ℝ) (ha : 0 ≤ a) (F : SmoothL2Field V)
    (C R : ℝ) (hF : F.HasJetBound C R) :
    (SmoothL2Field.mapField (a • ContinuousLinearMap.id ℝ V) F).HasJetBound (a*C) R := by
  intro n
  apply (SmoothL2Field.norm_jetLp_map_le _ F n).trans
  apply (mul_le_mul_of_nonneg_right (smul_id_norm_le a ha) (norm_nonneg _)).trans
  exact (mul_le_mul_of_nonneg_left (hF n) ha).trans_eq (by ring)


-- @@ L1712-1712 verbatim
end EulerTimeRescaling


-- @@ L1714-1714 verbatim
end

-- @@ L1715-1715 verbatim
end


-- @@ L1717-1717 verbatim
end


-- @@ L1719-1719 verbatim
@[expose] public section


-- @@ L1721-1721 verbatim
noncomputable section


-- @@ L1723-1723 verbatim
namespace EulerStaticEuler


-- @@ L1725-1727 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerPacketCylinderField

-- @@ L1728-1728 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1730-1731 verbatim
/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instStaticEulerGevrey1 : NormedAddCommGroup Space := inferInstance

-- @@ L1732-1733 verbatim
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instStaticEulerGevrey2 : NormedSpace ℝ Space := inferInstance

-- @@ L1734-1737 verbatim
/-- Cache the standard `NormedAddCommGroup (Space [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instStaticEulerGevrey3 (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) :=
    inferInstance

-- @@ L1738-1741 verbatim
/-- Cache the standard `NormedSpace ℝ (Space [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instStaticEulerGevrey4 (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) :=
    inferInstance

-- @@ L1742-1746 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to
shorten typeclass synthesis. -/
local instance instStaticEulerGevrey5 (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ]
    Space)) :=
    inferInstance

-- @@ L1747-1750 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instStaticEulerGevrey6 (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
    inferInstance


-- @@ L1752-1753 verbatim
/-- Cover radius, given by `‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹`. -/
def coverRadius (R : ℝ) : ℝ := ‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹


-- @@ L1755-1756 verbatim
/-- Output radius, given by `1+4*coverRadius R`. -/
def outputRadius (R : ℝ) : ℝ := 1+4*coverRadius R


-- @@ L1758-1759 verbatim
theorem coverRadius_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ coverRadius R :=
  mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (retainedRadius_pos R hR).le)


-- @@ L1761-1764 verbatim
theorem outputRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < outputRadius R := by
  have h := coverRadius_nonneg R hR
  unfold outputRadius
  positivity


-- @@ L1766-1766 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L1768-1770 verbatim
/-- Graph cost, given by `1+sobolevEmbeddingConstant P 3+Real.sqrt (2/P+2*P)*(1+coverRadius R)`. -/
def graphCost (R : ℝ) : ℝ :=
  1+sobolevEmbeddingConstant P 3+Real.sqrt (2/P+2*P)*(1+coverRadius R)


-- @@ L1772-1774 verbatim
/-- Output velocity size, given by `graphCost P R*(2*mixedAmplitude P C R+baseErrorFactor)`. -/
def outputVelocitySize (C R : ℝ) : ℝ :=
  graphCost P R*(2*mixedAmplitude P C R+baseErrorFactor)


-- @@ L1776-1779 verbatim
/-- Output derivative size, given by `(amplitude P C R hC hR)⁻¹*graphCost P R*staticTimeCost P
R`. -/
def outputDerivativeSize (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  (amplitude P C R hC hR)⁻¹*graphCost P R*staticTimeCost P R


-- @@ L1781-1785 verbatim
theorem graphCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ graphCost P R := by
  have h₁ := sobolevEmbeddingConstant_nonneg P 3
  have h₂ := coverRadius_nonneg R hR
  unfold graphCost
  positivity


-- @@ L1787-1791 verbatim
theorem outputVelocitySize_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ outputVelocitySize P C R :=
  mul_nonneg (graphCost_nonneg P R hR)
    (add_nonneg (mul_nonneg (by
        norm_num) (mixedAmplitude_nonneg P C R hC hR)) baseErrorFactor_nonneg)


-- @@ L1793-1796 verbatim
theorem outputDerivativeSize_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ outputDerivativeSize P C R hC hR := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (amplitude_pos P C R hC hR).le)
    (graphCost_nonneg P R hR)) (staticTimeCost_nonneg P R hR)


-- @@ L1798-1803 verbatim
private theorem graphCost_embedding (R : ℝ) (hR : 0 ≤ R) :
    sobolevEmbeddingConstant P 3 ≤ graphCost P R := by
  have h := mul_nonneg (Real.sqrt_nonneg (2/P+2*P))
    (add_nonneg zero_le_one (coverRadius_nonneg R hR))
  unfold graphCost
  linarith


-- @@ L1805-1809 verbatim
private theorem graphCost_trace (R : ℝ) :
    Real.sqrt (2/P+2*P)*(1+coverRadius R) ≤ graphCost P R := by
  have h := sobolevEmbeddingConstant_nonneg P 3
  unfold graphCost
  linarith


-- @@ L1811-1815 verbatim
private theorem jet_mono {a b r s : ℝ} (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hab : a ≤ b) (hrs : r ≤ s) (n : ℕ) :
    a*r^n*(n.factorial : ℝ)^2 ≤ b*s^n*(n.factorial : ℝ)^2 :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul hab (pow_le_pow_left₀ hr hrs n) (pow_nonneg hr n) hb) (sq_nonneg _)


-- @@ L1817-1818 verbatim
variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L1820-1826 verbatim
theorem unitVelocityCoefficient_graph (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field t x =
      (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphCoefficient.field t x := by
  rw [unitVelocityCoefficient_apply, FieldTower.zeroGraphCoefficient_apply,
      FieldTower.zeroGraphField_apply]
  simp only [EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    projIcc_of_mem zero_le_one t.property]


-- @@ L1828-1836 verbatim
theorem unitDerivativeCoefficient_graph (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitDerivativeCoefficient P u C R hC hR hu hdiv).field t x =
      ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).zeroGraphCoefficient.field t
          x := by
  change ((Field.zero P 1).smul (amplitude P C R hC hR)).toSmoothTimeField.field t (x,0)+_=_
  rw [Field.toSmoothTimeField_apply]
  change amplitude P C R hC hR • (0 : Space)+_=_
  rw [smul_zero,zero_add]
  rfl


-- @@ L1838-1842 verbatim
/-- Local derivative field, constructed using `SmoothL2Field.mapField`. -/
def localDerivativeField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField (((amplitude P C R hC hR)⁻¹)^2 • ContinuousLinearMap.id ℝ Space)
    (((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).zeroGraphField
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))


-- @@ L1844-1853 verbatim
theorem localDerivativeField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localDerivativeField P u C R hC hR hu hdiv t).field x =
      (derivativeCoefficient P u C R hC hR hu hdiv).field t x := by
  simp only [localDerivativeField, derivativeCoefficient,
    EulerTimeRescaling.derivativeCoefficient, SmoothL2Field.mapField_field,
    SmoothTimeField.map_apply, SmoothTimeField.compTime_apply, smul_apply, id_apply]
  have he := unitDerivativeCoefficient_graph P u C R hC hR hu hdiv
    (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t) x
  rw [FieldTower.zeroGraphCoefficient_apply] at he
  exact congrArg (fun v : Space => ((amplitude P C R hC hR)⁻¹)^2 • v) he.symm


-- @@ L1855-1885 verbatim
theorem velocityCoefficient_bound (n : ℕ) :
    ‖(velocityCoefficient P u C R hC hR hu hdiv).jet n‖ ≤
      outputVelocitySize P C R*(outputRadius R)^n*(n.factorial : ℝ)^2 := by
  have hV : 0 ≤ 2*mixedAmplitude P C R+baseErrorFactor :=
    add_nonneg (mul_nonneg (by norm_num) (mixedAmplitude_nonneg P C R hC hR)) baseErrorFactor_nonneg
  have he := (amplitude_pos P C R hC hR).le
  have hunit := (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphCoefficient_bound
    (retainedRadius R) (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))
    (retainedRadius_pos R hR) (mul_nonneg he hV) (exact_weighted P u C R hC hR hu hdiv) n
  rw [← SmoothTimeField.jet_eq_of_field_eq _ _ (unitVelocityCoefficient_graph P u C R hC hR hu
      hdiv) n] at hunit
  have h := (EulerTimeRescaling.coefficient_jet_norm (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) (unitVelocityCoefficient P u C R hC hR hu hdiv) n).trans
    (mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr he))
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  apply h.trans
  calc
    _ = (sobolevEmbeddingConstant P 3*(2*mixedAmplitude P C R+baseErrorFactor)) *
        (coverRadius R)^n*(n.factorial : ℝ)^2 := by
      unfold coverRadius
      calc
        _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR) *
          ((sobolevEmbeddingConstant P 3*(2*mixedAmplitude P C R+baseErrorFactor)) *
            (‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹)^n*(n.factorial :
                ℝ)^2) := by
                ring
        _ = _ := by rw [hi,one_mul]
    _ ≤ _ := jet_mono (outputVelocitySize_nonneg P C R hC hR) (coverRadius_nonneg R hR)
      (mul_le_mul_of_nonneg_right (graphCost_embedding P R hR) hV)
      (by have hc := coverRadius_nonneg R hR; unfold outputRadius; linarith) n


-- @@ L1887-1918 verbatim
theorem derivativeCoefficient_bound (n : ℕ) :
    ‖(derivativeCoefficient P u C R hC hR hu hdiv).jet n‖ ≤
      outputDerivativeSize P C R hC hR*(outputRadius R)^n*(n.factorial : ℝ)^2 := by
  have he := (amplitude_pos P C R hC hR).le
  have hT := staticTimeCost_nonneg P R hR
  have hunit := ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower
      P).zeroGraphCoefficient_bound
    (retainedRadius R) (amplitude P C R hC hR*staticTimeCost P R)
    (retainedRadius_pos R hR) (mul_nonneg he hT) (time_weighted P u C R hC hR hu hdiv) n
  rw [← SmoothTimeField.jet_eq_of_field_eq _ _ (unitDerivativeCoefficient_graph P u C R hC hR hu
      hdiv) n] at hunit
  have h := (EulerTimeRescaling.derivativeCoefficient_jet_norm (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) (unitDerivativeCoefficient P u C R hC hR hu hdiv) n).trans
    (mul_le_mul_of_nonneg_left hunit (sq_nonneg _))
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  apply h.trans
  calc
    _ = ((amplitude P C R hC hR)⁻¹*sobolevEmbeddingConstant P 3*staticTimeCost P R) *
        (coverRadius R)^n*(n.factorial : ℝ)^2 := by
      unfold coverRadius
      calc
        _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR) *
          (((amplitude P C R hC hR)⁻¹*sobolevEmbeddingConstant P 3*staticTimeCost P R) *
            (‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹)^n*(n.factorial :
                ℝ)^2) := by
                ring
        _ = _ := by rw [hi,one_mul]
    _ ≤ _ := jet_mono (outputDerivativeSize_nonneg P C R hC hR) (coverRadius_nonneg R hR)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (graphCost_embedding P R hR) (inv_nonneg.mpr he)) hT)
      (by have hc := coverRadius_nonneg R hR; unfold outputRadius; linarith) n


-- @@ L1920-1951 verbatim
theorem localField_bound (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    (localField P u C R hC hR hu hdiv t).HasJetBound (outputVelocitySize P C R) (outputRadius R) :=
        by
  have hV : 0 ≤ 2*mixedAmplitude P C R+baseErrorFactor :=
    add_nonneg (mul_nonneg (by norm_num) (mixedAmplitude_nonneg P C R hC hR)) baseErrorFactor_nonneg
  have he := (amplitude_pos P C R hC hR).le
  have hunit := (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphField_bound
    (retainedRadius R) (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))
    (retainedRadius_pos R hR) (mul_nonneg he hV) (exact_weighted P u C R hC hR hu hdiv)
    (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t)
  have h := EulerTimeRescaling.mapField_hasJetBound (amplitude P C R hC hR)⁻¹
    (inv_nonneg.mpr he) _ _ _ hunit
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  have ha : (amplitude P C R hC hR)⁻¹ *
      (Real.sqrt (2/P+2*P)*(amplitude P C R hC hR*(2*mixedAmplitude P C
          R+baseErrorFactor))*(1+coverRadius R)) =
      (Real.sqrt (2/P+2*P)*(1+coverRadius R))*(2*mixedAmplitude P C R+baseErrorFactor) := by
    calc
      _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR) *
        ((Real.sqrt (2/P+2*P)*(1+coverRadius R))*(2*mixedAmplitude P C R+baseErrorFactor)) := by
            ring
      _ = _ := by rw [hi,one_mul]
  change (localField P u C R hC hR hu hdiv t).HasJetBound
    ((amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P) *
      (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))*(1+coverRadius R)))
    (4*coverRadius R) at h
  rw [ha] at h
  exact h.mono (by have hc := coverRadius_nonneg R hR; positivity)
    (mul_nonneg (by norm_num) (coverRadius_nonneg R hR))
    (mul_le_mul_of_nonneg_right (graphCost_trace P R) hV)
    (by unfold outputRadius; linarith)


-- @@ L1953-1984 verbatim
theorem localDerivativeField_bound (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    (localDerivativeField P u C R hC hR hu hdiv t).HasJetBound
      (outputDerivativeSize P C R hC hR) (outputRadius R) := by
  have he := (amplitude_pos P C R hC hR).le
  have hT := staticTimeCost_nonneg P R hR
  have hunit := ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower
      P).zeroGraphField_bound
    (retainedRadius R) (amplitude P C R hC hR*staticTimeCost P R)
    (retainedRadius_pos R hR) (mul_nonneg he hT) (time_weighted P u C R hC hR hu hdiv)
    (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t)
  have h := EulerTimeRescaling.mapField_hasJetBound (((amplitude P C R hC hR)⁻¹)^2)
    (sq_nonneg _) _ _ _ hunit
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  have ha : ((amplitude P C R hC hR)⁻¹)^2 *
      (Real.sqrt (2/P+2*P)*(amplitude P C R hC hR*staticTimeCost P R)*(1+coverRadius R)) =
      (amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P)*(1+coverRadius R))*staticTimeCost P R := by
    calc
      _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR) *
        ((amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P)*(1+coverRadius R))*staticTimeCost P R) := by
            ring
      _ = _ := by rw [hi,one_mul]
  change (localDerivativeField P u C R hC hR hu hdiv t).HasJetBound
    (((amplitude P C R hC hR)⁻¹)^2*(Real.sqrt (2/P+2*P) *
      (amplitude P C R hC hR*staticTimeCost P R)*(1+coverRadius R)))
    (4*coverRadius R) at h
  rw [ha] at h
  exact h.mono (by have hc := coverRadius_nonneg R hR; positivity)
    (mul_nonneg (by norm_num) (coverRadius_nonneg R hR))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (graphCost_trace P R) (inv_nonneg.mpr he)) hT)
    (by unfold outputRadius; linarith)


-- @@ L1986-1986 verbatim
end EulerStaticEuler


-- @@ L1988-1988 verbatim
end

-- @@ L1989-1989 verbatim
end


-- @@ L1991-1991 verbatim
end


-- @@ L1993-1993 verbatim
section


-- @@ L1995-1997 verbatim
/-! The genuine ordinary flow of a smooth divergence-free velocity gives
the first parent particle data. Its horizon can be shortened by an explicit
positive amount before applying the uniform flow-jet estimate. -/


-- @@ L1999-1999 verbatim
@[expose] public section


-- @@ L2001-2001 verbatim
noncomputable section


-- @@ L2003-2003 verbatim
namespace EulerBaseEulerParent


-- @@ L2005-2006 verbatim
open Set MeasureTheory EulerSmoothLimit EulerSmoothBanachFlow
  EulerParentPacketFrames EulerVolterraConvolution EulerTimeIntervalRestriction

-- @@ L2007-2007 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L2009-2012 verbatim
/-- Cache the standard `NormedAddCommGroup (Space [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instBaseEulerParent1 (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) :=
    inferInstance

-- @@ L2013-2015 verbatim
/-- Cache the standard `NormedSpace ℝ (Space [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instBaseEulerParent2 (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance

-- @@ L2016-2020 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to
shorten typeclass synthesis. -/
local instance instBaseEulerParent3 (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))
    :=
    inferInstance

-- @@ L2021-2024 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instBaseEulerParent4 (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
    inferInstance


-- @@ L2026-2045 verbatim
/-- Input data, collecting `T`, `T_pos`, `field`, `derivative`, `time_derivative`, `divergence`
and their compatibility conditions. -/
structure Input where
  /-- Time horizon of `Input`, of type `ℝ`. -/
  T : ℝ
  T_pos : 0 < T
  /-- Underlying field of `Input`, of type `SmoothTimeField (Icc (0 : ℝ) T) Space Space`. -/
  field : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  /-- Derivative field of `Input`, of type `SmoothTimeField (Icc (0 : ℝ) T) Space Space`. -/
  derivative : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  time_derivative : SmoothTimeField.TimeDerivative T T_pos.le field derivative
  divergence : ∀ t x, EulerSmoothLimit.divergence (field.field t) x=0
  /-- Bound parameter of `Input`, of type `ℝ`. -/
  B : ℝ
  /-- Radius parameter of `Input`, of type `ℝ`. -/
  R : ℝ
  B_nonneg : 0 ≤ B
  R_pos : 0 < R
  small : B*R*T ≤ 1/8
  bound : ∀ n, ‖field.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2


-- @@ L2047-2047 verbatim
namespace Input


-- @@ L2049-2049 verbatim
variable (I : Input)


-- @@ L2051-2054 verbatim
/-- Displacement, given by `displacementCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg
I.R_pos I.small I.bound`. -/
def displacement : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  displacementCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos I.small I.bound


-- @@ L2056-2058 verbatim
/-- Velocity, given by `I.field.compDisplacement I.displacement`. -/
def velocity : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  I.field.compDisplacement I.displacement


-- @@ L2060-2064 verbatim
/-- Acceleration, given by `accelerationCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg
I.R_pos I.small I.bound I.derivative`. -/
def acceleration : SmoothTimeField (Icc (0 : ℝ) I.T) Space Space :=
  accelerationCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos I.small I.bound
      I.derivative


-- @@ L2066-2067 verbatim
@[simp] theorem displacement_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.displacement.field t x=(flowData I.T I.T_pos.le I.field).forward t x-x := rfl


-- @@ L2069-2076 verbatim
@[simp] theorem velocity_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.velocity.field t x=velocityFamily I.T I.T_pos.le I.field x t := by
  change I.field.field t (x+I.displacement.field t x)=_
  rw [I.displacement_apply]
  have he : x+((flowData I.T I.T_pos.le I.field).forward t x-x) =
      (flowData I.T I.T_pos.le I.field).forward t x := by abel
  rw [he]
  rfl


-- @@ L2078-2081 verbatim
@[simp] theorem acceleration_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.acceleration.field t x=accelerationFamily I.T I.T_pos.le I.field I.derivative x t :=
  accelerationCoefficient_apply I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
    I.small I.bound I.derivative t x


-- @@ L2083-2089 verbatim
theorem displacement_time : SmoothTimeField.TimeDerivative I.T I.T_pos.le
    I.displacement I.velocity := by
  intro t x
  have he : (fun s => I.displacement.realField I.T I.T_pos.le s x) =
      extendPath I.T I.T_pos.le (displacementFamily I.T I.T_pos.le I.field x) := rfl
  rw [he,I.velocity_apply]
  exact displacementFamily_time_derivative I.T I.T_pos.le I.field x t


-- @@ L2091-2099 verbatim
theorem velocity_time : SmoothTimeField.TimeDerivative I.T I.T_pos.le
    I.velocity I.acceleration := by
  intro t x
  have he : (fun s => I.velocity.realField I.T I.T_pos.le s x) =
      extendPath I.T I.T_pos.le (velocityFamily I.T I.T_pos.le I.field x) := by
    funext s
    exact I.velocity_apply (projIcc 0 I.T I.T_pos.le s) x
  rw [he,I.acceleration_apply]
  exact velocityFamily_time_derivative I.T I.T_pos.le I.field I.derivative I.time_derivative x t


-- @@ L2101-2102 verbatim
theorem displacement_initial (x : Space) : I.displacement.field ⟨0,le_rfl,I.T_pos.le⟩ x=0 := by
  rw [I.displacement_apply,(flowData I.T I.T_pos.le I.field).forward_zero,sub_self]


-- @@ L2104-2110 verbatim
theorem displacement_det (t : Icc (0 : ℝ) I.T) (x : Space) :
    (ContinuousLinearMap.id ℝ Space+fderiv ℝ (I.displacement.field t : Space → Space) x).det=1 := by
  rw [← I.displacement.derivativeField_eq t x]
  change ((deformationCoefficient I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
    I.small I.bound).field t x).det=1
  rw [deformationCoefficient_apply]
  exact forward_det_one I.T I.T_pos.le I.field I.divergence t x


-- @@ L2112-2127 verbatim
/-- Parent, bundling `T`, `T_pos`, `ell`, `ell_pos` and the required compatibility proofs. -/
def parent (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) : Parent where
  T := I.T
  T_pos := I.T_pos
  ell := ell
  ell_pos := hell
  ell_le_one := hell1
  displacement := I.displacement
  velocity := I.velocity
  acceleration := I.acceleration
  displacement_time := I.displacement_time
  velocity_time := I.velocity_time
  initial := I.displacement_initial
  determinant t x := by
    rw [EulerPacketVolumeDivergence.operatorMatrix_det]
    exact I.displacement_det t (ell • x)


-- @@ L2129-2134 verbatim
theorem parent_position (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) I.T) (x : Space) :
    (I.parent ell hell hell1).position t x=(flowData I.T I.T_pos.le I.field).forward t x := by
  change x+I.displacement.field t x=_
  rw [I.displacement_apply]
  abel


-- @@ L2136-2150 verbatim
/-- Particle inverse, bundling `field`, `left_inverse`, `right_inverse`, `continuous` and the
required compatibility proofs. -/
def particleInverse (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    ParticleInverse (I.parent ell hell hell1) where
  field t x := (flowData I.T I.T_pos.le I.field).backward t x
  left_inverse t x := by
    erw [I.parent_position ell hell hell1]
    exact (flowData I.T I.T_pos.le I.field).backward_forward t x
  right_inverse t x := by
    erw [I.parent_position ell hell hell1]
    exact (flowData I.T I.T_pos.le I.field).forward_backward t x
  continuous := by
    have hc : Continuous (fun q : Icc (0 : ℝ) I.T × Space => ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (flowData I.T I.T_pos.le I.field).backward_joint_continuous.comp hc


-- @@ L2152-2157 verbatim
theorem parent_velocity (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) I.T) (x : Space) :
    (I.parent ell hell hell1).velocity.field t x =
      I.field.field t ((I.parent ell hell hell1).position t x) := by
  rw [I.parent_position]
  exact I.velocity_apply t x


-- @@ L2159-2159 verbatim
end Input


-- @@ L2161-2162 verbatim
/-- Horizon, given by `min T (1/(8*(1+B*R)))`. -/
def horizon (T B R : ℝ) : ℝ := min T (1/(8*(1+B*R)))


-- @@ L2164-2168 verbatim
theorem horizon_pos (T B R : ℝ) (hT : 0 < T) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    0 < horizon T B R := by
  unfold horizon
  apply lt_min hT
  positivity


-- @@ L2170-2170 verbatim
theorem horizon_le (T B R : ℝ) : horizon T B R ≤ T := min_le_left _ _


-- @@ L2172-2178 verbatim
theorem horizon_small (T B R : ℝ) (hT : 0 < T) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    B*R*horizon T B R ≤ 1/8 := by
  have hp := horizon_pos T B R hT hB hR
  have hd : 0 < 8*(1+B*R) := by positivity
  have he := (le_div_iff₀ hd).1 (min_le_right T (1/(8*(1+B*R))))
  change horizon T B R*(8*(1+B*R)) ≤ 1 at he
  linarith


-- @@ L2180-2199 verbatim
/-- Of interval, bundling `T`, `T_pos`, `field`, `derivative` and the required compatibility
proofs. -/
def ofInterval (T : ℝ) (hT : 0 < T)
    (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) Space Space)
    (htime : SmoothTimeField.TimeDerivative T hT.le A A₁)
    (hdiv : ∀ t x, EulerSmoothLimit.divergence (A.field t) x = 0)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 < R)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2) : Input where
  T := horizon T B R
  T_pos := horizon_pos T B R hT hB hR.le
  field := A.compTime (initialInclusion T (horizon T B R) (horizon_le T B R))
  derivative := A₁.compTime (initialInclusion T (horizon T B R) (horizon_le T B R))
  time_derivative := htime.restrictInitial (horizon_pos T B R hT hB hR.le).le (horizon_le T B R)
  divergence t x := hdiv (initialInclusion T (horizon T B R) (horizon_le T B R) t) x
  B := B
  R := R
  B_nonneg := hB
  R_pos := hR
  small := horizon_small T B R hT hB hR.le
  bound n := (A.compTime_jet_norm _ n).trans (hb n)


-- @@ L2201-2201 verbatim
end EulerBaseEulerParent


-- @@ L2203-2203 verbatim
end

-- @@ L2204-2204 verbatim
end


-- @@ L2206-2206 verbatim
end


-- @@ L2208-2208 verbatim
section


-- @@ L2210-2211 verbatim
/-! The three actual base-flow fields satisfy the source's fixed-H6
label bound with one explicit constant, independent of derivative order. -/


-- @@ L2213-2213 verbatim
section


-- @@ L2215-2217 verbatim
/-! Actual ordinary L² displacement, material velocity and acceleration
for the base flow. The displacement estimate integrates the real spatial
jets of the flow, and the other two estimates use volume preservation. -/


-- @@ L2219-2219 verbatim
@[expose] public section


-- @@ L2221-2221 verbatim
noncomputable section


-- @@ L2223-2223 verbatim
namespace EulerBaseEulerParent


-- @@ L2225-2226 verbatim
open Set MeasureTheory Filter EulerSmoothLimit EulerSmoothBanachFlow
  EulerSmoothFlowGevrey EulerLpTranslation EulerGevrey EulerVolterraConvolution

-- @@ L2227-2227 verbatim
open scoped ContDiff BoundedContinuousFunction Interval


-- @@ L2229-2232 verbatim
/-- Cache the standard `NormedAddCommGroup (Space [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instBaseEulerFlowL21 (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) :=
    inferInstance

-- @@ L2233-2235 verbatim
/-- Cache the standard `NormedSpace ℝ (Space [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instBaseEulerFlowL22 (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance

-- @@ L2236-2240 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to
shorten typeclass synthesis. -/
local instance instBaseEulerFlowL23 (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))
    :=
    inferInstance

-- @@ L2241-2244 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instBaseEulerFlowL24 (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
    inferInstance


-- @@ L2246-2268 verbatim
/-- L² data, collecting `velocity`, `derivative`, `velocity_match`, `derivative_match`, `C`, `S`
and their compatibility conditions. -/
structure L2Data (I : Input) where
  /-- Velocity field of `L2Data`, of type `Icc (0 : ℝ) I.T → SmoothL2Field Space`. -/
  velocity : Icc (0 : ℝ) I.T → SmoothL2Field Space
  /-- Derivative field of `L2Data`, of type `Icc (0 : ℝ) I.T → SmoothL2Field Space`. -/
  derivative : Icc (0 : ℝ) I.T → SmoothL2Field Space
  velocity_match : ∀ t x, (velocity t).field x=I.field.field t x
  derivative_match : ∀ t x, (derivative t).field x=I.derivative.field t x
  /-- Bound coefficient of `L2Data`, of type `ℝ`. -/
  C : ℝ
  /-- Parameter `S` of `L2Data`, of type `ℝ`. -/
  S : ℝ
  /-- First-derivative bound coefficient of `L2Data`, of type `ℝ`. -/
  C₁ : ℝ
  /-- Parameter `S₁` of `L2Data`, of type `ℝ`. -/
  S₁ : ℝ
  C_nonneg : 0 ≤ C
  S_nonneg : 0 ≤ S
  C₁_nonneg : 0 ≤ C₁
  S₁_nonneg : 0 ≤ S₁
  velocity_bound : ∀ t, (velocity t).HasJetBound C S
  derivative_bound : ∀ t, (derivative t).HasJetBound C₁ S₁


-- @@ L2270-2270 verbatim
namespace L2Data


-- @@ L2272-2272 verbatim
variable {I : Input} (L : L2Data I)


-- @@ L2274-2275 verbatim
/-- Velocity radius, given by `flowRadius I.B I.R I.T L.S`. -/
def velocityRadius : ℝ := flowRadius I.B I.R I.T L.S


-- @@ L2277-2283 verbatim
theorem velocityRadius_nonneg : 0 ≤ L.velocityRadius := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have ht := I.T_pos
  have hs := L.S_nonneg
  dsimp [velocityRadius,flowRadius]
  positivity


-- @@ L2285-2295 verbatim
/-- Velocity field, constructed using `SmoothL2Field.composeField`. -/
def velocityField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.composeField ((flowData I.T I.T_pos.le I.field).forward t)
    (forward_contDiff I.T I.T_pos.le I.field t)
    (forward_measurePreserving I.T I.T_pos.le I.field I.divergence volume t)
    (1+I.B*I.T) (4*I.R+1)
    (add_nonneg zero_le_one (mul_nonneg I.B_nonneg I.T_pos.le))
    (add_nonneg (mul_nonneg (by norm_num) I.R_pos.le) zero_le_one)
    (fun n hn => forward_positive_bound I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
      I.small I.bound n hn t)
    (L.velocity t) L.C L.S L.C_nonneg L.S_nonneg (L.velocity_bound t)


-- @@ L2297-2300 verbatim
theorem velocityField_bound (t : Icc (0 : ℝ) I.T) :
    (L.velocityField t).HasJetBound L.C L.velocityRadius := by
  unfold velocityField velocityRadius
  apply SmoothL2Field.composeField_bound


-- @@ L2302-2306 verbatim
theorem velocityField_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    (L.velocityField t).field x=I.velocity.field t x := by
  change (L.velocity t).field ((flowData I.T I.T_pos.le I.field).forward t x)=_
  rw [L.velocity_match,I.velocity_apply]
  rfl


-- @@ L2308-2313 verbatim
theorem velocityField_jet (n : ℕ) (t : Icc (0 : ℝ) I.T) :
    iteratedFDeriv ℝ n (L.velocityField t).field =
      fun x => I.velocity.jet n t x := by
  rw [show (L.velocityField t).field = (I.velocity.field t : Space → Space) from
    funext (L.velocityField_apply t)]
  exact funext (fun x => (I.velocity.jet_eq n t x).symm)


-- @@ L2315-2335 verbatim
theorem displacement_jet_integral (n : ℕ) (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.displacement.jet n t x =
      ∫ s in (0 : ℝ)..(t : ℝ), extendPath I.T I.T_pos.le (I.velocity.jet n) s x := by
  let f : C(Icc (0 : ℝ) I.T,Space [×n]→L[ℝ] Space) :=
    ⟨fun s => I.velocity.jet n s x,
      (I.velocity.jet n).continuous.eval_const x⟩
  have h := EulerContinuousTimeIntegral.eq_initial_add_integral I.T I.T_pos.le f
    (fun s => extendPath I.T I.T_pos.le (I.displacement.jet n) s x)
    (fun s => SmoothTimeField.TimeDerivative.jet_pointwise I.T I.T_pos.le
      I.displacement I.velocity I.displacement_time n x s) t
  have hz : I.displacement.jet n ⟨0,le_rfl,I.T_pos.le⟩ x=0 := by
    rw [I.displacement.jet_eq]
    have he : (I.displacement.field ⟨0,le_rfl,I.T_pos.le⟩ : Space → Space)=0 :=
      funext I.displacement_initial
    rw [he,iteratedFDeriv_zero]
    rfl
  simp only [extendPath,projIcc_of_mem I.T_pos.le t.property,
    projIcc_of_mem I.T_pos.le (show (0 : ℝ) ∈ Icc 0 I.T from ⟨le_rfl,I.T_pos.le⟩),hz,
    zero_add,EulerContinuousTimeIntegral.integral_apply,EulerContinuousTimeIntegral.realIntegral]
        at h
  exact h


-- @@ L2337-2371 verbatim
theorem displacement_memLp_and_bound (n : ℕ) (t : Icc (0 : ℝ) I.T) :
    MemLp (iteratedFDeriv ℝ n (I.displacement.field t : Space → Space)) 2 volume ∧
      (eLpNorm (iteratedFDeriv ℝ n (I.displacement.field t : Space → Space)) 2 volume).toReal ≤
        I.T*L.C*L.velocityRadius^n*(n.factorial : ℝ)^2 := by
  let f : ℝ × Space → Space [×n]→L[ℝ] Space :=
    fun p => extendPath I.T I.T_pos.le (I.velocity.jet n) p.1 p.2
  have hc : Continuous f := by
    have ht := extendPath_continuous I.T I.T_pos.le (I.velocity.jet n)
    dsimp [f]
    fun_prop
  have hb : ∀ s : ℝ, MemLp (fun x => f (s,x)) 2 volume ∧
      (eLpNorm (fun x => f (s,x)) 2 volume).toReal ≤
        L.C*L.velocityRadius^n*(n.factorial : ℝ)^2 := by
    intro s
    have he : (fun x => f (s,x)) =
        iteratedFDeriv ℝ n (L.velocityField (projIcc 0 I.T I.T_pos.le s)).field :=
      (L.velocityField_jet n (projIcc 0 I.T I.T_pos.le s)).symm
    rw [he]
    exact ⟨(L.velocityField _).integrable n,by
      rw [← SmoothL2Field.norm_jetLp]
      exact L.velocityField_bound _ n⟩
  have hp := EulerLpParameterIntegral.intervalIntegral_memLp_and_bound (t : ℝ) t.property.1
    volume f hc.aestronglyMeasurable_of_secondCountable (L.C*L.velocityRadius^n*(n.factorial : ℝ)^2)
    (mul_nonneg (mul_nonneg L.C_nonneg (pow_nonneg L.velocityRadius_nonneg n)) (sq_nonneg _))
    (Eventually.of_forall hb)
  have he : (fun x => ∫ s in (0 : ℝ)..(t : ℝ), f (s,x)) =
      iteratedFDeriv ℝ n (I.displacement.field t : Space → Space) := by
    funext x
    exact (displacement_jet_integral (I := I) n t x).symm.trans (I.displacement.jet_eq n t x)
  rw [he] at hp
  refine ⟨hp.1,hp.2.trans ?_⟩
  have ht := mul_le_mul_of_nonneg_right t.property.2
    (mul_nonneg (mul_nonneg L.C_nonneg (pow_nonneg L.velocityRadius_nonneg n))
      (sq_nonneg (n.factorial : ℝ)))
  exact ht.trans_eq (by ring)


-- @@ L2373-2377 verbatim
/-- Displacement field, bundling `field`, `smooth`, `integrable`. -/
def displacementField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space where
  field := I.displacement.field t
  smooth := I.displacement.smooth t
  integrable n := (L.displacement_memLp_and_bound n t).1


-- @@ L2379-2383 verbatim
theorem displacementField_bound (t : Icc (0 : ℝ) I.T) :
    (L.displacementField t).HasJetBound (I.T*L.C) L.velocityRadius := by
  intro n
  rw [SmoothL2Field.norm_jetLp]
  exact (L.displacement_memLp_and_bound n t).2


-- @@ L2385-2386 verbatim
/-- Acceleration source radius, given by `4*I.R+L.S+L.S₁`. -/
def accelerationSourceRadius : ℝ := 4*I.R+L.S+L.S₁


-- @@ L2388-2393 verbatim
theorem accelerationSourceRadius_nonneg : 0 ≤ L.accelerationSourceRadius := by
  have hr := I.R_pos
  have hs := L.S_nonneg
  have hs₁ := L.S₁_nonneg
  dsimp [accelerationSourceRadius]
  positivity


-- @@ L2395-2402 verbatim
theorem field_derivative_bound (t : Icc (0 : ℝ) I.T) :
    HasSupBound (fderiv ℝ (I.field.field t : Space → Space)) (I.B*I.R) L.accelerationSourceRadius
        := by
  have h : HasSupBound (I.field.field t : Space → Space) I.B I.R :=
    fun n x => field_jet_bound I.T I.field I.B I.R I.bound n t x
  exact (h.derivative I.B_nonneg I.R_pos.le).mono (mul_nonneg I.B_nonneg I.R_pos.le)
    (mul_nonneg (by norm_num) I.R_pos.le) le_rfl
    (by dsimp [accelerationSourceRadius]; linarith [L.S_nonneg,L.S₁_nonneg])


-- @@ L2404-2411 verbatim
/-- Acceleration product, constructed using `SmoothL2Field.productField`. -/
def accelerationProduct (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.productField (fderiv ℝ (I.field.field t : Space → Space))
    ((I.field.smooth t).fderiv_right (m := ∞) (by simp)) (L.velocity t)
    (I.B*I.R) L.C L.accelerationSourceRadius (mul_nonneg I.B_nonneg I.R_pos.le) L.C_nonneg
    L.accelerationSourceRadius_nonneg (L.field_derivative_bound t)
    ((L.velocity_bound t).mono L.C_nonneg L.S_nonneg le_rfl
      (by dsimp [accelerationSourceRadius]; linarith [I.R_pos,L.S₁_nonneg]))


-- @@ L2413-2416 verbatim
/-- Acceleration source, given by `SmoothL2Field.addField (L.derivative t)
(L.accelerationProduct t)`. -/
def accelerationSource (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.addField (L.derivative t) (L.accelerationProduct t)


-- @@ L2418-2419 verbatim
/-- Acceleration amplitude, given by `L.C₁+3*(I.B*I.R)*L.C`. -/
def accelerationAmplitude : ℝ := L.C₁+3*(I.B*I.R)*L.C


-- @@ L2421-2427 verbatim
theorem accelerationAmplitude_nonneg : 0 ≤ L.accelerationAmplitude := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have hc := L.C_nonneg
  have hc₁ := L.C₁_nonneg
  dsimp [accelerationAmplitude]
  positivity


-- @@ L2429-2434 verbatim
theorem accelerationSource_bound (t : Icc (0 : ℝ) I.T) :
    (L.accelerationSource t).HasJetBound L.accelerationAmplitude L.accelerationSourceRadius := by
  apply SmoothL2Field.HasJetBound.add
  · exact (L.derivative_bound t).mono L.C₁_nonneg L.S₁_nonneg le_rfl
      (by dsimp [accelerationSourceRadius]; linarith [I.R_pos,L.S_nonneg])
  · exact SmoothL2Field.productField_bound _ _ _ _ _ _ _ _ _ _ _


-- @@ L2436-2437 verbatim
/-- Acceleration radius, given by `flowRadius I.B I.R I.T L.accelerationSourceRadius`. -/
def accelerationRadius : ℝ := flowRadius I.B I.R I.T L.accelerationSourceRadius


-- @@ L2439-2445 verbatim
theorem accelerationRadius_nonneg : 0 ≤ L.accelerationRadius := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have ht := I.T_pos
  have hs := L.accelerationSourceRadius_nonneg
  dsimp [accelerationRadius,flowRadius]
  positivity


-- @@ L2447-2458 verbatim
/-- Acceleration field, constructed using `SmoothL2Field.composeField`. -/
def accelerationField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.composeField ((flowData I.T I.T_pos.le I.field).forward t)
    (forward_contDiff I.T I.T_pos.le I.field t)
    (forward_measurePreserving I.T I.T_pos.le I.field I.divergence volume t)
    (1+I.B*I.T) (4*I.R+1)
    (add_nonneg zero_le_one (mul_nonneg I.B_nonneg I.T_pos.le))
    (add_nonneg (mul_nonneg (by norm_num) I.R_pos.le) zero_le_one)
    (fun n hn => forward_positive_bound I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
      I.small I.bound n hn t)
    (L.accelerationSource t) L.accelerationAmplitude L.accelerationSourceRadius
    L.accelerationAmplitude_nonneg L.accelerationSourceRadius_nonneg (L.accelerationSource_bound t)


-- @@ L2460-2463 verbatim
theorem accelerationField_bound (t : Icc (0 : ℝ) I.T) :
    (L.accelerationField t).HasJetBound L.accelerationAmplitude L.accelerationRadius := by
  unfold accelerationField accelerationRadius
  apply SmoothL2Field.composeField_bound


-- @@ L2465-2470 verbatim
theorem accelerationField_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    (L.accelerationField t).field x=I.acceleration.field t x := by
  change (L.derivative t).field ((flowData I.T I.T_pos.le I.field).forward t x) +
    fderiv ℝ (I.field.field t : Space → Space) ((flowData I.T I.T_pos.le I.field).forward t x)
      ((L.velocity t).field ((flowData I.T I.T_pos.le I.field).forward t x)) = _
  rw [L.derivative_match,L.velocity_match,I.acceleration_apply,accelerationFamily_apply]


-- @@ L2472-2472 verbatim
end L2Data

-- @@ L2473-2473 verbatim
end EulerBaseEulerParent


-- @@ L2475-2475 verbatim
end

-- @@ L2476-2476 verbatim
end


-- @@ L2478-2478 verbatim
end


-- @@ L2480-2480 verbatim
@[expose] public section


-- @@ L2482-2482 verbatim
noncomputable section


-- @@ L2484-2484 verbatim
namespace EulerBaseEulerParent.L2Data


-- @@ L2486-2487 verbatim
open EulerParentPacketFrames EulerLpTranslation EulerParameterWordGevrey
  EulerPacketParentLabelBounds Set


-- @@ L2489-2489 verbatim
variable {I : Input} (L : L2Data I)


-- @@ L2491-2497 verbatim
/-- Label cost, constructed using `1`. -/
def labelCost : ℝ :=
  1 + sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius (I.T*L.C) +
    sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius L.C +
    sobolevCoefficientAmplitude (Fin 3) 6 L.accelerationRadius L.accelerationAmplitude +
    sobolevCoefficientRadius (Fin 3) L.velocityRadius +
    sobolevCoefficientRadius (Fin 3) L.accelerationRadius


-- @@ L2499-2511 verbatim
private theorem costs_nonneg :
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius (I.T*L.C) ∧
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius L.C ∧
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.accelerationRadius L.accelerationAmplitude ∧
    0 ≤ sobolevCoefficientRadius (Fin 3) L.velocityRadius ∧
    0 ≤ sobolevCoefficientRadius (Fin 3) L.accelerationRadius :=
  ⟨sobolevCoefficientAmplitude_nonneg 6 L.velocityRadius (I.T*L.C)
      L.velocityRadius_nonneg (mul_nonneg I.T_pos.le L.C_nonneg),
    sobolevCoefficientAmplitude_nonneg 6 L.velocityRadius L.C L.velocityRadius_nonneg L.C_nonneg,
    sobolevCoefficientAmplitude_nonneg 6 L.accelerationRadius L.accelerationAmplitude
      L.accelerationRadius_nonneg L.accelerationAmplitude_nonneg,
    sobolevCoefficientRadius_nonneg L.velocityRadius L.velocityRadius_nonneg,
    sobolevCoefficientRadius_nonneg L.accelerationRadius L.accelerationRadius_nonneg⟩


-- @@ L2513-2516 verbatim
theorem labelCost_one : 1 ≤ L.labelCost := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  dsimp [labelCost]
  linarith


-- @@ L2518-2525 verbatim
theorem displacement_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.displacementField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.displacementField t)
    (I.T*L.C) L.velocityRadius L.labelCost (mul_nonneg I.T_pos.le L.C_nonneg)
    L.velocityRadius_nonneg (L.displacementField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith


-- @@ L2527-2533 verbatim
theorem velocity_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.velocityField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.velocityField t)
    L.C L.velocityRadius L.labelCost L.C_nonneg L.velocityRadius_nonneg (L.velocityField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith


-- @@ L2535-2542 verbatim
theorem acceleration_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.accelerationField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.accelerationField t)
    L.accelerationAmplitude L.accelerationRadius L.labelCost L.accelerationAmplitude_nonneg
    L.accelerationRadius_nonneg (L.accelerationField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith


-- @@ L2544-2558 verbatim
/-- Label data, bundling `K`, `K_one`, `displacement`, `velocity` and the required compatibility
proofs. -/
def labelData (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    LabelData (I.parent ell hell hell1) where
  K := L.labelCost
  K_one := L.labelCost_one
  displacement := L.displacementField
  velocity := L.velocityField
  acceleration := L.accelerationField
  displacement_match _ _ := rfl
  velocity_match := L.velocityField_apply
  acceleration_match := L.accelerationField_apply
  displacement_bound := L.displacement_labelBound
  velocity_bound := L.velocity_labelBound
  acceleration_bound := L.acceleration_labelBound


-- @@ L2560-2560 verbatim
end EulerBaseEulerParent.L2Data


-- @@ L2562-2562 verbatim
end

-- @@ L2563-2563 verbatim
end


-- @@ L2565-2565 verbatim
end


-- @@ L2567-2567 verbatim
section


-- @@ L2569-2571 verbatim
/-! Odd initial velocity produces the actual odd local Euler velocity
and odd pressure force. The scalar pressure, normalized at the origin,
is even. These are consequences of correction uniqueness. -/


-- @@ L2573-2573 verbatim
section


-- @@ L2575-2577 verbatim
/-! Odd static data give the genuine parity hypotheses of the constructed
correction. In particular the actual convection residual is odd; this is
proved from its derivative formula. -/


-- @@ L2579-2579 verbatim
@[expose] public section


-- @@ L2581-2581 verbatim
noncomputable section


-- @@ L2583-2583 verbatim
namespace EulerSmallCorrection


-- @@ L2585-2587 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCorrectionAssembly
  EulerConstantCorrection


-- @@ L2589-2590 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}
  (G : Field P T raw) (hodd : JointOdd T raw)


-- @@ L2592-2601 verbatim
include G hodd in
theorem residual_odd (ε : ℝ) :
    JointOdd T (fun z => fderiv ℝ (fun y => (ε • raw) (z.1,y)) z.2 ((ε • raw) z,0)) := by
  have hs := hodd.smul ε
  intro t x θ
  change (fderiv ℝ (fun y => (ε • raw) (t,y)) (-x,-θ)) ((ε • raw) (t,(-x,-θ)),0) =
    -((fderiv ℝ (fun y => (ε • raw) (t,y)) (x,θ)) ((ε • raw) (t,(x,θ)),0))
  rw [(G.smul ε).raw_fderiv_even_of_odd hs t x θ,hs t x θ]
  have he : (-(ε • raw) (t,(x,θ)),(0 : ℝ)) = -((ε • raw) (t,(x,θ)),(0 : ℝ)) := by simp
  rw [he,map_neg]


-- @@ L2603-2617 verbatim
include hodd in
theorem parityData (ε : ℝ) : ParityData P (input G ε) where
  metric _ _ := rfl
  linear _ _ := rfl
  quadratic _ _ _ := by
    change (0 : Space →L[ℝ] Space)= -0
    simp only [neg_zero]
  approximation t := by
    have h := ((G.smul ε).reflectionOdd_of_raw (hodd.smul ε)) t
    change -EulerCylinderFieldReflection.reflection P ((G.smul ε).path t)=(G.smul ε).path t
    rw [h,neg_neg]
  residual t := by
    have h := ((residual G ε).reflectionOdd_of_raw (residual_odd G hodd ε)) t
    change -EulerCylinderFieldReflection.reflection P ((residual G ε).path t)=(residual G ε).path t
    rw [h,neg_neg]


-- @@ L2619-2619 verbatim
end EulerSmallCorrection


-- @@ L2621-2621 verbatim
end

-- @@ L2622-2622 verbatim
end


-- @@ L2624-2624 verbatim
end


-- @@ L2626-2626 verbatim
@[expose] public section


-- @@ L2628-2628 verbatim
noncomputable section


-- @@ L2630-2630 verbatim
namespace EulerStaticEuler


-- @@ L2632-2635 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCylinderField EulerCorrectionAssembly EulerMetricTransport
  EulerCanonicalGraphPotential EulerGraphPressurePotential


-- @@ L2637-2639 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)
  (hodd : ∀ x, u.field (-x) = -u.field x)


-- @@ L2641-2641 verbatim
include hodd


-- @@ L2643-2645 verbatim
theorem symmetry : ParityData P (inputData P u C R hC hR) :=
  EulerSmallCorrection.parityData (EulerStaticCylinder.field P 1 u)
    (fun _ x _ => hodd x) (amplitude P C R hC hR)


-- @@ L2647-2651 verbatim
theorem exactPacket_odd (t : Icc (0 : ℝ) 1) :
    -EulerCylinderReflection.reflection P ((exactPacket P u C R hC hR hu hdiv).velocity.field t) =
      (exactPacket P u C R hC hR hu hdiv).velocity.field t :=
  exactPacketOfResidual_velocity_odd P (correctionBudget P u C R hC hR hu hdiv)
    _ (symmetry P u C R hC hR hodd) t


-- @@ L2653-2664 verbatim
theorem unit_velocity_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.velocity (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  let s := projIcc 0 1 zero_le_one t
  have h := continuous_representative_odd P
    ((exactPacket P u C R hC hR hu hdiv).velocity.field s)
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField s)
    (exactPacket_odd P u C R hC hR hu hdiv hodd s)
    (smoothField_continuous P _ ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_smooth s))
    ((exactPacket P u C R hC hR hu hdiv).velocity.pointField_ae s) (x,(0 : AddCircle P))
  simpa only [Prod.neg_mk,neg_zero,EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,
    FieldTower.rawField,coveringMap,AddCircle.coe_zero] using h


-- @@ L2666-2676 verbatim
omit hodd in
theorem unit_pressure_point (t : Icc (0 : ℝ) 1) (x : LiftDomain P) :
    (exactPacket P u C R hC hR hu hdiv).pressure.pointField t x =
      (correctionBudget P u C R hC hR hu hdiv).pointPressure P t x := by
  erw [exactPacket,exactPacketOfResidual_pressure_pointField]
  have hz : (Field.zero P 1).toFieldTower.pointField t x=0 := by
    change EulerSobolevPointEvaluation.pointEvaluation P x
      ((Field.zero P 1).toFieldTower.realization 3 t)=0
    simp only [EulerSmallCorrection.zero_tower,map_zero]
  change (Field.zero P 1).toFieldTower.pointField t x+_=_
  rw [hz,zero_add]


-- @@ L2678-2687 verbatim
theorem unit_force_odd (t : ℝ) (x : Space) :
    EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      -EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  change (exactPacket P u C R hC hR hu hdiv).pressure.pointField
      (projIcc 0 1 zero_le_one t) (-x,0) =
    -(exactPacket P u C R hC hR hu hdiv).pressure.pointField (projIcc 0 1 zero_le_one t) (x,0)
  rw [unit_pressure_point,unit_pressure_point]
  have h := (correctionBudget P u C R hC hR hu hdiv).pointPressure_odd P
    (symmetry P u C R hC hR hodd) (projIcc 0 1 zero_le_one t) (x,0)
  simpa only [Prod.neg_mk,neg_zero] using h


-- @@ L2689-2708 verbatim
theorem unit_pressure_even (t : ℝ) (x : Space) :
    EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (t,-x) =
      EulerConstantEuler.pressure (exactPacket P u C R hC hR hu hdiv) (t,x) := by
  have h := radialPotential_even
    (fun y => EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,y))
    (unit_force_odd P u C R hC hR hu hdiv hodd t) x
  change radialPotential ((exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t)) (-x) =
    radialPotential ((exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t)) x
  have he : (exactPacket P u C R hC hR hu hdiv).graphPressure 1
      (projIcc 0 1 zero_le_one t) =
      fun y => EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) (t,y) := by
    funext y
    simp only [ExactLiftedPacket.graphPressure,EulerConstantEuler.force,
      ExactLiftedPacket.rawPressure,FieldTower.rawField,cylinderGraph,coveringMap,
      inputData,EulerSmallCorrection.input,EulerConstantCorrection.data,
      one_smul,inner_zero_left,mul_zero]
  rw [he]
  exact h


-- @@ L2710-2714 verbatim
theorem localVelocity_odd (t : ℝ) (x : Space) :
    localVelocity P u C R hC hR hu hdiv (t,-x)= -localVelocity P u C R hC hR hu hdiv (t,x) := by
  unfold localVelocity EulerTimeRescaling.velocity
  rw [EulerTimeRescaling.coordinates_apply,EulerTimeRescaling.coordinates_apply,
    unit_velocity_odd P u C R hC hR hu hdiv hodd,smul_neg]


-- @@ L2716-2720 verbatim
theorem localPressure_even (t : ℝ) (x : Space) :
    localPressure P u C R hC hR hu hdiv (t,-x)=localPressure P u C R hC hR hu hdiv (t,x) := by
  unfold localPressure EulerTimeRescaling.pressure
  rw [EulerTimeRescaling.coordinates_apply,EulerTimeRescaling.coordinates_apply,
    unit_pressure_even P u C R hC hR hu hdiv hodd]


-- @@ L2722-2722 verbatim
end EulerStaticEuler


-- @@ L2724-2724 verbatim
end

-- @@ L2725-2725 verbatim
end


-- @@ L2727-2727 verbatim
end


-- @@ L2729-2729 verbatim
section


-- @@ L2731-2733 verbatim
/-! The actual local Euler velocity and pressure force agree with the
constructed smooth coefficient paths. In particular the local velocity
has a true one-sided time derivative at the initial and terminal times. -/


-- @@ L2735-2735 verbatim
@[expose] public section


-- @@ L2737-2737 verbatim
noncomputable section


-- @@ L2739-2739 verbatim
namespace EulerStaticEuler


-- @@ L2741-2741 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation EulerVolterraConvolution

-- @@ L2742-2742 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L2744-2745 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L2747-2758 verbatim
theorem velocityCoefficient_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (velocityCoefficient P u C R hC hR hu hdiv).field t x =
      localVelocity P u C R hC hR hu hdiv (t,x) := by
  change (amplitude P C R hC hR)⁻¹ •
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t) x = _
  rw [unitVelocityCoefficient_apply]
  change (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]


-- @@ L2760-2771 verbatim
theorem forceCoefficient_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (forceCoefficient P u C R hC hR hu hdiv).field t x =
      localForce P u C R hC hR hu hdiv (t,x) := by
  change ((amplitude P C R hC hR)⁻¹)^2 •
    (unitForceCoefficient P u C R hC hR hu hdiv).field
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t) x = _
  rw [unitForceCoefficient_apply]
  change ((amplitude P C R hC hR)⁻¹)^2 • EulerConstantEuler.force
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    ((amplitude P C R hC hR)⁻¹)^2 • EulerConstantEuler.force
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]


-- @@ L2773-2783 verbatim
theorem localVelocity_hasDerivWithinAt
    (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    HasDerivWithinAt (fun s => localVelocity P u C R hC hR hu hdiv (s,x))
      ((derivativeCoefficient P u C R hC hR hu hdiv).field t x)
      (Icc (0 : ℝ) (amplitude P C R hC hR)) t := by
  have hd := coefficient_time P u C R hC hR hu hdiv t x
  apply hd.congr_of_mem _ t.property
  intro s hs
  have he := velocityCoefficient_apply P u C R hC hR hu hdiv ⟨s,hs⟩ x
  simpa only [SmoothTimeField.realField,extendPath,projIcc_of_mem (amplitude_pos P C R hC hR).le hs]
    using he.symm


-- @@ L2785-2785 verbatim
end EulerStaticEuler


-- @@ L2787-2787 verbatim
end

-- @@ L2788-2788 verbatim
end


-- @@ L2790-2790 verbatim
end


-- @@ L2792-2792 verbatim
section


-- @@ L2794-2795 verbatim
/-! Oddness of the genuine base velocity propagates through its actual
flow to the base parent, using ODE uniqueness. -/


-- @@ L2797-2797 verbatim
@[expose] public section


-- @@ L2799-2799 verbatim
noncomputable section


-- @@ L2801-2801 verbatim
namespace EulerBaseEulerParent.Input


-- @@ L2803-2803 verbatim
open Set EulerSmoothLimit EulerSmoothBanachFlow EulerParentPacketFrames


-- @@ L2805-2805 verbatim
variable (I : Input)


-- @@ L2807-2813 verbatim
theorem oddData (hodd : ∀ t, Function.Odd (I.field.field t : Space → Space))
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) : OddData (I.parent ell hell hell1) := by
  have hd (t : Icc (0 : ℝ) I.T) : Function.Odd (I.displacement.field t : Space → Space) := by
    intro x
    rw [I.displacement_apply,I.displacement_apply,forward_odd I.T I.T_pos.le I.field hodd t]
    abel
  exact { displacement := hd }


-- @@ L2815-2815 verbatim
end EulerBaseEulerParent.Input


-- @@ L2817-2817 verbatim
end

-- @@ L2818-2818 verbatim
end


-- @@ L2820-2820 verbatim
end


-- @@ L2822-2822 verbatim
@[expose] public section


-- @@ L2824-2824 verbatim
noncomputable section


-- @@ L2826-2826 verbatim
namespace EulerStaticEuler


-- @@ L2828-2829 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerParentPacketFrames
  EulerTimeIntervalRestriction EulerParameterWordGevrey EulerSmoothFlowGevrey

-- @@ L2830-2830 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L2832-2832 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L2834-2838 verbatim
/-- Base time, given by `EulerBaseEulerParent.horizon (amplitude P C R hC hR)
(outputVelocitySize P C R) (outputRadius R)`. -/
def baseTime (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  EulerBaseEulerParent.horizon (amplitude P C R hC hR)
    (outputVelocitySize P C R) (outputRadius R)


-- @@ L2840-2843 verbatim
theorem baseTime_pos (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 < baseTime P C R hC hR :=
  EulerBaseEulerParent.horizon_pos _ _ _ (amplitude_pos P C R hC hR)
    (outputVelocitySize_nonneg P C R hC hR) (outputRadius_pos R hR).le


-- @@ L2845-2847 verbatim
theorem baseTime_le (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    baseTime P C R hC hR ≤ amplitude P C R hC hR :=
  EulerBaseEulerParent.horizon_le _ _ _


-- @@ L2849-2852 verbatim
/-- Base inclusion, given by `initialInclusion _ _ (baseTime_le P C R hC hR)`. -/
def baseInclusion (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) (baseTime P C R hC hR), Icc (0 : ℝ) (amplitude P C R hC hR)) :=
  initialInclusion _ _ (baseTime_le P C R hC hR)


-- @@ L2854-2866 verbatim
/-- Base label constant as an element of `ℝ`. -/
def baseLabelConstant (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  let T := baseTime P C R hC hR
  let B := outputVelocitySize P C R
  let S := outputRadius R
  let C₁ := outputDerivativeSize P C R hC hR
  let V := flowRadius B S T S
  let M := C₁+3*(B*S)*B
  let A := flowRadius B S T (4*S+S+S)
  1+sobolevCoefficientAmplitude (Fin 3) 6 V (T*B) +
    sobolevCoefficientAmplitude (Fin 3) 6 V B +
    sobolevCoefficientAmplitude (Fin 3) 6 A M +
    sobolevCoefficientRadius (Fin 3) V+sobolevCoefficientRadius (Fin 3) A


-- @@ L2868-2869 verbatim
variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L2871-2885 verbatim
/-- Base input, constructed using `EulerBaseEulerParent.ofInterval`. -/
def baseInput : EulerBaseEulerParent.Input :=
  EulerBaseEulerParent.ofInterval (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
    (velocityCoefficient P u C R hC hR hu hdiv)
    (derivativeCoefficient P u C R hC hR hu hdiv)
    (coefficient_time P u C R hC hR hu hdiv)
    (fun t x => by
      have he : ((velocityCoefficient P u C R hC hR hu hdiv).field t : Space → Space) =
          fun y => localVelocity P u C R hC hR hu hdiv (t,y) :=
        funext (velocityCoefficient_apply P u C R hC hR hu hdiv t)
      rw [he]
      exact localVelocity_divergence P u C R hC hR hu hdiv t x)
    (outputVelocitySize P C R) (outputRadius R)
    (outputVelocitySize_nonneg P C R hC hR) (outputRadius_pos R hR)
    (velocityCoefficient_bound P u C R hC hR hu hdiv)


-- @@ L2887-2890 verbatim
theorem baseInput_field (t : Icc (0 : ℝ) (baseTime P C R hC hR)) (x : Space) :
    (baseInput P u C R hC hR hu hdiv).field.field t x =
      localVelocity P u C R hC hR hu hdiv (t,x) :=
  velocityCoefficient_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x


-- @@ L2892-2915 verbatim
/-- Base L² data, bundling `velocity`, `derivative`, `velocity_match`, `derivative_match` and
the required compatibility proofs. -/
def baseL2Data : EulerBaseEulerParent.L2Data (baseInput P u C R hC hR hu hdiv) where
  velocity t := localField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  derivative t := localDerivativeField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  velocity_match t x :=
    (localField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x).trans
      (baseInput_field P u C R hC hR hu hdiv t x).symm
  derivative_match t x := by
    rw [show (baseInput P u C R hC hR hu hdiv).derivative =
      (derivativeCoefficient P u C R hC hR hu hdiv).compTime (baseInclusion P C R hC hR) from rfl]
    erw [SmoothTimeField.compTime_apply]
    exact localDerivativeField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t) x
  C := outputVelocitySize P C R
  S := outputRadius R
  C₁ := outputDerivativeSize P C R hC hR
  S₁ := outputRadius R
  C_nonneg := outputVelocitySize_nonneg P C R hC hR
  S_nonneg := (outputRadius_pos R hR).le
  C₁_nonneg := outputDerivativeSize_nonneg P C R hC hR
  S₁_nonneg := (outputRadius_pos R hR).le
  velocity_bound t := localField_bound P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  derivative_bound t := localDerivativeField_bound P u C R hC hR hu hdiv
    (baseInclusion P C R hC hR t)


-- @@ L2917-2917 verbatim
variable (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)


-- @@ L2919-2920 verbatim
/-- Base parent, given by `(baseInput P u C R hC hR hu hdiv).parent ell hell hell1`. -/
def baseParent : Parent := (baseInput P u C R hC hR hu hdiv).parent ell hell hell1


-- @@ L2922-2924 verbatim
/-- Base label data, given by `(baseL2Data P u C R hC hR hu hdiv).labelData ell hell hell1`. -/
def baseLabelData : LabelData (baseParent P u C R hC hR hu hdiv ell hell hell1) :=
  (baseL2Data P u C R hC hR hu hdiv).labelData ell hell hell1


-- @@ L2926-2927 verbatim
theorem baseLabelData_constant :
    (baseLabelData P u C R hC hR hu hdiv ell hell hell1).K=baseLabelConstant P C R hC hR := rfl


-- @@ L2929-2931 verbatim
include u hu hdiv ell hell hell1 in
theorem baseLabelConstant_one : 1 ≤ baseLabelConstant P C R hC hR :=
  (baseLabelData P u C R hC hR hu hdiv ell hell hell1).K_one


-- @@ L2933-2935 verbatim
/-- Base inverse, given by `(baseInput P u C R hC hR hu hdiv).particleInverse ell hell hell1`. -/
def baseInverse : ParticleInverse (baseParent P u C R hC hR hu hdiv ell hell hell1) :=
  (baseInput P u C R hC hR hu hdiv).particleInverse ell hell hell1


-- @@ L2937-2942 verbatim
theorem baseParent_velocity_match (t : Icc (0 : ℝ) (baseTime P C R hC hR)) (x : Space) :
    (baseParent P u C R hC hR hu hdiv ell hell hell1).velocity.field t x =
      localVelocity P u C R hC hR hu hdiv
        (t,(baseParent P u C R hC hR hu hdiv ell hell hell1).position t x) := by
  have h := (baseInput P u C R hC hR hu hdiv).parent_velocity ell hell hell1 t x
  exact h.trans (baseInput_field P u C R hC hR hu hdiv t _)


-- @@ L2944-2964 verbatim
/-- Base evolution, bundling `inverse`, `velocity`, `pressure`, `force` and the required
compatibility proofs. -/
def baseEvolution : Evolution (baseParent P u C R hC hR hu hdiv ell hell hell1) where
  inverse := baseInverse P u C R hC hR hu hdiv ell hell hell1
  velocity := localVelocity P u C R hC hR hu hdiv
  pressure := localPressure P u C R hC hR hu hdiv
  force t x := localForce P u C R hC hR hu hdiv (t,x)
  force_continuous := by
    have hc : Continuous (fun q : Icc (0 : ℝ) (baseTime P C R hC hR) × Space =>
        ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact (localForce_joint_continuous P u C R hC hR hu hdiv).comp hc
  velocity_match := baseParent_velocity_match P u C R hC hR hu hdiv ell hell hell1
  velocity_differentiable t ht x := localVelocity_differentiableAt P u C R hC hR hu hdiv t
    ⟨ht.1,ht.2.trans_le (baseTime_le P C R hC hR)⟩ x
  pressure_differentiable t x :=
    (localPressure_smooth P u C R hC hR hu hdiv t).differentiable (by simp) x
  pressure_gradient t x := localPressure_gradient P u C R hC hR hu hdiv t x
  momentum_zero t ht x := localMomentum P u C R hC hR hu hdiv t
    ⟨ht.1,ht.2.trans_le (baseTime_le P C R hC hR)⟩ x
  divergence_zero t _ x := localVelocity_divergence P u C R hC hR hu hdiv t x


-- @@ L2966-2976 verbatim
theorem baseParent_initial_velocity (x : Space) :
    (baseParent P u C R hC hR hu hdiv ell hell hell1).velocity.field
      ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x=u.field x := by
  have h := baseParent_velocity_match P u C R hC hR hu hdiv ell hell hell1
    ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x
  have hz : (baseParent P u C R hC hR hu hdiv ell hell hell1).position
      ⟨0,le_rfl,(baseTime_pos P C R hC hR).le⟩ x=x := by
    change x+(baseParent P u C R hC hR hu hdiv ell hell hell1).displacement.field _ x=x
    rw [(baseParent P u C R hC hR hu hdiv ell hell hell1).initial,add_zero]
  erw [hz,localVelocity_initial] at h
  exact h


-- @@ L2978-2983 verbatim
theorem baseOddData (hodd : ∀ x, u.field (-x) = -u.field x) :
    OddData (baseParent P u C R hC hR hu hdiv ell hell hell1) := by
  apply (baseInput P u C R hC hR hu hdiv).oddData _ ell hell hell1
  intro t x
  erw [baseInput_field,baseInput_field]
  exact localVelocity_odd P u C R hC hR hu hdiv hodd t x


-- @@ L2985-2985 verbatim
end EulerStaticEuler


-- @@ L2987-2987 verbatim
end

-- @@ L2988-2988 verbatim
end


-- @@ L2990-2990 verbatim
end


-- @@ L2992-2992 verbatim
section


-- @@ L2994-2995 verbatim
/-! The actual compact base datum has factorial bounds uniform in the
small transverse parameter. All constants use the fixed cutoff only. -/


-- @@ L2997-2997 verbatim
section


-- @@ L2999-3000 verbatim
/-! The compact initial velocity in the manuscript is constructed using
the fixed factorial-bounded outer cutoff and the actual curl potential. -/


-- @@ L3002-3002 verbatim
@[expose] public section


-- @@ L3004-3004 verbatim
noncomputable section


-- @@ L3006-3006 verbatim
namespace EulerBaseDatum


-- @@ L3008-3009 verbatim
open Set Filter ContinuousLinearMap MeasureTheory EulerSmoothLimit EulerVectorCalculus
  EulerSpatialCutoffs EulerGevrey  EulerLpTranslation EulerMeanSolenoidal

-- @@ L3010-3010 verbatim
open scoped ContDiff Topology


-- @@ L3012-3014 verbatim
/-- Potential, given by `outerCutoff x*linearPotential L i x`. -/
def potential (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) : ℝ :=
  outerCutoff x*linearPotential L i x


-- @@ L3016-3018 verbatim
theorem potential_smooth (L : Space →L[ℝ] Space) (i : Fin 3) :
    ContDiff ℝ ∞ (potential L i) :=
  outerCutoff_contDiff.mul (contDiff_linearPotential L i)


-- @@ L3020-3022 verbatim
theorem potential_support (L : Space →L[ℝ] Space) (i : Fin 3) :
    tsupport (potential L i) ⊆ Metric.closedBall (0 : Space) 2 :=
  tsupport_mul_subset_left.trans outerCutoff_support


-- @@ L3024-3025 verbatim
/-- Velocity, given by `curl (potential L)`. -/
def velocity (L : Space →L[ℝ] Space) : Space → Space := curl (potential L)


-- @@ L3027-3028 verbatim
theorem velocity_smooth (L : Space →L[ℝ] Space) : ContDiff ℝ ∞ (velocity L) :=
  contDiff_curl (potential L) (potential_smooth L)


-- @@ L3030-3032 verbatim
theorem velocity_support (L : Space →L[ℝ] Space) :
    tsupport (velocity L) ⊆ Metric.closedBall (0 : Space) 2 :=
  tsupport_curl_subset (potential L) _ Metric.isClosed_closedBall (potential_support L)


-- @@ L3034-3036 verbatim
theorem velocity_compact (L : Space →L[ℝ] Space) : HasCompactSupport (velocity L) :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
    (isClosed_tsupport _) (velocity_support L)


-- @@ L3038-3039 verbatim
theorem velocity_divergence (L : Space →L[ℝ] Space) (x : Space) :
    divergence (velocity L) x=0 := divergence_curl (potential L) (potential_smooth L) x


-- @@ L3041-3044 verbatim
theorem velocity_odd (L : Space →L[ℝ] Space) (x : Space) : velocity L (-x)= -velocity L x := by
  apply odd_curl_of_even (potential L) (fun i => (potential_smooth L i).differentiable (by simp))
  intro i y
  simp only [potential,outerCutoff_even,linearPotential_even]


-- @@ L3046-3054 verbatim
theorem velocity_plateau (L : Space →L[ℝ] Space) (hL : LinearMap.trace ℝ Space L.toLinearMap = 0)
    (x : Space) (hx : ‖x‖ < 1) : velocity L x=L x := by
  have he (i : Fin 3) : potential L i =ᶠ[𝓝 x] linearPotential L i := by
    have hx' : x ∈ Metric.ball (0 : Space) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    have hy' : ‖y‖ ≤ 1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < 1).le
    simp only [potential,outerCutoff_one y hy',one_mul]
  exact (curl_congr_nhds _ _ x he).trans (curl_linearPotential_of_trace_zero L hL x)


-- @@ L3056-3064 verbatim
theorem velocity_fderiv_plateau (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0) (x : Space) (hx : ‖x‖ < 1) :
    fderiv ℝ (velocity L) x=L := by
  have he : velocity L =ᶠ[𝓝 x] (L : Space → Space) := by
    have hx' : x ∈ Metric.ball (0 : Space) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    exact velocity_plateau L hL y (by simpa only [Metric.mem_ball,dist_zero_right] using hy)
  exact he.fderiv_eq.trans L.fderiv


-- @@ L3066-3072 verbatim
/-- Field, bundling `field`, `smooth`, `integrable`. -/
def field (L : Space →L[ℝ] Space) : SmoothL2Field Space where
  field := velocity L
  smooth := velocity_smooth L
  integrable n := ((velocity_smooth L).continuous_iteratedFDeriv (m := n) (by
      simp)).memLp_of_hasCompactSupport
    ((velocity_compact L).iteratedFDeriv n)


-- @@ L3074-3075 verbatim
theorem velocity_memLp (L : Space →L[ℝ] Space) : MemLp (velocity L) 2 volume :=
  (velocity_smooth L).continuous.memLp_of_hasCompactSupport (velocity_compact L)


-- @@ L3077-3079 verbatim
theorem field_solenoidal (L : Space →L[ℝ] Space) :
    (velocity_memLp L).toLp (velocity L) ∈ solenoidalSpace :=
  smooth_mem_solenoidal (velocity L) (velocity_smooth L) (velocity_memLp L) (velocity_divergence L)


-- @@ L3081-3084 verbatim
/-- Linear, given by `(EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 0 1+β •
EuclideanSpace.single 2 1)`. -/
def linear (β : ℝ) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1)


-- @@ L3086-3087 verbatim
@[simp] theorem linear_apply (β : ℝ) (x : Space) :
    linear β x=x 1 • (EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1) := rfl


-- @@ L3089-3091 verbatim
theorem linear_trace (β : ℝ) : LinearMap.trace ℝ Space (linear β).toLinearMap=0 := by
  rw [← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace,Fin.sum_univ_three,linear_apply,PiLp.smul_apply]


-- @@ L3093-3102 verbatim
theorem linear_norm (β : ℝ) : ‖linear β‖ ≤ 1+|β| := by
  apply opNorm_le_bound _ (by positivity)
  intro x
  rw [linear_apply,norm_smul,Real.norm_eq_abs]
  have hv : ‖(EuclideanSpace.single 0 1 : Space)+β • EuclideanSpace.single 2 1‖ ≤ 1+|β| := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    simp
  exact (mul_le_mul (PiLp.norm_apply_le x 1) hv (norm_nonneg _) (norm_nonneg x)).trans_eq (mul_comm
      _ _)


-- @@ L3104-3107 verbatim
theorem linear_q (β : ℝ) :
    linear β (EuclideanSpace.single 1 1)=EuclideanSpace.single 0 1+β • EuclideanSpace.single 2 1 :=
        by
  simp [linear_apply]


-- @@ L3109-3109 verbatim
end EulerBaseDatum


-- @@ L3111-3111 verbatim
end

-- @@ L3112-3112 verbatim
end


-- @@ L3114-3114 verbatim
end


-- @@ L3116-3116 verbatim
section


-- @@ L3118-3119 verbatim
/-! Pointwise factorial estimates suffice when one factor has compact
support. In particular polynomial factors need not be globally bounded. -/


-- @@ L3121-3121 verbatim
@[expose] public section


-- @@ L3123-3123 verbatim
noncomputable section


-- @@ L3125-3125 verbatim
namespace EulerGevreyFunctions


-- @@ L3127-3127 verbatim
open EulerGevrey EulerGevreyGeneratingDerivatives

-- @@ L3128-3128 verbatim
open scoped ContDiff


-- @@ L3130-3131 verbatim
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L3133-3143 verbatim
theorem product_bound_at (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : E)
    (hb₁ : ∀ n, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R 0 n)
    (hb₂ : ∀ n, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R 0 n) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤ (3*A*B)*majorant R 0 n := by
  have hp := sequence_product_majorant R A B hR hA hB 0 0
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb₁ k)
    (fun k => by simpa only [abs_norm] using hb₂ k) n
  exact (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
    ((le_abs_self _).trans (by simpa using hp))


-- @@ L3145-3148 verbatim
theorem majorant_one_le (R : ℝ) (hR : 1 ≤ R) (n : ℕ) : 1 ≤ majorant R 0 n := by
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  simpa only [majorant,Nat.add_zero] using
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) (by nlinarith : (1 : ℝ) ≤ (n.factorial : ℝ)^2)


-- @@ L3150-3160 verbatim
theorem id_bound_on_ball (r R : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (x : E) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ r*majorant R 0 n := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero,id_eq,majorant,Nat.zero_add,
      pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hx
  | succ n =>
    have hi := norm_iteratedFDeriv_id_le (n+1) (Nat.succ_pos _) x
    have hnorm : ‖iteratedFDeriv ℝ (n+1) (id : E → E) x‖ ≤ 1 := by
      split_ifs at hi <;> linarith
    exact hnorm.trans (one_le_mul_of_one_le_of_one_le hr (majorant_one_le R hR _))


-- @@ L3162-3168 verbatim
theorem linear_bound_on_ball (L : E →L[ℝ] V) (r R : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R)
    (x : E) (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (L : E → V) x‖ ≤ (‖L‖*r)*majorant R 0 n := by
  have h := L.norm_iteratedFDeriv_comp_left (f := id) (x := x) contDiffAt_id (by
      simp : (n : ℕ∞ω) ≤ ∞)
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (id_bound_on_ball r R hr hR x hx n) (norm_nonneg L))


-- @@ L3170-3183 verbatim
theorem compact_product_bound (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (K : Set E) (hK : tsupport f ⊆ K) (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb₁ : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R 0 n)
    (hb₂ : ∀ x ∈ K, ∀ n, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R 0 n) :
    ∀ n x, ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤ (3*A*B)*majorant R 0 n := by
  intro n x
  by_cases hx : x ∈ K
  · exact product_bound_at f g hf hg R A B hR hA hB x (fun j => hb₁ j x) (hb₂ x hx) n
  · have hn : x ∉ tsupport (fun y => f y*g y) := fun h => hx (hK (tsupport_mul_subset_left h))
    have hz : iteratedFDeriv ℝ n (fun y => f y*g y) x=0 := by
      by_contra hh
      exact hn (support_iteratedFDeriv_subset n hh)
    rw [hz,norm_zero]
    exact mul_nonneg (by positivity) (majorant_nonneg R hR 0 n)


-- @@ L3185-3185 verbatim
end EulerGevreyFunctions


-- @@ L3187-3187 verbatim
end

-- @@ L3188-3188 verbatim
end


-- @@ L3190-3190 verbatim
end


-- @@ L3192-3192 verbatim
section


-- @@ L3194-3195 verbatim
/-! Compact support turns actual uniform tensor bounds into the ordinary
L² tensor bounds used in the label Sobolev estimates. -/


-- @@ L3197-3197 verbatim
@[expose] public section


-- @@ L3199-3199 verbatim
noncomputable section


-- @@ L3201-3201 verbatim
namespace EulerLpTranslation.SmoothL2Field


-- @@ L3203-3203 verbatim
open Set MeasureTheory EulerSmoothLimit EulerGevrey


-- @@ L3205-3205 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L3207-3222 verbatim
theorem hasJetBound_of_support_sup (A : SmoothL2Field V) (K : Set Space)
    (hK : volume K ≠ ⊤) (hs : tsupport A.field ⊆ K)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hb : HasSupBound A.field C R) :
    A.HasJetBound (C*(volume K).toReal^(1/2 : ℝ)) R := by
  intro n
  have hzero : ∀ x ∉ K, iteratedFDeriv ℝ n A.field x=0 := by
    intro x hx
    by_contra hn
    exact hx (hs (support_iteratedFDeriv_subset n hn))
  have h := EulerMeanBoundary.lpNorm_le_bound_volume (iteratedFDeriv ℝ n A.field)
    (A.integrable n).aestronglyMeasurable K hK (C*R^n*(n.factorial : ℝ)^2)
    (by positivity) (hb n) hzero 2
  rw [norm_jetLp,toReal_eLpNorm]
  convert h using 1
  norm_num
  ring


-- @@ L3224-3224 verbatim
end EulerLpTranslation.SmoothL2Field


-- @@ L3226-3226 verbatim
end

-- @@ L3227-3227 verbatim
end


-- @@ L3229-3229 verbatim
end


-- @@ L3231-3231 verbatim
@[expose] public section


-- @@ L3233-3233 verbatim
noncomputable section


-- @@ L3235-3235 verbatim
namespace EulerBaseDatum


-- @@ L3237-3240 verbatim
open Set Filter ContinuousLinearMap MeasureTheory EulerSmoothLimit EulerVectorCalculus
  EulerSpatialCutoffs EulerGevrey EulerGevreyFunctions EulerLpTranslation
      EulerOperatorGevreyCalculus
  EulerMeanBoundary EulerMeanCutoffCurl EulerPacketPiola

-- @@ L3241-3241 verbatim
open scoped ContDiff Topology


-- @@ L3243-3247 verbatim
theorem coordinate_norm_le (i : Fin 3) : ‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  change ‖x i‖ ≤ 1*‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i


-- @@ L3249-3254 verbatim
theorem coordinate_bound_on_ball (i : Fin 3) (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : Space => y i) x‖ ≤ 2*majorant 256 0 n := by
  apply (linear_bound_on_ball (EuclideanSpace.proj i) 2 256 (by
      norm_num) (by norm_num) x hx n).trans
  exact mul_le_mul_of_nonneg_right (by linarith [coordinate_norm_le i])
    (majorant_nonneg 256 (by norm_num) 0 n)


-- @@ L3256-3264 verbatim
theorem linear_coordinate_bound_on_ball (L : Space →L[ℝ] Space) (i : Fin 3)
    (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => L y i) x‖ ≤ (2*‖L‖)*majorant 256 0 n := by
  have hL : ‖(EuclideanSpace.proj i).comp L‖ ≤ ‖L‖ := by
    apply (opNorm_comp_le _ _).trans
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right (coordinate_norm_le i) (norm_nonneg L))
  apply (linear_bound_on_ball ((EuclideanSpace.proj i).comp L) 2 256
    (by norm_num) (by norm_num) x hx n).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (majorant_nonneg 256 (by norm_num) 0 n)


-- @@ L3266-3293 verbatim
theorem linearPotential_bound (L : Space →L[ℝ] Space) (i : Fin 3)
    (x : Space) (hx : ‖x‖ ≤ 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (linearPotential L i) x‖ ≤ (24*‖L‖)*majorant 256 0 n := by
  let f : Space → ℝ := fun y => y (i+1)*L y (i+2)
  let g : Space → ℝ := fun y => y (i+2)*L y (i+1)
  have hs (a b : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y a*L y b) :=
    (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff.mul
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp L.contDiff)
  have hp (a b : Fin 3) :
      ‖iteratedFDeriv ℝ n (fun y : Space => y a*L y b) x‖ ≤ (12*‖L‖)*majorant 256 0 n := by
    have h := product_bound_at (fun y : Space => y a) (fun y => L y b)
      (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff
      ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).contDiff.comp L.contDiff)
      256 2 (2*‖L‖) (by norm_num) (by norm_num) (by positivity) x
      (coordinate_bound_on_ball a x hx) (linear_coordinate_bound_on_ball L b x hx) n
    convert h using 1
    ring
  have hfg : ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ (24*‖L‖)*majorant 256 0 n := by
    rw [iteratedFDeriv_sub_apply ((hs (i+1) (i+2)).contDiffAt.of_le (by simp))
      ((hs (i+2) (i+1)).contDiffAt.of_le (by simp))]
    exact (norm_sub_le _ _).trans ((add_le_add (hp (i+1) (i+2)) (hp (i+2) (i+1))).trans_eq (by
        ring))
  change ‖iteratedFDeriv ℝ n ((-1/3 : ℝ) • (f-g)) x‖ ≤ _
  have hfgsm : ContDiff ℝ ∞ (f-g) := (hs (i+1) (i+2)).sub (hs (i+2) (i+1))
  rw [iteratedFDeriv_const_smul_apply (a := (-1/3 : ℝ)) (f := f-g)
    (hfgsm.contDiffAt.of_le (by simp)),norm_smul]
  exact (mul_le_mul_of_nonneg_right (by norm_num : ‖(-1/3 : ℝ)‖ ≤ 1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hfg)


-- @@ L3295-3296 verbatim
/-- Cutoff amplitude, given by `(9*(1+3/EulerGevreyCutoff.bumpMass)^2)^3`. -/
def cutoffAmplitude : ℝ := (9*(1+3/EulerGevreyCutoff.bumpMass)^2)^3


-- @@ L3298-3298 verbatim
theorem cutoffAmplitude_nonneg : 0 ≤ cutoffAmplitude := by unfold cutoffAmplitude; positivity


-- @@ L3300-3301 verbatim
/-- Potential amplitude, given by `3*cutoffAmplitude*(24*‖L‖)`. -/
def potentialAmplitude (L : Space →L[ℝ] Space) : ℝ := 3*cutoffAmplitude*(24*‖L‖)


-- @@ L3303-3305 verbatim
theorem potentialAmplitude_nonneg (L : Space →L[ℝ] Space) : 0 ≤ potentialAmplitude L := by
  unfold potentialAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) cutoffAmplitude_nonneg) (by positivity)


-- @@ L3307-3313 verbatim
theorem potential_bound (L : Space →L[ℝ] Space) (i : Fin 3) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (potential L i) x‖ ≤ potentialAmplitude L*majorant 256 0 n := by
  exact compact_product_bound outerCutoff (linearPotential L i) outerCutoff_contDiff
    (contDiff_linearPotential L i) (Metric.closedBall 0 2) outerCutoff_support
    256 cutoffAmplitude (24*‖L‖) (by norm_num) cutoffAmplitude_nonneg (by positivity)
    outerCutoff_gevrey (fun y hy => linearPotential_bound L i y
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)) n x


-- @@ L3315-3317 verbatim
/-- Vector potential, given by `∑ i : Fin 3, potential L i x • EuclideanSpace.single i 1`. -/
def vectorPotential (L : Space →L[ℝ] Space) (x : Space) : Space :=
  ∑ i : Fin 3, potential L i x • EuclideanSpace.single i 1


-- @@ L3319-3321 verbatim
@[simp] theorem vectorPotential_apply (L : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    vectorPotential L x i=potential L i x := by
  fin_cases i <;> simp [vectorPotential,Fin.sum_univ_three]


-- @@ L3323-3324 verbatim
theorem vectorPotential_smooth (L : Space →L[ℝ] Space) : ContDiff ℝ ∞ (vectorPotential L) :=
  ContDiff.sum (fun i _ => (potential_smooth L i).smul contDiff_const)


-- @@ L3326-3329 verbatim
/-- Coordinate embedding, given by `(ContinuousLinearMap.id ℝ ℝ).smulRight
(EuclideanSpace.single i 1)`. -/
def coordinateEmbedding (i : Fin 3) : ℝ →L[ℝ] Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)


-- @@ L3331-3335 verbatim
theorem coordinateEmbedding_norm (i : Fin 3) : ‖coordinateEmbedding i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  change ‖x • (EuclideanSpace.single i 1 : Space)‖ ≤ 1*‖x‖
  simp [norm_smul]


-- @@ L3337-3354 verbatim
theorem vectorPotential_bound (L : Space →L[ℝ] Space) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (vectorPotential L) x‖ ≤ (3*potentialAmplitude L)*majorant 256 0 n := by
  unfold vectorPotential
  have hs (i : Fin 3) : ContDiff ℝ ∞ (fun y => potential L i y • (EuclideanSpace.single i 1 :
      Space)) :=
    (potential_smooth L i).smul contDiff_const
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i y => potential L i y • (EuclideanSpace.single i 1 : Space))
    (u := Finset.univ) (fun i _ => (hs i).contDiffAt.of_le (by simp))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, potentialAmplitude L*majorant 256 0 n := by
      apply Finset.sum_le_sum
      intro i _
      exact contraction_bound (coordinateEmbedding i) (coordinateEmbedding_norm i)
        (potential L i) (potential_smooth L i) 256 (potentialAmplitude L)
        (by norm_num) (potentialAmplitude_nonneg L) 0 (potential_bound L i) n x
    _ = _ := by simp; ring


-- @@ L3356-3364 verbatim
theorem velocity_eq_curlOperator (L : Space →L[ℝ] Space) :
    velocity L = fun x => curlOperator (fderiv ℝ (vectorPotential L) x) := by
  funext x
  rw [curlOperator_apply,← vectorCurl_eq_matrix _ x
    ((vectorPotential_smooth L).differentiable (by simp) x)]
  have he : (fun i x => vectorPotential L x i)=potential L := by
    funext i y
    exact vectorPotential_apply L y i
  exact congrArg (fun f => curl f x) he.symm


-- @@ L3366-3368 verbatim
/-- Velocity amplitude, given by `‖curlOperator‖*(3*potentialAmplitude L*256)`. -/
def velocityAmplitude (L : Space →L[ℝ] Space) : ℝ :=
  ‖curlOperator‖*(3*potentialAmplitude L*256)


-- @@ L3370-3374 verbatim
theorem velocityAmplitude_nonneg (L : Space →L[ℝ] Space) : 0 ≤ velocityAmplitude L := by
  unfold velocityAmplitude
  apply mul_nonneg
  · exact norm_nonneg curlOperator
  · exact mul_nonneg (mul_nonneg (by norm_num) (potentialAmplitude_nonneg L)) (by norm_num)


-- @@ L3376-3390 verbatim
theorem velocity_sup_bound (L : Space →L[ℝ] Space) : HasSupBound (velocity L) (velocityAmplitude L)
    1024 := by
  have hp : HasSupBound (vectorPotential L) (3*potentialAmplitude L) 256 := by
    intro n x
    simpa only [majorant,Nat.add_zero,mul_assoc] using vectorPotential_bound L n x
  have hd := hp.derivative (mul_nonneg (by norm_num) (potentialAmplitude_nonneg L))
    (by norm_num : (0 : ℝ) ≤ 256)
  rw [velocity_eq_curlOperator]
  intro n x
  have h := linear_bound curlOperator (fderiv ℝ (vectorPotential L))
    ((vectorPotential_smooth L).fderiv_right (m := ∞) (by simp))
    1024 (3*potentialAmplitude L*256) 0 (fun j y => by
      simpa only [majorant,Nat.add_zero,mul_assoc,show 4*(256 : ℝ)=1024 by
          norm_num] using hd j y) n x
  simpa only [velocityAmplitude,majorant,Nat.add_zero,mul_assoc] using h


-- @@ L3392-3393 verbatim
/-- Volume factor, given by `(volume (Metric.closedBall (0 : Space) 2)).toReal^(1/2 : ℝ)`. -/
def volumeFactor : ℝ := (volume (Metric.closedBall (0 : Space) 2)).toReal^(1/2 : ℝ)


-- @@ L3395-3395 verbatim
theorem volumeFactor_nonneg : 0 ≤ volumeFactor := Real.rpow_nonneg (ENNReal.toReal_nonneg) _


-- @@ L3397-3401 verbatim
theorem field_jet_bound (L : Space →L[ℝ] Space) :
    (field L).HasJetBound (velocityAmplitude L*volumeFactor) 1024 :=
  SmoothL2Field.hasJetBound_of_support_sup (field L) (Metric.closedBall 0 2)
    (isCompact_closedBall (0 : Space) 2).measure_lt_top.ne (velocity_support L)
    (velocityAmplitude L) 1024 (velocityAmplitude_nonneg L) (by norm_num) (velocity_sup_bound L)


-- @@ L3403-3403 verbatim
end EulerBaseDatum


-- @@ L3405-3405 verbatim
end

-- @@ L3406-3406 verbatim
end


-- @@ L3408-3408 verbatim
end


-- @@ L3410-3410 verbatim
section


-- @@ L3412-3414 verbatim
/-! A single positive time and a single label bound work for every
compact base datum with |β|≤1. The parent, inverse and Euler evolution
below are the actual constructed objects. -/


-- @@ L3416-3416 verbatim
section


-- @@ L3418-3420 verbatim
/-! A single factorial budget for every base datum with |β|≤1.
In particular this covers β=x₀⁻² with x₀≥1, independently of the
eventual frequency and iteration scales. -/


-- @@ L3422-3422 verbatim
@[expose] public section


-- @@ L3424-3424 verbatim
noncomputable section


-- @@ L3426-3426 verbatim
namespace EulerBaseDatum


-- @@ L3428-3429 verbatim
open Set EulerSmoothLimit EulerGevrey EulerLpTranslation EulerPacketPiola
  EulerPacketParentLabelBounds EulerMeanClassicalWordBounds EulerParameterWordGevrey


-- @@ L3431-3432 verbatim
/-- Uniform amplitude, given by `1+‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256)`. -/
def uniformAmplitude : ℝ := 1+‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256)


-- @@ L3434-3437 verbatim
theorem uniformAmplitude_pos : 0 < uniformAmplitude := by
  have h := cutoffAmplitude_nonneg
  unfold uniformAmplitude
  positivity


-- @@ L3439-3447 verbatim
theorem velocityAmplitude_le_uniform (β : ℝ) (hβ : |β| ≤ 1) :
    velocityAmplitude (linear β) ≤ uniformAmplitude := by
  have hL : ‖linear β‖ ≤ 2 := (linear_norm β).trans (by linarith)
  have hc := cutoffAmplitude_nonneg
  calc
    velocityAmplitude (linear β) ≤ ‖curlOperator‖*(3*(3*cutoffAmplitude*(24*2))*256) := by
      unfold velocityAmplitude potentialAmplitude
      gcongr
    _ ≤ uniformAmplitude := by unfold uniformAmplitude; linarith


-- @@ L3449-3452 verbatim
theorem velocity_uniform_sup (β : ℝ) (hβ : |β| ≤ 1) :
    HasSupBound (velocity (linear β)) uniformAmplitude 1024 :=
  (velocity_sup_bound (linear β)).mono (velocityAmplitude_nonneg _) (by norm_num)
    (velocityAmplitude_le_uniform β hβ) le_rfl


-- @@ L3454-3455 verbatim
/-- Uniform L² amplitude, given by `uniformAmplitude*volumeFactor`. -/
def uniformL2Amplitude : ℝ := uniformAmplitude*volumeFactor


-- @@ L3457-3458 verbatim
theorem uniformL2Amplitude_nonneg : 0 ≤ uniformL2Amplitude :=
  mul_nonneg uniformAmplitude_pos.le volumeFactor_nonneg


-- @@ L3460-3464 verbatim
theorem field_uniform_jet (β : ℝ) (hβ : |β| ≤ 1) :
    (field (linear β)).HasJetBound uniformL2Amplitude 1024 :=
  (field_jet_bound (linear β)).mono
    (mul_nonneg (velocityAmplitude_nonneg _) volumeFactor_nonneg) (by norm_num)
    (mul_le_mul_of_nonneg_right (velocityAmplitude_le_uniform β hβ) volumeFactor_nonneg) le_rfl


-- @@ L3466-3470 verbatim
/-- Uniform label bound, given by `1+sobolevCoefficientAmplitude (Fin 3) 6 1024
uniformL2Amplitude + sobolevCoefficientRadius (Fin 3) 1024`. -/
def uniformLabelBound : ℝ :=
  1+sobolevCoefficientAmplitude (Fin 3) 6 1024 uniformL2Amplitude +
    sobolevCoefficientRadius (Fin 3) 1024


-- @@ L3472-3477 verbatim
theorem uniformLabelBound_one : 1 ≤ uniformLabelBound := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 3) 6 1024 uniformL2Amplitude
    (by norm_num) uniformL2Amplitude_nonneg
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 3) 1024 (by norm_num)
  unfold uniformLabelBound
  linarith


-- @@ L3479-3489 verbatim
theorem field_uniform_label (β : ℝ) (hβ : |β| ≤ 1) :
    HasLabelBound uniformLabelBound (field (linear β)) := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 3) 6 1024 uniformL2Amplitude
    (by norm_num) uniformL2Amplitude_nonneg
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 3) 1024 (by norm_num)
  apply SmoothL2Field.hasLabelBound_of_jet_bound (field (linear β)) uniformL2Amplitude
    1024 uniformLabelBound uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
  · unfold uniformLabelBound
    linarith
  · unfold uniformLabelBound
    linarith


-- @@ L3491-3498 verbatim
theorem field_uniform_Hq (β : ℝ) (hβ : |β| ≤ 1) (q n : ℕ) :
    classicalBlockSize direction q (field (linear β)).toLp
      (field (linear β)).translation_contDiff n ≤
        sobolevCoefficientAmplitude (Fin 3) q 1024 uniformL2Amplitude *
          (sobolevCoefficientRadius (Fin 3) 1024)^n*(n.factorial : ℝ)^2 :=
  SmoothL2Field.classicalBlockSize_of_jet_bound direction (by intro i; simp [direction]) q
    (field (linear β)) uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)
    (field_uniform_jet β hβ) n


-- @@ L3500-3503 verbatim
theorem beta_bound (x₀ : ℝ) (hx : 1 ≤ x₀) : |(x₀^2)⁻¹| ≤ 1 := by
  have hpow : (1 : ℝ) ≤ x₀^2 := one_le_pow₀ hx
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x₀))]
  exact inv_le_one_of_one_le₀ hpow


-- @@ L3505-3507 verbatim
theorem initial_gradient (x₀ : ℝ) :
    fderiv ℝ (field (linear ((x₀^2)⁻¹))).field 0=linear ((x₀^2)⁻¹) :=
  velocity_fderiv_plateau _ (linear_trace _) 0 (by simp)


-- @@ L3509-3509 verbatim
end EulerBaseDatum


-- @@ L3511-3511 verbatim
end

-- @@ L3512-3512 verbatim
end


-- @@ L3514-3514 verbatim
end


-- @@ L3516-3516 verbatim
@[expose] public section


-- @@ L3518-3518 verbatim
noncomputable section


-- @@ L3520-3520 verbatim
namespace EulerBaseDatum


-- @@ L3522-3522 verbatim
open Set EulerSmoothLimit EulerParentPacketFrames


-- @@ L3524-3524 verbatim
local instance instBaseEulerInput1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩


-- @@ L3526-3529 verbatim
/-- Solution time, given by `EulerStaticEuler.baseTime 1 uniformL2Amplitude 1024
uniformL2Amplitude_nonneg (by norm_num)`. -/
def solutionTime : ℝ :=
  EulerStaticEuler.baseTime 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)


-- @@ L3531-3532 verbatim
theorem solutionTime_pos : 0 < solutionTime :=
  EulerStaticEuler.baseTime_pos 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)


-- @@ L3534-3538 verbatim
/-- Solution label constant, given by `EulerStaticEuler.baseLabelConstant 1 uniformL2Amplitude
1024 uniformL2Amplitude_nonneg (by norm_num)`. -/
def solutionLabelConstant : ℝ :=
  EulerStaticEuler.baseLabelConstant 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by
      norm_num)


-- @@ L3540-3540 verbatim
variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)


-- @@ L3542-3546 verbatim
/-- Solution parent, constructed using `EulerStaticEuler.baseParent`. -/
def solutionParent : Parent :=
  EulerStaticEuler.baseParent 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


-- @@ L3548-3552 verbatim
/-- Solution label data, constructed using `EulerStaticEuler.baseLabelData`. -/
def solutionLabelData : LabelData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseLabelData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


-- @@ L3554-3558 verbatim
/-- Solution inverse, constructed using `EulerStaticEuler.baseInverse`. -/
def solutionInverse : ParticleInverse (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseInverse 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


-- @@ L3560-3564 verbatim
/-- Solution evolution, constructed using `EulerStaticEuler.baseEvolution`. -/
def solutionEvolution : Evolution (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseEvolution 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


-- @@ L3566-3566 verbatim
theorem solutionParent_time : (solutionParent β hβ ell hell hell1).T=solutionTime := rfl


-- @@ L3568-3569 verbatim
theorem solutionLabelData_constant :
    (solutionLabelData β hβ ell hell hell1).K=solutionLabelConstant := rfl


-- @@ L3571-3574 verbatim
theorem solutionOddData : OddData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseOddData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 (velocity_odd (linear β))


-- @@ L3576-3581 verbatim
theorem solution_initial_velocity (x : Space) :
    (solutionParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,solutionTime_pos.le⟩ x =
      velocity (linear β) x :=
  EulerStaticEuler.baseParent_initial_velocity 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 x


-- @@ L3583-3590 verbatim
theorem solution_initial_gradient :
    fderiv ℝ ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space) 0=linear β := by
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_fderiv_plateau _ (linear_trace β) 0 (by simp)


-- @@ L3592-3599 verbatim
theorem solution_initial_support :
    tsupport ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space) ⊆ Metric.closedBall 0 2 := by
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_support _


-- @@ L3601-3603 verbatim
theorem solution_origin_fixed (t : Icc (0 : ℝ) solutionTime) :
    (solutionParent β hβ ell hell hell1).position t 0=0 :=
  (solutionOddData β hβ ell hell hell1).position_zero t


-- @@ L3605-3607 verbatim
omit β hβ ell hell hell1 in
theorem solutionLabelConstant_one : 1 ≤ solutionLabelConstant :=
  (solutionLabelData 0 (by norm_num) 1 zero_lt_one le_rfl).K_one


-- @@ L3609-3609 verbatim
end EulerBaseDatum


-- @@ L3611-3611 verbatim
end

-- @@ L3612-3612 verbatim
end


-- @@ L3614-3614 verbatim
end


-- @@ L3616-3616 verbatim
section


-- @@ L3618-3619 verbatim
/-! The actual normalized Euler pressure force has smooth ordinary L²
slices, with all derivative tensors continuous in time. -/


-- @@ L3621-3621 verbatim
@[expose] public section


-- @@ L3623-3623 verbatim
noncomputable section


-- @@ L3625-3625 verbatim
namespace EulerStaticEuler


-- @@ L3627-3628 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection


-- @@ L3630-3631 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)


-- @@ L3633-3637 verbatim
/-- Local force field, constructed using `SmoothL2Field.mapField`. -/
def localForceField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField (((amplitude P C R hC hR)⁻¹)^2 • ContinuousLinearMap.id ℝ Space)
    ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))


-- @@ L3639-3656 verbatim
theorem localForceField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localForceField P u C R hC hR hu hdiv t).field x=localForce P u C R hC hR hu hdiv (t,x) := by
  change ((amplitude P C R hC hR)⁻¹)^2 •
    ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField _).field x = _
  rw [FieldTower.zeroGraphField_apply]
  change ((amplitude P C R hC hR)⁻¹)^2 •
    (exactPacket P u C R hC hR hu hdiv).pressure.pointField _ _ =
      ((amplitude P C R hC hR)⁻¹)^2 •
        EulerConstantEuler.force (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t
            : ℝ),x)
  have ht := (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)
      t).property
  change (t : ℝ)/amplitude P C R hC hR ∈ Icc (0 : ℝ) 1 at ht
  have he : (amplitude P C R hC hR)⁻¹*(t : ℝ)=(t : ℝ)/amplitude P C R hC hR := by ring
  rw [he]
  simp only [EulerConstantEuler.force,ExactLiftedPacket.rawPressure,FieldTower.rawField,
    projIcc_of_mem zero_le_one ht]
  rfl


-- @@ L3658-3662 verbatim
theorem localForceField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (localForceField P u C R hC hR hu hdiv t).jetLp n) :=
  SmoothL2Field.continuous_jetLp_mapField _ _
    (fun n => ((exactPacket P u C R hC hR hu hdiv).pressure.zeroGraphField_jetLp_continuous n).comp
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR)).continuous) n


-- @@ L3664-3664 verbatim
end EulerStaticEuler


-- @@ L3666-3666 verbatim
end

-- @@ L3667-3667 verbatim
end


-- @@ L3669-3669 verbatim
end


-- @@ L3671-3671 verbatim
section


-- @@ L3673-3675 verbatim
/-! The concrete local base evolution has actual continuous L² jets for
both velocity and pressure force. Consequently its Euler equation holds
strongly in every finite Sobolev order, including endpoint derivatives. -/


-- @@ L3677-3677 verbatim
@[expose] public section


-- @@ L3679-3679 verbatim
noncomputable section


-- @@ L3681-3681 verbatim
namespace EulerStaticEuler


-- @@ L3683-3683 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerParentPacketFrames


-- @@ L3685-3687 verbatim
variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R)
  (hdiv : ∀ x, divergence u.field x = 0) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)


-- @@ L3689-3701 verbatim
/-- Base sobolev data, bundling `velocity`, `force`, `velocity_match`, `force_match` and the
required compatibility proofs. -/
def baseSobolevData : SobolevData (baseEvolution P u C R hC hR hu hdiv ell hell hell1) where
  velocity t := localField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  force t := localForceField P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
  velocity_match t x := (localField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
      x).symm
  force_match t x := (localForceField_apply P u C R hC hR hu hdiv (baseInclusion P C R hC hR t)
      x).symm
  velocity_continuous n := (localField_jetLp_continuous P u C R hC hR hu hdiv n).comp
    (baseInclusion P C R hC hR).continuous
  force_continuous n := (localForceField_jetLp_continuous P u C R hC hR hu hdiv n).comp
    (baseInclusion P C R hC hR).continuous


-- @@ L3703-3703 verbatim
end EulerStaticEuler


-- @@ L3705-3705 verbatim
namespace EulerBaseDatum


-- @@ L3707-3707 verbatim
open EulerParentPacketFrames


-- @@ L3709-3709 verbatim
local instance instBaseEulerSobolev1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩


-- @@ L3711-3716 verbatim
/-- Solution sobolev data, constructed using `EulerStaticEuler.baseSobolevData`. -/
def solutionSobolevData (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    SobolevData (solutionEvolution β hβ ell hell hell1) :=
  EulerStaticEuler.baseSobolevData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1


-- @@ L3718-3718 verbatim
end EulerBaseDatum


-- @@ L3720-3720 verbatim
end

-- @@ L3721-3721 verbatim
end


-- @@ L3723-3723 verbatim
end


-- @@ L3725-3725 verbatim
@[expose] public section


-- @@ L3727-3727 verbatim
noncomputable section


-- @@ L3729-3729 verbatim
namespace EulerBaseDatum


-- @@ L3731-3732 verbatim
open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerBaseEulerGuards EulerTransverseFrameCoordinates


-- @@ L3734-3735 verbatim
/-- Initial time, given by `guardTime solutionTime solutionLabelConstant`. -/
def initialTime : ℝ := guardTime solutionTime solutionLabelConstant


-- @@ L3737-3738 verbatim
theorem initialTime_pos : 0 < initialTime :=
  guardTime_pos _ _ solutionTime_pos


-- @@ L3740-3740 verbatim
theorem initialTime_le : initialTime ≤ solutionTime := guardTime_le _ _


-- @@ L3742-3742 verbatim
theorem initialTime_le_one : initialTime ≤ 1 := guardTime_le_one _ _


-- @@ L3744-3745 verbatim
/-- Initial coefficient cost, given by `coefficientCost solutionLabelConstant`. -/
def initialCoefficientCost : ℝ := coefficientCost solutionLabelConstant


-- @@ L3747-3747 verbatim
theorem initialCoefficientCost_nonneg : 0 ≤ initialCoefficientCost := coefficientCost_nonneg _


-- @@ L3749-3753 verbatim
theorem initialTime_small :
    initialCoefficientCost*initialTime ≤ 1/4 ∧
      EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost
          initialCoefficientCost*initialTime ≤ 1/4 :=
  guardTime_small _ _


-- @@ L3755-3755 verbatim
variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)


-- @@ L3757-3760 verbatim
/-- Initial parent, given by `(solutionParent β hβ ell hell hell1).restrictTime initialTime
initialTime_pos initialTime_le`. -/
def initialParent : Parent :=
  (solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3762-3765 verbatim
/-- Initial label data, given by `(solutionLabelData β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialLabelData : LabelData (initialParent β hβ ell hell hell1) :=
  (solutionLabelData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3767-3770 verbatim
/-- Initial inverse, given by `(solutionInverse β hβ ell hell hell1).restrictTime initialTime
initialTime_pos initialTime_le`. -/
def initialInverse : ParticleInverse (initialParent β hβ ell hell hell1) :=
  (solutionInverse β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3772-3775 verbatim
/-- Initial evolution, given by `(solutionEvolution β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialEvolution : Evolution (initialParent β hβ ell hell hell1) :=
  (solutionEvolution β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3777-3780 verbatim
/-- Initial sobolev data, given by `(solutionSobolevData β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialSobolevData : SobolevData (initialEvolution β hβ ell hell hell1) :=
  (solutionSobolevData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3782-3783 verbatim
theorem initialOddData : OddData (initialParent β hβ ell hell hell1) :=
  (solutionOddData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le


-- @@ L3785-3787 verbatim
/-- Initial low bounds, given by `lowBounds (solutionLabelData β hβ ell hell hell1)`. -/
def initialLowBounds : LowBounds (initialParent β hβ ell hell hell1) :=
  lowBounds (solutionLabelData β hβ ell hell hell1)


-- @@ L3789-3795 verbatim
theorem initialLowBounds_values :
    (initialLowBounds β hβ ell hell hell1).Be=initialCoefficientCost ∧
    (initialLowBounds β hβ ell hell hell1).Bc=0 ∧
    (initialLowBounds β hβ ell hell hell1).L=0 ∧
    (initialLowBounds β hβ ell hell hell1).r=0 ∧
    (initialLowBounds β hβ ell hell hell1).K=initialCoefficientCost :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩


-- @@ L3797-3797 verbatim
theorem initialParent_time : (initialParent β hβ ell hell hell1).T=initialTime := rfl


-- @@ L3799-3800 verbatim
theorem initialLabelData_constant :
    (initialLabelData β hβ ell hell hell1).K=solutionLabelConstant := rfl


-- @@ L3802-3805 verbatim
theorem initial_velocity (x : Space) :
    (initialParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,initialTime_pos.le⟩ x =
      velocity (linear β) x :=
  solution_initial_velocity β hβ ell hell hell1 x


-- @@ L3807-3811 verbatim
theorem initial_velocity_support :
    tsupport ((initialParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,initialTime_pos.le⟩ : Space → Space) ⊆ Metric.closedBall 0 2 := by
  rw [funext (initial_velocity β hβ ell hell hell1)]
  exact velocity_support _


-- @@ L3813-3820 verbatim
theorem solution_initialStrain (x : Space) (hx : ‖ell • x‖ < 1) :
    (solutionParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  rw [Parent.initialStrain_apply,Parent.first_apply]
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      (solutionParent β hβ ell hell hell1).zeroTime : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_fderiv_plateau _ (linear_trace β) (ell • x) hx


-- @@ L3822-3827 verbatim
theorem initialStrain_plateau (x : Space) (hx : ‖ell • x‖ < 1) :
    (initialParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  change ((solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos
    initialTime_le).initialStrain.field x=linear β
  erw [Parent.restrictTime_initialStrain]
  exact solution_initialStrain β hβ ell hell hell1 x hx


-- @@ L3829-3831 verbatim
theorem initial_strain_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).strain.field t x‖ ≤ initialCoefficientCost :=
  strain_norm (initialLabelData β hβ ell hell hell1) t x


-- @@ L3833-3835 verbatim
theorem initial_curvature_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).curvature.field t x‖ ≤ initialCoefficientCost :=
  curvature_norm (initialLabelData β hβ ell hell hell1) t x


-- @@ L3837-3839 verbatim
theorem initial_origin_fixed (t : Icc (0 : ℝ) initialTime) :
    (initialParent β hβ ell hell hell1).position t 0=0 :=
  (initialOddData β hβ ell hell hell1).position_zero t


-- @@ L3841-3844 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (R : U ≃ₗᵢ[ℝ] referencePlane (EuclideanSpace.single 0 1 : Space))
  (ξ : U) (hξ : (R ξ : Space) = EuclideanSpace.single 1 1)
  (S : Set Space) (hS : IsCompact S)


-- @@ L3846-3863 verbatim
include hξ in
theorem initial_pressure_numerator (t : Icc (0 : ℝ) initialTime)
    (x : Space) (hx : ‖ell • x‖ < 1) :
    1/2 ≤ ⟪((initialParent β hβ ell hell hell1).transverseData
      (EuclideanSpace.single 0 1) (by simp) R S hS).normal.field t x,
      (initialParent β hβ ell hell hell1).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((initialParent β hβ ell hell hell1).transverseData
            (EuclideanSpace.single 0 1) (by simp) R S hS) ξ t x)⟫_ℝ := by
  have hξnorm : ‖ξ‖=1 := by
    have hn : ‖(R ξ : Space)‖=1 := by rw [hξ]; simp
    exact (R.norm_map ξ).symm.trans hn
  apply source_numerator_pos (initialLabelData β hβ ell hell hell1)
    (EuclideanSpace.single 0 1) (by simp) R S hS ξ hξnorm x _ _ _ t
  · rw [initialStrain_plateau β hβ ell hell hell1 x hx,hξ,linear_q]
    simp [EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]
  · exact initialTime_small.1.trans (by norm_num)
  · exact initialTime_small.2.trans (by norm_num)


-- @@ L3865-3879 verbatim
include hξ in
theorem initial_pressure_numerator_on_support (t : Icc (0 : ℝ) initialTime)
    (x : Space) (hx : x ∈ tsupport EulerSpatialCutoffs.innerCutoff) :
    1/2 ≤ ⟪((initialParent β hβ ell hell hell1).transverseData
      (EuclideanSpace.single 0 1) (by simp) R S hS).normal.field t x,
      (initialParent β hβ ell hell hell1).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((initialParent β hβ ell hell hell1).transverseData
            (EuclideanSpace.single 0 1) (by simp) R S hS) ξ t x)⟫_ℝ := by
  apply initial_pressure_numerator β hβ ell hell hell1 R ξ hξ S hS t x
  have hn : ‖x‖ < (1/2 : ℝ) := by
    simpa only [Metric.mem_ball,dist_zero_right] using EulerSpatialCutoffs.innerCutoff_support hx
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hell]
  have hb := mul_le_mul_of_nonneg_right hell1 (norm_nonneg x)
  linarith


-- @@ L3881-3881 verbatim
end EulerBaseDatum
