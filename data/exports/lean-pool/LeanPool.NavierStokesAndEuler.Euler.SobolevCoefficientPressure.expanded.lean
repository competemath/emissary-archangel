/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
import LeanPool.NavierStokesAndEuler.Euler.H6Pressure


-- @@ L12-13 verbatim
/-! Actual coefficient multiplication and the coercive projected pressure inverse as Sobolev CLMs.
-/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerSobolevCoefficientPressure


-- @@ L22-24 verbatim
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCoerciveProjection EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace


-- @@ L26-26 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L28-34 verbatim
/-- A genuine jet has exactly its source derivative-sum norm when regarded as a complete Sobolev
element. -/
theorem sumNorm_ofJet {q : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection q f) :
    sumNorm period (ofJet period J) = J.sobolevNorm := by
  rw [sumNorm_eq_jet]
  exact EulerH6Pressure.SpatialJet.norm_unique (toJet period (ofJet period J)) J (value_ofJet
      period J)


-- @@ L36-40 verbatim
/-- An L² operator with a genuine derivative-jet construction acts on the complete Sobolev space. -/
def jetLift {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (Jmap : ∀ {f : LiftL2 period}, SpatialJet period standardDirection q f →
      SpatialJet period standardDirection q (A f))
    (u : SobolevSpace period q) : SobolevSpace period q := ofJet period (Jmap (toJet period u))


-- @@ L42-47 verbatim
/-- The jet lift has exactly the original L² value. -/
@[simp]
theorem jetLift_value {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (Jmap : ∀ {f : LiftL2 period}, SpatialJet period standardDirection q f →
      SpatialJet period standardDirection q (A f)) (u : SobolevSpace period q) :
    value period (jetLift period A Jmap u) = A (value period u) := value_ofJet period _


-- @@ L49-61 verbatim
/-- The actual jet estimate controls the complete Sobolev operator norm. -/
theorem jetLift_bound {q : ℕ} (A : LiftL2 period →L[ℝ] LiftL2 period)
    (Jmap : ∀ {f : LiftL2 period}, SpatialJet period standardDirection q f →
      SpatialJet period standardDirection q (A f)) (C : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ {f : LiftL2 period} (J : SpatialJet period standardDirection q f),
      (Jmap J).sobolevNorm ≤ C * J.sobolevNorm) (u : SobolevSpace period q) :
    ‖jetLift period A Jmap u‖ ≤ (C * (Fintype.card (SobolevWord q) : ℝ)) * ‖u‖ := by
  have h := norm_le_sumNorm period (jetLift period A Jmap u)
  rw [jetLift, sumNorm_ofJet] at h
  have hj := hJ (toJet period u)
  rw [← sumNorm_eq_jet] at hj
  exact (h.trans hj).trans ((mul_le_mul_of_nonneg_left (sumNorm_le_card_norm period u) hC).trans_eq
    (mul_assoc _ _ _).symm)


-- @@ L63-81 verbatim
/-- Uniqueness of derivative arrays makes a genuine L² jet lift linear. -/
def jetLiftLinearMap (q : ℕ) (A : LiftL2 period →L[ℝ] LiftL2 period)
    (Jmap : ∀ {f : LiftL2 period}, SpatialJet period standardDirection q f →
      SpatialJet period standardDirection q (A f)) : SobolevSpace period q →ₗ[ℝ] SobolevSpace
          period q where
  toFun := jetLift period A Jmap
  map_add' := by
    intro u v
    apply value_injective period
    change value period (jetLift period A Jmap (u + v)) =
      value period (jetLift period A Jmap u) + value period (jetLift period A Jmap v)
    simp only [jetLift_value]
    exact map_add A _ _
  map_smul' := by
    intro r u
    apply value_injective period
    change value period (jetLift period A Jmap (r • u)) = r • value period (jetLift period A Jmap u)
    simp only [jetLift_value]
    exact map_smul A r _


-- @@ L83-91 verbatim
/-- The bounded continuous lift of an actual L² operator with proved derivative-jet estimates. -/
def jetLiftOperator (q : ℕ) (A : LiftL2 period →L[ℝ] LiftL2 period)
    (Jmap : ∀ {f : LiftL2 period}, SpatialJet period standardDirection q f →
      SpatialJet period standardDirection q (A f)) (C : ℝ) (hC : 0 ≤ C)
    (hJ : ∀ {f : LiftL2 period} (J : SpatialJet period standardDirection q f),
      (Jmap J).sobolevNorm ≤ C * J.sobolevNorm) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  (jetLiftLinearMap period q A Jmap).mkContinuous (C * (Fintype.card (SobolevWord q) : ℝ))
    (jetLift_bound period A Jmap C hC hJ)


-- @@ L93-99 verbatim
/-- Actual multiplication by a smooth bounded coefficient, as a Sobolev continuous linear map. -/
def coefficientSobolevOperator {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  jetLiftOperator period q A.operator (SpatialJet.multiply K) K.productConstant
      K.productConstant_nonneg
    (SpatialJet.multiply_norm_le K)


-- @@ L101-107 verbatim
/-- The coefficient Sobolev operator is represented by literal pointwise coefficient multiplication.
-/
@[simp]
theorem coefficientSobolevOperator_value {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (u : SobolevSpace period q) :
    value period (coefficientSobolevOperator period K u) = A.operator (value period u) :=
  jetLift_value period A.operator (SpatialJet.multiply K) u


-- @@ L109-115 verbatim
/-- The existing Lax–Milgram pressure inverse as an ambient L² continuous linear map. -/
def pressureL2Operator (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) :
    LiftL2 period →L[ℝ] LiftL2 period :=
  (gradientSpace period κ m).subtypeL.comp
    (pressureSolver (gradientSpace period κ m) A.operator c hc
      (coefficientOperator_coercive A.coefficient A.measurable A.bound A.norm_bound c hpos))


-- @@ L117-123 verbatim
/-- The bounded L² pressure operator agrees with the already constructed actual coercive pressure.
-/
@[simp]
theorem pressureL2Operator_apply (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc :
    0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    pressureL2Operator period A κ m c hc hpos f = A.pressure κ m c hc hpos f := rfl


-- @@ L125-134 verbatim
/-- The genuine coercive projected pressure inverse is a bounded map on every finite Sobolev space.
-/
def pressureSobolevOperator {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  jetLiftOperator period q (pressureL2Operator period A κ m c hc hpos)
    (fun J => J.solvePressure K κ m c hc hpos) (K.pressureConstant c) (K.pressureConstant_nonneg c
        hc)
    (fun J => J.solvePressure_norm_le K κ m c hc hpos)


-- @@ L136-144 verbatim
/-- The Sobolev pressure is exactly the actual coercive L² pressure on underlying fields. -/
@[simp]
theorem pressureSobolevOperator_value {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    value period (pressureSobolevOperator period K κ m c hc hpos u) = A.pressure κ m c hc hpos
        (value period u) :=
  jetLift_value period (pressureL2Operator period A κ m c hc hpos)
    (fun J => J.solvePressure K κ m c hc hpos) u


-- @@ L146-153 verbatim
/-- The explicit finite-order pressure bound on the complete Sobolev norm. -/
theorem pressureSobolevOperator_bound {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    ‖pressureSobolevOperator period K κ m c hc hpos u‖ ≤
      (K.pressureConstant c * (Fintype.card (SobolevWord q) : ℝ)) * ‖u‖ :=
  jetLift_bound period _ _ _ (K.pressureConstant_nonneg c hc)
    (fun J => J.solvePressure_norm_le K κ m c hc hpos) u


-- @@ L155-161 verbatim
/-- Subtracting the actual coefficient-weighted pressure defines the projected Euler forcing. -/
def projectedSourceOperator {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  ContinuousLinearMap.id ℝ _ -
    (coefficientSobolevOperator period K).comp (pressureSobolevOperator period K κ m c hc hpos)


-- @@ L163-172 verbatim
/-- The projected forcing has the literal pressure-corrected L² value. -/
@[simp]
theorem projectedSourceOperator_value {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    value period (projectedSourceOperator period K κ m c hc hpos u) =
      value period u - A.operator (A.pressure κ m c hc hpos (value period u)) := by
  change value period u - value period
    (coefficientSobolevOperator period K (pressureSobolevOperator period K κ m c hc hpos u)) = _
  rw [coefficientSobolevOperator_value, pressureSobolevOperator_value]


-- @@ L174-186 verbatim
/-- The actual pressure correction cancels the lifted gradient projection of the source. -/
theorem projectedSource_gradient_zero {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    gradientProjection period κ m (value period (projectedSourceOperator period K κ m c hc hpos u))
        = 0 := by
  rw [projectedSourceOperator_value, map_sub]
  have h := liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c hc
      hpos
    (value period u)
  change gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos (value period u))) =
    gradientProjection period κ m (value period u) at h
  rw [h, sub_self]


-- @@ L188-188 verbatim
end EulerSobolevCoefficientPressure
