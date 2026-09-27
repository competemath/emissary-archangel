/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletMean
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletSupport
import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual


-- @@ L19-26 verbatim
/-!
# The actual forced transverse history on packet fields

The forcing is an ordinary admissible cylinder path. Source deformation and
Hessian data construct its zero-endpoint history, physical velocity, true
time derivative, and scalar pressure path. No output regularity or equation
is included in the input.
-/


-- @@ L28-28 verbatim
section


-- @@ L30-36 verbatim
/-!
# The literal spatial equation of the actual cylinder history

The Hilbert-space projected equation is an equality of genuine L² fields.
The adjoint multiplier identity turns it into the pointwise matrix equation
almost everywhere. Its normal residual is exactly the scalar source in (11).
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace EulerCylinderDirichlet.Coefficients


-- @@ L44-46 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTransverseGramInverse EulerTransverseNormalResidual EulerBoundedFieldCalculus

-- @@ L47-47 verbatim
open scoped BoundedContinuousFunction


-- @@ L49-53 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)
  (f : C(Icc (0 : ℝ) T, CylinderL2 P E))


-- @@ L55-89 verbatim
/-- The exact source equation (10) for the actual cylinder representatives. -/
theorem coordinate_equation_ae (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      gram (D.Q t x.1) (D.accelerationPath P f t x) =
        (D.Q t x.1).adjoint (f t x-(2 : ℝ) •
          D.Q₁ t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x)) := by
  let v := D.velocityPath P (pathLp T D.time_pos.le f) t
  let a := D.accelerationPath P f t
  let r := f t-(2 : ℝ) • fullOperatorMap P (D.Q₁ t) v
  have he : (fullOperatorMap P (D.Q t)).adjoint (fullOperatorMap P (D.Q t) a) =
      (fullOperatorMap P (D.Q t)).adjoint r := D.projected_equation P f t
  rw [fullOperatorMap_adjoint] at he
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t)))
      (fullOperatorMap P (D.Q t) a),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t))) r,
    Lp.coeFn_sub (f t) ((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v),
    Lp.coeFn_smul (2 : ℝ) (fullOperatorMap P (D.Q₁ t) v),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v]
    with x hl hq hr hsub hsmul hq₁
  have hp := congrArg (fun w : CylinderL2 P U => w x) he
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    fullOperatorMap P (adjointMap (D.Q t)) r x at hp
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    (D.Q t x.1).adjoint (fullOperatorMap P (D.Q t) a x) at hl
  change fullOperatorMap P (D.Q t) a x = D.Q t x.1 (a x) at hq
  change fullOperatorMap P (adjointMap (D.Q t)) r x = (D.Q t x.1).adjoint (r x) at hr
  change fullOperatorMap P (D.Q₁ t) v x = D.Q₁ t x.1 (v x) at hq₁
  rw [hl,hq,hr] at hp
  change r x = f t x-((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v) x at hsub
  change ((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v) x =
    (2 : ℝ) • (fullOperatorMap P (D.Q₁ t) v x) at hsmul
  rw [hsub,hsmul,hq₁] at hp
  exact hp


-- @@ L91-94 verbatim
theorem physicalVelocity_ae (t : Icc (0 : ℝ) T) :
    D.physicalVelocity P f t =ᵐ[liftMeasure P] fun x =>
      D.Q t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x) :=
  EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) _


-- @@ L96-107 verbatim
theorem physicalDerivative_ae (t : Icc (0 : ℝ) T) :
    D.physicalDerivative P f t =ᵐ[liftMeasure P] fun x =>
      D.Q₁ t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x) +
        D.Q t x.1 (D.accelerationPath P f t x) := by
  let v := D.velocityPath P (pathLp T D.time_pos.le f) t
  let a := D.accelerationPath P f t
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    Lp.coeFn_add (fullOperatorMap P (D.Q₁ t) v) (fullOperatorMap P (D.Q t) a)]
    with x h₁ h₂ hs
  exact hs.trans (congrArg₂ (·+·) h₁ h₂)


-- @@ L109-125 verbatim
/-- The scalar normal source in (11), derived from the actual inverse. -/
theorem physical_balance_ae
    (M : Icc (0 : ℝ) T → Space → E →L[ℝ] E) (m : Icc (0 : ℝ) T → Space → E)
    (hm : ∀ t x, m t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m t x, D.Q t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m t x, η⟫_ℝ = 0 → ∃ v, D.Q t x v = η)
    (hFlow : ∀ t x, D.Q₁ t x = (M t x).comp (D.Q t x))
    (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      D.physicalDerivative P f t x+M t x.1 (D.physicalVelocity P f t x) +
        ((⟪m t x.1,f t x⟫_ℝ-2*⟪m t x.1,M t x.1 (D.physicalVelocity P f t x)⟫_ℝ)/
          ‖m t x.1‖^2) • m t x.1 = f t x := by
  filter_upwards [D.coordinate_equation_ae P f t,D.physicalVelocity_ae P f t,
    D.physicalDerivative_ae P f t] with x he hv hd
  rw [hv,hd]
  exact physical_velocity_balance (D.Q t x.1) (D.Q₁ t x.1) (M t x.1) (m t x.1)
    (hm t x.1) (hTangent t x.1) (hRange t x.1) (hFlow t x.1) _ _ _ he


-- @@ L127-127 verbatim
end EulerCylinderDirichlet.Coefficients


-- @@ L129-129 verbatim
end

-- @@ L130-130 verbatim
end


-- @@ L132-132 verbatim
end


-- @@ L134-134 verbatim
@[expose] public section


-- @@ L136-136 verbatim
noncomputable section


-- @@ L138-138 verbatim
namespace EulerTransversePacketProvider.HistoryData


-- @@ L140-143 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerTimeLp
  EulerCylinderSmoothOrbit EulerCylinderAngleAverage EulerVolterraConvolution EulerMetricTransport
  EulerSourceNormalResidualBounds EulerPacketProfileRecursion

-- @@ L144-144 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L146-148 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)


-- @@ L150-151 verbatim
/-- Forcing path: an abbreviation for `includePath P D.support D.support_measurable G.path`. -/
abbrev forcingPath := includePath P D.support D.support_measurable G.path


-- @@ L153-156 verbatim
/-- Coordinate path, given by `B.coefficients.velocityPath P (pathLp D.T D.T_pos.le (forcingPath
G))`. -/
def coordinatePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.velocityPath P (pathLp D.T D.T_pos.le (forcingPath G))


-- @@ L158-160 verbatim
/-- Coordinate derivative path, given by `B.coefficients.accelerationPath P (forcingPath G)`. -/
def coordinateDerivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.accelerationPath P (forcingPath G)


-- @@ L162-164 verbatim
/-- Velocity path, given by `B.coefficients.physicalVelocity P (forcingPath G)`. -/
def velocityPath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.physicalVelocity P (forcingPath G)


-- @@ L166-168 verbatim
/-- Derivative path, given by `B.coefficients.physicalDerivative P (forcingPath G)`. -/
def derivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.physicalDerivative P (forcingPath G)


-- @@ L170-174 verbatim
/-- Pressure path, given by `sourcePressure P D.M D.normal D.normalLower D.normalLower_pos
D.normal_lower (forcingPath G) (B.velocityPath G)`. -/
def pressurePath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (forcingPath G) (B.velocityPath G)


-- @@ L176-178 verbatim
theorem coordinatePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (B.coordinatePath G)) :=
  B.coefficients.velocityPath_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff (forcingPath G) G.path_orbit


-- @@ L180-183 verbatim
theorem coordinateDerivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (B.coordinateDerivativePath G)) :=
  B.coefficients.accelerationPath_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff (forcingPath G) G.path_orbit


-- @@ L185-187 verbatim
theorem velocityPath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (B.velocityPath G)) :=
  B.coefficients.physicalVelocity_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff (forcingPath G) G.path_orbit


-- @@ L189-191 verbatim
theorem derivativePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (B.derivativePath G)) :=
  B.coefficients.physicalDerivative_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff (forcingPath G) G.path_orbit


-- @@ L193-195 verbatim
theorem pressurePath_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (B.pressurePath G)) :=
  sourcePressure_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (forcingPath G) (B.velocityPath G) G.path_orbit (B.velocityPath_orbit G)


-- @@ L197-200 verbatim
theorem coordinatePath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (B.coordinatePath G))
      (B.coordinateDerivativePath G t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.velocity_hasDerivWithinAt P (forcingPath G) t


-- @@ L202-205 verbatim
theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (B.velocityPath G))
      (B.derivativePath G t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.physicalVelocity_hasDerivWithinAt P (forcingPath G) t


-- @@ L207-210 verbatim
theorem coordinatePath_supported (t : Icc (0 : ℝ) D.T) :
    B.coordinatePath G t ∈ Supported P U D.support D.support_measurable :=
  B.coefficients.velocityPath_supported P D.support D.support_measurable
    (forcingPath G) (fun s => (G.path s).property) t


-- @@ L212-215 verbatim
theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    B.velocityPath G t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.physicalVelocity_supported P D.support D.support_measurable
    (forcingPath G) (fun s => (G.path s).property) t


-- @@ L217-220 verbatim
theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    B.derivativePath G t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.physicalDerivative_supported P D.support D.support_measurable
    (forcingPath G) (fun s => (G.path s).property) t


-- @@ L222-223 verbatim
theorem coordinatePath_mean_zero (t : Icc (0 : ℝ) D.T) : average P (B.coordinatePath G t) = 0 :=
  B.coefficients.velocityPath_mean_zero P (forcingPath G) G.mean_zero t


-- @@ L225-226 verbatim
theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) : average P (B.velocityPath G t) = 0 :=
  B.coefficients.physicalVelocity_mean_zero P (forcingPath G) G.mean_zero t


-- @@ L228-229 verbatim
theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) : average P (B.derivativePath G t) = 0 :=
  B.coefficients.physicalDerivative_mean_zero P (forcingPath G) G.mean_zero t


-- @@ L231-233 verbatim
/-- Field, given by `pointField P (B.velocityPath G) (B.velocityPath_orbit G) t`. -/
def field (t : Icc (0 : ℝ) D.T) : LiftDomain P → Space :=
  pointField P (B.velocityPath G) (B.velocityPath_orbit G) t


-- @@ L235-237 verbatim
/-- Derivative field, given by `pointField P (B.derivativePath G) (B.derivativePath_orbit G) t`. -/
def derivativeField (t : Icc (0 : ℝ) D.T) : LiftDomain P → Space :=
  pointField P (B.derivativePath G) (B.derivativePath_orbit G) t


-- @@ L239-241 verbatim
theorem field_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (B.field G t) x) :=
  pointField_smooth P (B.velocityPath G) (B.velocityPath_orbit G) t x


-- @@ L243-245 verbatim
theorem derivativeField_smooth (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (B.derivativeField G t) x) :=
  pointField_smooth P (B.derivativePath G) (B.derivativePath_orbit G) t x


-- @@ L247-249 verbatim
theorem field_ae (t : Icc (0 : ℝ) D.T) :
    B.velocityPath G t =ᵐ[liftMeasure P] B.field G t :=
  pointField_ae P (B.velocityPath G) (B.velocityPath_orbit G) t


-- @@ L251-253 verbatim
theorem derivativeField_ae (t : Icc (0 : ℝ) D.T) :
    B.derivativePath G t =ᵐ[liftMeasure P] B.derivativeField G t :=
  pointField_ae P (B.derivativePath G) (B.derivativePath_orbit G) t


-- @@ L255-259 verbatim
theorem field_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    HasDerivWithinAt (fun s => B.field G (D.clamp s) x)
      (B.derivativeField G t x) (Icc (0 : ℝ) D.T) t :=
  pointField_hasDerivWithinAt P D.T D.T_pos.le (B.velocityPath G) (B.derivativePath G)
    (B.velocityPath_orbit G) (B.derivativePath_orbit G) (B.velocityPath_time G) t x


-- @@ L261-266 verbatim
theorem field_zero_outside (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) (hx : x.1 ∉ D.support) :
    B.field G t x = 0 := by
  change pointField P (B.velocityPath G) (B.velocityPath_orbit G) t x = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (B.velocityPath_supported G t) x hx


-- @@ L268-274 verbatim
theorem derivativeField_zero_outside (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) (hx : x.1 ∉
    D.support) :
    B.derivativeField G t x = 0 := by
  change pointField P (B.derivativePath G) (B.derivativePath_orbit G) t x = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (B.derivativePath_supported G t) x hx


-- @@ L276-281 verbatim
omit [CompleteSpace U] in
theorem normal_ne_zero (t : Icc (0 : ℝ) D.T) (x : Space) : D.normal.field t x ≠ 0 := by
  intro hzero
  have hb := D.normal_lower t x
  rw [hzero,norm_zero,zero_pow (by omega : 2 ≠ 0)] at hb
  exact (not_le_of_gt D.normalLower_pos) hb


-- @@ L283-291 verbatim
theorem balance_ae (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      B.derivativePath G t x+D.M.field t x.1 (B.velocityPath G t x) +
        ((⟪D.normal.field t x.1,forcingPath G t x⟫_ℝ -
          2*⟪D.normal.field t x.1,D.M.field t x.1 (B.velocityPath G t x)⟫_ℝ)/
          ‖D.normal.field t x.1‖^2) • D.normal.field t x.1 = forcingPath G t x :=
  B.coefficients.physical_balance_ae P (forcingPath G)
    (fun t x => D.M.field t x) (fun t x => D.normal.field t x)
    (normal_ne_zero (D := D)) D.frame_tangent D.frame_range D.frame_strain t


-- @@ L293-304 verbatim
theorem field_tangent (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    ⟪D.normal.field t x.1,B.field G t x⟫_ℝ = 0 := by
  have hae : (fun y : LiftDomain P => ⟪D.normal.field t y.1,B.field G t y⟫_ℝ) =ᵐ[liftMeasure P]
      (fun _ => 0) := by
    filter_upwards [B.coefficients.physicalVelocity_ae P (forcingPath G) t,B.field_ae G t] with y
        hq ha
    change B.velocityPath G t y = D.frame.field t y.1 (B.coordinatePath G t y) at hq
    rw [← ha,hq]
    exact D.frame_tangent t y.1 _
  exact congrFun (Measure.eq_of_ae_eq hae
    (((D.normal.field t).continuous.comp continuous_fst).inner
      (smoothField_continuous P _ (B.field_smooth G t))) continuous_const) x


-- @@ L306-306 verbatim
end EulerTransversePacketProvider.HistoryData
