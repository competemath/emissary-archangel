/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathGluing
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathNaturality
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketEndpoint
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalData
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketInitial
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTraceMatching


-- @@ L19-24 verbatim
/-!
The actual primary field on the full history-plus-forward interval.
Only the history interval uses the coercive endpoint solve. The forward
interval uses its true coordinate trace, and gluing preserves the actual
time derivative and the mixed translation orbit.
-/


-- @@ L26-26 verbatim
section


-- @@ L28-32 verbatim
/-!
The primary history has prescribed terminal displacement. Its actual
coordinate velocity at τ is the initial value of the homogeneous forward
solve. Both the physical velocity and its true derivative match at τ.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace EulerTransversePacketPrimary


-- @@ L40-44 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerVolterraConvolution

-- @@ L45-45 verbatim
open scoped ContDiff


-- @@ L47-48 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


-- @@ L50-57 verbatim
/-- Zero forcing, bundling `path`, `path_orbit`, `raw_eq`, `mean_zero`. -/
def zeroForcing (D : Data U) : Forcing P D (0 : VectorField) where
  path := 0
  path_orbit := by
    simpa only [map_zero] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P))))
  raw_eq t x θ := (pointField_zero_of_value_zero P _ _ t (by simp) (x,(θ : AddCircle P))).symm
  mean_zero _ := map_zero _


-- @@ L59-60 verbatim
variable {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)


-- @@ L62-66 verbatim
/-- Endpoint data, bundling `value`, `orbit`, `mean_zero`. -/
def endpointData : InitialData P (D.initial τ hτ hτT.le) where
  value := Y.value
  orbit := Y.orbit
  mean_zero := Y.mean_zero


-- @@ L68-72 verbatim
/-- Forward initial, bundling `value`, `orbit`, `mean_zero`. -/
def forwardInitial : InitialData P (D.tail τ hτ.le hτT) where
  value := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).value
  orbit := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).orbit
  mean_zero := (EulerTransversePacketEndpoint.terminalInitial B (endpointData τ hτ hτT Y)).mean_zero


-- @@ L74-77 verbatim
/-- Past velocity, given by `EulerTransversePacketEndpoint.velocityPath B (endpointData τ hτ hτT
Y)`. -/
def pastVelocity : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  EulerTransversePacketEndpoint.velocityPath B (endpointData τ hτ hτT Y)


-- @@ L79-82 verbatim
/-- Past derivative, given by `EulerTransversePacketEndpoint.derivativePath B (endpointData τ hτ
hτT Y)`. -/
def pastDerivative : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  EulerTransversePacketEndpoint.derivativePath B (endpointData τ hτ hτT Y)


-- @@ L84-88 verbatim
/-- Future velocity, given by `includePath P D.support D.support_measurable ((zeroForcing
(D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y))`. -/
def futureVelocity : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y))


-- @@ L90-94 verbatim
/-- Future derivative, given by `includePath P D.support D.support_measurable ((zeroForcing
(D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))`. -/
def futureDerivative : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath P D.support D.support_measurable
    ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y))


-- @@ L96-98 verbatim
theorem pastVelocity_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (pastVelocity τ hτ hτT B Y))
    :=
  EulerTransversePacketEndpoint.velocityPath_orbit B (endpointData τ hτ hτT Y)


-- @@ L100-102 verbatim
theorem pastDerivative_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (pastDerivative τ hτ hτT B
    Y)) :=
  EulerTransversePacketEndpoint.derivativePath_orbit B (endpointData τ hτ hτT Y)


-- @@ L104-106 verbatim
theorem futureVelocity_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (futureVelocity τ hτ hτT B
    Y)) :=
  (zeroForcing (D.tail τ hτ.le hτT)).velocityPath_orbit (forwardInitial τ hτ hτT B Y)


-- @@ L108-110 verbatim
theorem futureDerivative_orbit : ContDiff ℝ ∞ (fun a => pathTranslate P a (futureDerivative τ hτ
    hτT B Y)) :=
  (zeroForcing (D.tail τ hτ.le hτT)).derivativePath_orbit (forwardInitial τ hτ hτT B Y)


-- @@ L112-131 verbatim
theorem velocity_match : pastVelocity τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureVelocity τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hQ : (D.initial τ hτ hτT.le).frame.field th = (D.tail τ hτ.le hτT).frame.field tf := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    change D.F.field ⟨τ,hτ.le,hτT.le⟩ x (D.R v : Space) =
      D.F.field ⟨τ+0,by linarith,by linarith⟩ x (D.R v : Space)
    simp only [add_zero]
  change fullOperatorMap P ((D.initial τ hτ hτT.le).frame.field th)
    (EulerTransversePacketEndpoint.coordinatePath B (endpointData τ hτ hτT Y) th) =
      fullOperatorMap P ((D.tail τ hτ.le hτT).frame.field tf)
        (((zeroForcing (D.tail τ hτ.le hτT)).coordinatePath (forwardInitial τ hτ hτT B Y) tf) :
          CylinderL2 P U)
  dsimp only [tf]
  erw [Forcing.coordinatePath_initial,hQ]
  rfl


-- @@ L133-141 verbatim
theorem past_balance_ae (t : Icc (0 : ℝ) τ) :
    ∀ᵐ x ∂liftMeasure P,
      pastDerivative τ hτ hτT B Y t x +
        (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.initial τ hτ hτT.le).normal.field t x.1,
          (D.initial τ hτ hτT.le).M.field t x.1 (pastVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.initial τ hτ hτT.le).normal.field t x.1‖^2) •
            (D.initial τ hτ hτT.le).normal.field t x.1 = 0 :=
  EulerTransversePacketEndpoint.balance_ae B (endpointData τ hτ hτT Y) t


-- @@ L143-162 verbatim
theorem future_balance_ae (t : Icc (0 : ℝ) (D.T - τ)) :
    ∀ᵐ x ∂liftMeasure P,
      futureDerivative τ hτ hτT B Y t x +
        (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x) +
        (-(2*⟪(D.tail τ hτ.le hτT).normal.field t x.1,
          (D.tail τ hτ.le hτT).M.field t x.1 (futureVelocity τ hτ hτT B Y t x)⟫_ℝ)/
          ‖(D.tail τ hτ.le hτT).normal.field t x.1‖^2) •
            (D.tail τ hτ.le hτT).normal.field t x.1 = 0 := by
  let Df := D.tail τ hτ.le hτT
  have hh := EulerSourceCylinderEquation.velocity_balance_ae P D.support D.support_measurable
    Df.T Df.T_pos.le Df.frame Df.frameDerivative Df.frameLower Df.frameLower_pos Df.frame_lower
    (zeroForcing Df).path (forwardInitial τ hτ hτT B Y).value
    (fun t x => Df.M.field t x) (fun t x => Df.normal.field t x)
    (HistoryData.normal_ne_zero (D := Df)) Df.frame_tangent Df.frame_range Df.frame_strain t
  filter_upwards [hh,Lp.coeFn_zero Space 2 (liftMeasure P)] with x hx hz
  change futureDerivative τ hτ hτT B Y t x+Df.M.field t x.1 (futureVelocity τ hτ hτT B Y t x) +
    ((⟪Df.normal.field t x.1,(0 : LiftL2 P) x⟫_ℝ -
      2*⟪Df.normal.field t x.1,Df.M.field t x.1 (futureVelocity τ hτ hτT B Y t x)⟫_ℝ)/
      ‖Df.normal.field t x.1‖^2) • Df.normal.field t x.1 = (0 : LiftL2 P) x at hx
  simpa only [hz,Pi.zero_apply,inner_zero_right,zero_sub] using hx


-- @@ L164-176 verbatim
theorem derivative_match : pastDerivative τ hτ hτT B Y ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B Y ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hM : (D.initial τ hτ hτT.le).M.field th = (D.tail τ hτ.le hτT).M.field tf :=
    EulerTransversePacketJoin.source_coefficient_match τ hτ hτT D.M
  have hm : (D.initial τ hτ hτT.le).normal.field th = (D.tail τ hτ.le hτT).normal.field tf :=
    EulerTransversePacketJoin.normal_match τ hτ hτT
  have hh := past_balance_ae τ hτ hτT B Y th
  rw [hM,hm,velocity_match τ hτ hτT B Y] at hh
  apply Lp.ext
  filter_upwards [hh,future_balance_ae τ hτ hτT B Y tf] with x hx hy
  exact add_right_cancel (add_right_cancel (hx.trans hy.symm))


-- @@ L178-181 verbatim
theorem pastVelocity_time (t : Icc (0 : ℝ) τ) :
    HasDerivWithinAt (extendPath τ hτ.le (pastVelocity τ hτ hτT B Y))
      (pastDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) τ) t :=
  EulerTransversePacketEndpoint.velocityPath_time B (endpointData τ hτ hτT Y) t


-- @@ L183-186 verbatim
theorem futureVelocity_time (t : Icc (0 : ℝ) (D.T - τ)) :
    HasDerivWithinAt (extendPath (D.T-τ) (sub_pos.mpr hτT).le (futureVelocity τ hτ hτT B Y))
      (futureDerivative τ hτ hτT B Y t) (Icc (0 : ℝ) (D.T-τ)) t :=
  (zeroForcing (D.tail τ hτ.le hτT)).vectorField_time (forwardInitial τ hτ hτT B Y) t


-- @@ L188-188 verbatim
end EulerTransversePacketPrimary


-- @@ L190-190 verbatim
end

-- @@ L191-191 verbatim
end


-- @@ L193-193 verbatim
end


-- @@ L195-195 verbatim
@[expose] public section


-- @@ L197-197 verbatim
noncomputable section


-- @@ L199-199 verbatim
namespace EulerTransversePacketPrimary


-- @@ L201-204 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerElapsedTimePathGluing
  EulerVolterraConvolution EulerTransversePacketProvider EulerCylinderAngleAverage
  EulerSourceNormalResidualBounds

-- @@ L205-205 verbatim
open scoped ContDiff


-- @@ L207-210 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)


-- @@ L212-216 verbatim
/-- Velocity path, given by `join D.T τ hτ.le hτT.le (pastVelocity τ hτ hτT B Y) (futureVelocity
τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)`. -/
def velocityPath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y)
    (velocity_match τ hτ hτT B Y)


-- @@ L218-222 verbatim
/-- Derivative path, given by `join D.T τ hτ.le hτT.le (pastDerivative τ hτ hτT B Y)
(futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)`. -/
def derivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P) :=
  join D.T τ hτ.le hτT.le (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y)
    (derivative_match τ hτ hτT B Y)


-- @@ L224-228 verbatim
/-- Pressure path, given by `sourcePressure P D.M D.normal D.normalLower D.normalLower_pos
D.normal_lower 0 (velocityPath τ hτ hτT B Y)`. -/
def pressurePath : C(Icc (0 : ℝ) D.T,CylinderL2 P ℝ) :=
  sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y)


-- @@ L230-233 verbatim
theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (velocityPath τ hτ hτT B Y)) :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) (futureVelocity_orbit τ hτ hτT B Y)


-- @@ L235-238 verbatim
theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (derivativePath τ hτ hτT B Y)) :=
  join_orbit_contDiff P D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y)
    (pastDerivative_orbit τ hτ hτT B Y) (futureDerivative_orbit τ hτ hτT B Y)


-- @@ L240-245 verbatim
theorem pressurePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (pressurePath τ hτ hτT B Y)) :=
  sourcePressure_contDiff P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    0 (velocityPath τ hτ hτT B Y) (by simpa only [map_zero] using (contDiff_const :
      ContDiff ℝ ∞ (fun _ : LiftTangent => (0 : C(Icc (0 : ℝ) D.T,LiftL2 P)))))
    (velocityPath_orbit τ hτ hτT B Y)


-- @@ L247-250 verbatim
theorem velocityPath_left (t : Icc (0 : ℝ) τ) :
    velocityPath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastVelocity τ hτ hτT B Y t :=
  join_left D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) t


-- @@ L252-255 verbatim
theorem derivativePath_left (t : Icc (0 : ℝ) τ) :
    derivativePath τ hτ hτT B Y ⟨t,t.property.1,t.property.2.trans hτT.le⟩ =
      pastDerivative τ hτ hτT B Y t :=
  join_left D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) t


-- @@ L257-261 verbatim
theorem velocityPath_right (t : Icc τ D.T) :
    velocityPath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureVelocity τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) t


-- @@ L263-267 verbatim
theorem derivativePath_right (t : Icc τ D.T) :
    derivativePath τ hτ hτT B Y ⟨t,hτ.le.trans t.property.1,t.property.2⟩ =
      futureDerivative τ hτ hτT B Y
        ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ :=
  join_right D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) t


-- @@ L269-275 verbatim
theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath τ hτ hτT B Y))
      (derivativePath τ hτ hτT B Y t) (Icc (0 : ℝ) D.T) t :=
  join_hasDerivWithinAt D.T τ hτ.le hτT.le
    (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)
    (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)
    (pastVelocity_time τ hτ hτT B Y) (futureVelocity_time τ hτ hτT B Y) t


-- @@ L277-282 verbatim
theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) _
    (EulerTransversePacketEndpoint.velocityPath_supported B (endpointData τ hτ hτT Y))
    (fun s => ((zeroForcing (D.tail τ hτ.le hτT)).velocityPath (forwardInitial τ hτ hτT B Y)
        s).property) t


-- @@ L284-289 verbatim
theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath τ hτ hτT B Y t ∈ Supported P Space D.support D.support_measurable :=
  join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) _
    (EulerTransversePacketEndpoint.derivativePath_supported B (endpointData τ hτ hτT Y))
    (fun s => ((zeroForcing (D.tail τ hτ.le hτT)).derivativePath (forwardInitial τ hτ hτT B Y)
        s).property) t


-- @@ L291-302 verbatim
theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (velocityPath τ hτ hτT B Y t) = 0 := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y)
    {u | average P u = 0} _ _ t
  · exact EulerTransversePacketEndpoint.velocityPath_mean_zero B (endpointData τ hτ hτT Y)
  · intro s
    exact EulerSourceCylinderEquation.velocity_average_zero P D.support D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le
          hτT).frame_lower
      (zeroForcing (D.tail τ hτ.le hτT)).path (forwardInitial τ hτ hτT B Y).value
      (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s


-- @@ L304-316 verbatim
theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath τ hτ hτT B Y t) = 0 := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y)
    {u | average P u = 0} _ _ t
  · exact EulerTransversePacketEndpoint.derivativePath_mean_zero B (endpointData τ hτ hτT Y)
  · intro s
    exact EulerSourceCylinderEquation.velocityDerivative_average_zero P D.support
        D.support_measurable
      (D.T-τ) (sub_pos.mpr hτT).le (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
      (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos (D.tail τ hτ.le
          hτT).frame_lower
      (zeroForcing (D.tail τ hτ.le hτT)).path (forwardInitial τ hτ hτT B Y).value
      (zeroForcing (D.tail τ hτ.le hτT)).mean_zero (forwardInitial τ hτ hτT B Y).mean_zero s


-- @@ L318-318 verbatim
end EulerTransversePacketPrimary
