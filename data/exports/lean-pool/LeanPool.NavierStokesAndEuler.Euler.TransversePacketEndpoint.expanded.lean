/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointEquation
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointSupport
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory


-- @@ L17-21 verbatim
/-!
The actual source history with prescribed compact terminal displacement.
`Y.value` is an L² field of reference-plane coordinates. It is passed to
the constructed affine-endpoint inverse, not imposed as a solution law.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerTransversePacketEndpoint


-- @@ L30-32 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderAngleAverage
  EulerVolterraConvolution EulerTransversePacketProvider EulerCylinderSmoothOrbit

-- @@ L33-33 verbatim
open scoped ContDiff


-- @@ L35-37 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (Y : InitialData P D)


-- @@ L39-42 verbatim
/-- Displacement path, given by `B.coefficients.endpointDisplacement P (Y.value : CylinderL2 P
U)`. -/
def displacementPath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointDisplacement P (Y.value : CylinderL2 P U)


-- @@ L44-46 verbatim
/-- Coordinate path, given by `B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U)`. -/
def coordinatePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U)


-- @@ L48-51 verbatim
/-- Coordinate derivative path, given by `B.coefficients.endpointAcceleration P (Y.value :
CylinderL2 P U)`. -/
def coordinateDerivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P U) :=
  B.coefficients.endpointAcceleration P (Y.value : CylinderL2 P U)


-- @@ L53-55 verbatim
/-- Velocity path, given by `B.coefficients.endpointVelocity P (Y.value : CylinderL2 P U)`. -/
def velocityPath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.endpointVelocity P (Y.value : CylinderL2 P U)


-- @@ L57-59 verbatim
/-- Derivative path, given by `B.coefficients.endpointDerivative P (Y.value : CylinderL2 P U)`. -/
def derivativePath : C(Icc (0 : ℝ) D.T,CylinderL2 P Space) :=
  B.coefficients.endpointDerivative P (Y.value : CylinderL2 P U)


-- @@ L61-62 verbatim
theorem displacement_initial : displacementPath B Y ⟨0,le_rfl,D.T_pos.le⟩ = 0 :=
  B.coefficients.endpointDisplacement_initial P Y.value


-- @@ L64-65 verbatim
theorem displacement_terminal : displacementPath B Y ⟨D.T,D.T_pos.le,le_rfl⟩ = Y.value :=
  B.coefficients.endpointDisplacement_terminal P Y.value


-- @@ L67-70 verbatim
theorem coordinatePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (coordinatePath B Y)) :=
  B.coefficients.endpointCoordinate_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit


-- @@ L72-75 verbatim
theorem coordinateDerivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (coordinateDerivativePath B Y)) :=
  B.coefficients.endpointAcceleration_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit


-- @@ L77-80 verbatim
theorem velocityPath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (velocityPath B Y)) :=
  B.coefficients.endpointVelocity_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit


-- @@ L82-85 verbatim
theorem derivativePath_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (derivativePath B Y)) :=
  B.coefficients.endpointDerivative_orbit_contDiff P D.frame.translation_contDiff
    D.frameDerivative.translation_contDiff B.H.translation_contDiff Y.value Y.orbit


-- @@ L87-90 verbatim
theorem displacementPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (displacementPath B Y))
      (coordinatePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointDisplacement_hasDerivWithinAt P Y.value t


-- @@ L92-95 verbatim
theorem coordinatePath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (coordinatePath B Y))
      (coordinateDerivativePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointCoordinate_hasDerivWithinAt P Y.value t


-- @@ L97-100 verbatim
theorem velocityPath_time (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (velocityPath B Y))
      (derivativePath B Y t) (Icc (0 : ℝ) D.T) t :=
  B.coefficients.endpointVelocity_hasDerivWithinAt P Y.value t


-- @@ L102-105 verbatim
theorem coordinatePath_supported (t : Icc (0 : ℝ) D.T) :
    coordinatePath B Y t ∈ Supported P U D.support D.support_measurable :=
  B.coefficients.endpointCoordinate_supported P D.support D.support_measurable
    Y.value Y.value.property t


-- @@ L107-110 verbatim
theorem velocityPath_supported (t : Icc (0 : ℝ) D.T) :
    velocityPath B Y t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.endpointVelocity_supported P D.support D.support_measurable
    Y.value Y.value.property t


-- @@ L112-115 verbatim
theorem derivativePath_supported (t : Icc (0 : ℝ) D.T) :
    derivativePath B Y t ∈ Supported P Space D.support D.support_measurable :=
  B.coefficients.endpointDerivative_supported P D.support D.support_measurable
    Y.value Y.value.property t


-- @@ L117-119 verbatim
theorem coordinatePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (coordinatePath B Y t) = 0 :=
  B.coefficients.endpointCoordinate_mean_zero P Y.value Y.mean_zero t


-- @@ L121-123 verbatim
theorem velocityPath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (velocityPath B Y t) = 0 :=
  B.coefficients.endpointVelocity_mean_zero P Y.value Y.mean_zero t


-- @@ L125-127 verbatim
theorem derivativePath_mean_zero (t : Icc (0 : ℝ) D.T) :
    average P (derivativePath B Y t) = 0 :=
  B.coefficients.endpointDerivative_mean_zero P Y.value Y.mean_zero t


-- @@ L129-136 verbatim
/-- Terminal initial, bundling `value`, `orbit`, `mean_zero`. -/
def terminalInitial : InitialData P D where
  value := ⟨coordinatePath B Y ⟨D.T,D.T_pos.le,le_rfl⟩,
    coordinatePath_supported B Y _⟩
  orbit := (ContinuousMap.evalCLM ℝ ⟨D.T,D.T_pos.le,le_rfl⟩ :
    C(Icc (0 : ℝ) D.T,CylinderL2 P U) →L[ℝ] CylinderL2 P U).contDiff.comp
      (coordinatePath_orbit B Y)
  mean_zero := coordinatePath_mean_zero B Y _


-- @@ L138-140 verbatim
theorem velocityPath_ae (t : Icc (0 : ℝ) D.T) :
    velocityPath B Y t =ᵐ[liftMeasure P] fun x => D.frame.field t x.1 (coordinatePath B Y t x) :=
  B.coefficients.endpointVelocity_ae P Y.value t


-- @@ L142-149 verbatim
theorem balance_ae (t : Icc (0 : ℝ) D.T) :
    ∀ᵐ x ∂liftMeasure P,
      derivativePath B Y t x+D.M.field t x.1 (velocityPath B Y t x) +
        (-(2*⟪D.normal.field t x.1,D.M.field t x.1 (velocityPath B Y t x)⟫_ℝ)/
          ‖D.normal.field t x.1‖^2) • D.normal.field t x.1 = 0 :=
  B.coefficients.endpoint_physical_balance_ae P Y.value
    (fun t x => D.M.field t x) (fun t x => D.normal.field t x)
    (HistoryData.normal_ne_zero (D := D)) D.frame_tangent D.frame_range D.frame_strain t


-- @@ L151-151 verbatim
end EulerTransversePacketEndpoint
