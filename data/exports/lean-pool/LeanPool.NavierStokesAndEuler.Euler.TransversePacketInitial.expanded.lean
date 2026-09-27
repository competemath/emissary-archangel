/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl


-- @@ L12-12 verbatim
/-! The constructed raw forward field has the prescribed actual initial data. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerCylinderSmoothOrbit


-- @@ L21-22 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerMetricTransport

-- @@ L23-23 verbatim
open scoped ContDiff


-- @@ L25-26 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L28-35 verbatim
theorem pointField_zero_of_value_zero (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (t : K) (ht : p t = 0) (x : LiftDomain P) : pointField P p hp t x = 0 := by
  have hrep := pointField_ae P p hp t
  rw [ht] at hrep
  exact congrFun (Measure.eq_of_ae_eq
    (hrep.symm.trans (Lp.coeFn_zero Space 2 (liftMeasure P)))
    (smoothField_continuous P _ (pointField_smooth P p hp t)) continuous_const) x


-- @@ L37-37 verbatim
end EulerCylinderSmoothOrbit


-- @@ L39-39 verbatim
namespace EulerTransversePacketProvider


-- @@ L41-43 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerLpCylinderRectangular EulerSourceCylinderEquation
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion


-- @@ L45-46 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


-- @@ L48-48 verbatim
namespace Forcing


-- @@ L50-50 verbatim
variable {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)


-- @@ L52-54 verbatim
theorem coordinatePath_initial : G.coordinatePath I ⟨0,le_rfl,D.T_pos.le⟩ = I.value :=
  coordinates_initial P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value


-- @@ L56-62 verbatim
theorem velocityPath_initial :
    G.velocityPath I ⟨0,le_rfl,D.T_pos.le⟩ =
      supportedOperatorMap P D.support D.support_measurable
        (D.frame.field ⟨0,le_rfl,D.T_pos.le⟩) I.value := by
  change supportedOperatorMap P D.support D.support_measurable
    (D.frame.field ⟨0,le_rfl,D.T_pos.le⟩) (G.coordinatePath I ⟨0,le_rfl,D.T_pos.le⟩) = _
  rw [G.coordinatePath_initial I]


-- @@ L64-74 verbatim
theorem vector_initial_of_zero (hi : I.value = 0) (x : Space) (θ : ℝ) :
    G.vector I (0,(x,θ)) = 0 := by
  have hv : G.velocityPath I ⟨0,le_rfl,D.T_pos.le⟩ = 0 := by
    rw [G.velocityPath_initial I,hi,map_zero]
  have hfull : includePath P D.support D.support_measurable (G.velocityPath I)
      ⟨0,le_rfl,D.T_pos.le⟩ = 0 := congrArg Subtype.val hv
  have h := pointField_zero_of_value_zero P
    (includePath P D.support D.support_measurable (G.velocityPath I))
    (G.velocityPath_orbit I) ⟨0,le_rfl,D.T_pos.le⟩ hfull (x,(θ : AddCircle P))
  simpa only [vector,EulerSourceCylinderClassical.field,Data.clamp,
    projIcc_of_mem D.T_pos.le (show (0 : ℝ) ∈ Icc 0 D.T from ⟨le_rfl,D.T_pos.le⟩)] using h


-- @@ L76-78 verbatim
theorem vector_zero_initial (x : Space) (θ : ℝ) :
    G.vector (InitialData.zero P D) (0,(x,θ)) = 0 :=
  G.vector_initial_of_zero (InitialData.zero P D) rfl x θ


-- @@ L80-80 verbatim
end Forcing


-- @@ L82-86 verbatim
theorem highSolve_zero_initial (D : Data U) (raw : VectorField)
    (h : Nonempty (Forcing P D raw)) (x : Space) (θ : ℝ) :
    (highSolve P D (InitialData.zero P D) raw).1 (0,(x,θ)) = 0 := by
  rw [highSolve_of_admissible D (InitialData.zero P D) raw h]
  exact (Classical.choice h).vector_zero_initial x θ


-- @@ L88-88 verbatim
end EulerTransversePacketProvider
