/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderMeanZero


-- @@ L13-21 verbatim
/-!
# The actual transverse forward operator on raw packet fields

The returned velocity and normalized pressure come from the constructed
supported cylinder solution. All source-frame hypotheses are discharged by
the deformation data. This module covers the forward interval, with genuine
prescribed initial coordinates; the zero initial datum gives the forced
operator used when t₀ = 0.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerTransversePacketProvider


-- @@ L30-33 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerMeanCoefficients EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderSmoothOrbit EulerCylinderAngleAverage EulerSourceCylinderClassical
  EulerPacketPointJets EulerPacketProfileRecursion EulerMetricTransport

-- @@ L34-34 verbatim
open scoped ContDiff


-- @@ L36-37 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


-- @@ L39-39 verbatim
namespace Forcing


-- @@ L41-41 verbatim
variable {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)


-- @@ L43-47 verbatim
/-- Vector as an element of `VectorField`. -/
def vector : VectorField := fun z =>
  field P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L49-53 verbatim
/-- Vector derivative as an element of `VectorField`. -/
def vectorDerivative : VectorField := fun z =>
  derivativeField P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L55-60 verbatim
/-- Scalar as an element of `ScalarField`. -/
def scalar : ScalarField := fun z =>
  pressureField P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero I.mean_zero (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L62-68 verbatim
theorem vector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun r => G.vector I (r,(x,θ))) (G.vectorDerivative I (t,(x,θ)))
      (Icc (0 : ℝ) D.T) t := by
  have h := field_hasDerivWithinAt P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.frame_derivative t (x,(θ : AddCircle P))
  simpa only [vector,vectorDerivative,Data.clamp,projIcc_of_mem D.T_pos.le t.property] using h


-- @@ L70-80 verbatim
/-- The literal transverse equation, including its constructed angular pressure. -/
theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative I (t,(x,θ))+D.strain (t,(x,θ)) (G.vector I (t,(x,θ))) +
      deriv (fun s : ℝ => G.scalar I (t,(x,s))) θ • D.normalField (t,(x,θ)) = raw (t,(x,θ)) := by
  have h := field_pressure_equation P D.support D.support_measurable D.support_compact D.T
      D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero I.mean_zero D.frame_tangent D.frame_range D.frame_strain t x θ
  rw [← G.raw_eq t x θ] at h
  simpa only [vector,vectorDerivative,scalar,Data.strain,Data.normalField,Data.clamp_coe] using h


-- @@ L82-86 verbatim
theorem vector_tangent (t : ℝ) (x : Space) (θ : ℝ) :
    ⟪D.normalField (t,(x,θ)),G.vector I (t,(x,θ))⟫_ℝ = 0 :=
  field_tangent P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.normal D.frame_tangent (D.clamp t) (x,(θ : AddCircle P))


-- @@ L88-93 verbatim
theorem scalar_normalized (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, G.scalar I (t,(x,θ))) = 0 :=
  pressureField_mean_zero P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero I.mean_zero (D.clamp t) x


-- @@ L95-102 verbatim
theorem vector_mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, G.vector I (t,(x,θ))) = 0 := by
  have hz := EulerSourceCylinderEquation.velocity_average_zero P D.support D.support_measurable
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    G.path I.value G.mean_zero I.mean_zero (D.clamp t)
  exact (pointField_mean_zero_iff P
    (includePath P D.support D.support_measurable (G.velocityPath I))
    (G.velocityPath_orbit I) (D.clamp t)).mp hz x


-- @@ L104-112 verbatim
theorem vector_spatial_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => G.vector I (t,y)) := by
  have h := field_smooth P D.support D.support_measurable D.support_compact D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
      G.path_orbit I.orbit (D.clamp t) 0
  convert h using 1
  first
    | rfl
    | (funext y; simp only [vector,localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add])


-- @@ L114-122 verbatim
theorem vectorDerivative_spatial_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => G.vectorDerivative I (t,y)) := by
  have h := derivativeField_smooth P D.support D.support_measurable D.support_compact D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
      G.path_orbit I.orbit (D.clamp t) 0
  convert h using 1
  first
    | rfl
    | (funext y; simp only [vectorDerivative,localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add])


-- @@ L124-133 verbatim
theorem scalar_spatial_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => G.scalar I (t,y)) := by
  have h := pressureField_smooth P D.support D.support_measurable D.support_compact D.T D.T_pos.le
      D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
      G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
      G.mean_zero I.mean_zero (D.clamp t) 0
  convert h using 1
  first
    | rfl
    | (funext y; simp only [scalar,localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add])


-- @@ L135-140 verbatim
theorem vector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.vector I (t,(x,θ)) = 0 := by
  by_contra h
  exact hx (field_tsupport_subset P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit (D.clamp t) (subset_closure h))


-- @@ L142-147 verbatim
theorem scalar_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    G.scalar I (t,(x,θ)) = 0 :=
  pressureField_zero_outside P D.support D.support_measurable D.support_compact D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
    G.path_orbit I.orbit D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    G.mean_zero I.mean_zero (D.clamp t) x hx θ


-- @@ L149-152 verbatim
theorem vector_periodic (t : ℝ) (x : Space) : Function.Periodic (fun θ => G.vector I (t,(x,θ))) P
    := by
  intro θ
  simp only [vector,AddCircle.coe_add_period]


-- @@ L154-157 verbatim
theorem scalar_periodic (t : ℝ) (x : Space) : Function.Periodic (fun θ => G.scalar I (t,(x,θ))) P
    := by
  intro θ
  simp only [scalar,AddCircle.coe_add_period]


-- @@ L159-159 verbatim
end Forcing


-- @@ L161-168 verbatim
/-- A total raw-field map backed by the actual forward solution on its admissible domain. -/
def highSolve (P : ℝ) [Fact (0 < P)] (D : Data U) (I : InitialData P D)
    (raw : VectorField) : VectorField × ScalarField := by
  classical
  exact if h : Nonempty (Forcing P D raw) then
    let G := Classical.choice h
    (G.vector I,G.scalar I)
  else (0,0)


-- @@ L170-173 verbatim
theorem highSolve_of_admissible (D : Data U) (I : InitialData P D) (raw : VectorField)
    (h : Nonempty (Forcing P D raw)) :
    highSolve P D I raw = ((Classical.choice h).vector I,(Classical.choice h).scalar I) := by
  simp only [highSolve,dite_eq_left h]


-- @@ L175-194 verbatim
theorem highSolve_contract (D : Data U) (I : InitialData P D) (raw : VectorField)
    (h : Nonempty (Forcing P D raw)) :
    ∃ a_t : VectorField,
      (∀ (t : Icc (0 : ℝ) D.T) x θ,
        HasDerivWithinAt (fun r => (highSolve P D I raw).1 (r,(x,θ)))
          (a_t (t,(x,θ))) (Icc (0 : ℝ) D.T) t) ∧
      (∀ (t : Icc (0 : ℝ) D.T) x θ,
        a_t (t,(x,θ))+D.strain (t,(x,θ)) ((highSolve P D I raw).1 (t,(x,θ))) +
          deriv (fun s => (highSolve P D I raw).2 (t,(x,s))) θ • D.normalField (t,(x,θ)) = raw
              (t,(x,θ))) ∧
      (∀ t, ContDiff ℝ ∞ (fun y : Space × ℝ => (highSolve P D I raw).1 (t,y))) ∧
      (∀ t, ContDiff ℝ ∞ (fun y : Space × ℝ => (highSolve P D I raw).2 (t,y))) ∧
      (∀ t x, (∫ θ in (0 : ℝ)..P, (highSolve P D I raw).2 (t,(x,θ))) = 0) := by
  rw [highSolve_of_admissible D I raw h]
  exact ⟨(Classical.choice h).vectorDerivative I,
    (Classical.choice h).vector_hasDerivWithinAt I,
    (Classical.choice h).equation I,
    (Classical.choice h).vector_spatial_smooth I,
    (Classical.choice h).scalar_spatial_smooth I,
    (Classical.choice h).scalar_normalized I⟩


-- @@ L196-196 verbatim
end EulerTransversePacketProvider
