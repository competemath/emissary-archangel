/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData
import LeanPool.NavierStokesAndEuler.Euler.CylinderSliceRepresentatives
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketEndpoint
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointPointwise


-- @@ L15-19 verbatim
/-!
The actual joined primary, restricted to its history interval, is the
literal compact periodic wave times the finite-dimensional endpoint history.
In particular its angular derivative at zero has the manuscript's δ⁻¹ factor.
-/


-- @@ L21-21 verbatim
section


-- @@ L23-26 verbatim
/-!
The actual compact-terminal source history is the manuscript's pointwise
stationary history multiplied by the literal cutoff and periodic wave.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace EulerTransversePacketProvider.Data


-- @@ L34-34 verbatim
open ContinuousLinearMap EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransverseSourceFrame


-- @@ L36-36 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)


-- @@ L38-39 verbatim
/-- Coordinate embedding, given by `referenceEmbedding D.m₀ D.R`. -/
def coordinateEmbedding : U →L[ℝ] Space := referenceEmbedding D.m₀ D.R


-- @@ L41-45 verbatim
/-- Coordinate retraction, given by `D.R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
(referencePlane D.m₀).orthogonalProjectionOnto`. -/
def coordinateRetraction : Space →L[ℝ] U :=
  D.R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (referencePlane D.m₀).orthogonalProjectionOnto


-- @@ L47-51 verbatim
theorem coordinateRetraction_embedding (v : U) :
    D.coordinateRetraction (D.coordinateEmbedding v) = v := by
  change D.R.symm ((referencePlane D.m₀).orthogonalProjectionOnto (D.R v : Space)) = v
  rw [(referencePlane D.m₀).orthogonalProjectionOnto_mem_subspace_eq_self]
  exact D.R.symm_apply_apply v


-- @@ L53-53 verbatim
end EulerTransversePacketProvider.Data


-- @@ L55-55 verbatim
namespace EulerTransversePacketEndpoint


-- @@ L57-59 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMetricTransport EulerCylinderSmoothOrbit
  EulerTransversePacketProvider


-- @@ L61-63 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (Y : InitialData P D)


-- @@ L65-72 verbatim
theorem velocityPath_eq_history (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : (Y.value : CylinderL2 P U) =ᵐ[liftMeasure P] f)
    (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    pointField P (velocityPath B Y) (velocityPath_orbit B Y) t x =
      B.coefficients.labelVelocity x.1 (f x) t :=
  B.coefficients.endpointVelocity_pointwise P D.coordinateEmbedding D.coordinateRetraction
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Y.value Y.orbit D.coordinateRetraction_embedding f hf hrep x t


-- @@ L74-74 verbatim
end EulerTransversePacketEndpoint


-- @@ L76-76 verbatim
namespace EulerPacketTerminalDatum


-- @@ L78-80 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
  EulerLpCylinderTranslation EulerTransversePacketProvider EulerTransversePacketEndpoint
  EulerCylinderSmoothOrbit EulerSpatialCutoffs


-- @@ L82-84 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)


-- @@ L86-93 verbatim
theorem compact_wave_history (t : Icc (0 : ℝ) D.T) (x : LiftDomain period) :
    pointField period (velocityPath B (initialData D δ hδ ξ hs))
      (velocityPath_orbit B (initialData D δ hδ ξ hs)) t x =
      scalarField δ x • B.coefficients.labelVelocity x.1 ξ t := by
  rw [velocityPath_eq_history B (initialData D δ hδ ξ hs) (field δ ξ)
    (smoothField_continuous period _ (field_smooth δ hδ ξ)) (terminal_ae δ hδ ξ)]
  change B.coefficients.labelVelocity x.1 (scalarField δ x • ξ) t = _
  rw [map_smul,ContinuousMap.smul_apply]


-- @@ L95-95 verbatim
end EulerPacketTerminalDatum


-- @@ L97-97 verbatim
end

-- @@ L98-98 verbatim
end


-- @@ L100-100 verbatim
end


-- @@ L102-102 verbatim
@[expose] public section


-- @@ L104-104 verbatim
noncomputable section


-- @@ L106-106 verbatim
namespace EulerTransversePacketPrimary


-- @@ L108-111 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSmoothOrbit EulerMetricTransport
  EulerTransversePacketProvider EulerVolterraConvolution EulerPacketTerminalDatum
  EulerSpatialCutoffs EulerPeriodicProfile


-- @@ L113-116 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)


-- @@ L118-131 verbatim
theorem vector_eq_history (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : (Y.value : CylinderL2 P U) =ᵐ[liftMeasure P] f)
    (t : Icc (0 : ℝ) τ) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B Y (t,(x,θ)) =
      B.coefficients.labelVelocity x (f (x,(θ : AddCircle P))) t := by
  let tg : Icc (0 : ℝ) D.T := ⟨t,t.property.1,t.property.2.trans hτT.le⟩
  have he := congrFun (pointField_eq_of_slice_eq P (velocityPath τ hτ hτT B Y)
    (pastVelocity τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) tg t (velocityPath_left τ hτ hτT B Y t))
    (x,(θ : AddCircle P))
  change pointField P (velocityPath τ hτ hτT B Y) _ (D.clamp tg) _ = _
  rw [Data.clamp_coe]
  exact he.trans (EulerTransversePacketEndpoint.velocityPath_eq_history B
    (endpointData τ hτ hτT Y) f hf hrep t (x,(θ : AddCircle P)))


-- @@ L133-142 verbatim
omit P [Fact (0 < P)] Y in
theorem vector_compact_wave_history (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) τ) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) =
      (innerCutoff x*profile δ θ) • B.coefficients.labelVelocity x ξ t := by
  rw [vector_eq_history τ hτ hτT B (initialData D δ hδ ξ hs) (field δ ξ)
    (smoothField_continuous period _ (field_smooth δ hδ ξ)) (terminal_ae δ hδ ξ)]
  rw [field_coe,map_smul]
  rfl


-- @@ L144-156 verbatim
omit P [Fact (0 < P)] Y in
theorem angular_derivative_zero_history (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) τ) (x : Space) :
    HasDerivAt (fun θ : ℝ => vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)))
      ((innerCutoff x*δ⁻¹) • B.coefficients.labelVelocity x ξ t) 0 := by
  have he : (fun θ : ℝ => vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ))) =
      (fun θ => (innerCutoff x*profile δ θ) • B.coefficients.labelVelocity x ξ t) :=
    funext (vector_compact_wave_history τ hτ hτT B δ hδ ξ hs t x)
  rw [he]
  have hp := (profile_hasDerivAt δ hδ 0).differentiableAt.hasDerivAt
  rw [profile_deriv_zero δ hδ] at hp
  exact (hp.const_mul (innerCutoff x)).smul_const (B.coefficients.labelVelocity x ξ t)


-- @@ L158-164 verbatim
omit P [Fact (0 < P)] Y in
theorem angular_derivative_zero_origin (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) τ) :
    deriv (fun θ : ℝ => vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(0,θ))) 0 =
      δ⁻¹ • B.coefficients.labelVelocity 0 ξ t := by
  simpa only [innerCutoff_zero,one_mul] using
    (angular_derivative_zero_history τ hτ hτT B δ hδ ξ hs t 0).deriv


-- @@ L166-172 verbatim
omit P [Fact (0 < P)] Y in
theorem angular_derivative_zero_origin_norm (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) τ) :
    ‖deriv (fun θ : ℝ => vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(0,θ))) 0‖ =
      δ⁻¹ * ‖B.coefficients.labelVelocity 0 ξ t‖ := by
  rw [angular_derivative_zero_origin τ hτ hτT B δ hδ ξ hs t,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]


-- @@ L174-174 verbatim
end EulerTransversePacketPrimary
