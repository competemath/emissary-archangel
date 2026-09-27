/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedCorrector
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTimeParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryPressure
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletParity
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarParity


-- @@ L20-20 verbatim
/-! Joint parity of the complete constructed high inverse, pressure and actual corrector. -/


-- @@ L22-22 verbatim
section


-- @@ L24-24 verbatim
/-! Joint parity of the actual source history inverse and its normalized pressure. -/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace EulerTransversePacketProvider.HistoryData


-- @@ L32-35 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
      EulerCylinderFieldReflection
  EulerPacketProfileRecursion EulerCylinderScalarPrimitive EulerMetricTransport


-- @@ L37-43 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))


-- @@ L45-45 verbatim
include hF hM hH hraw


-- @@ L47-50 verbatim
theorem coordinatePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.coordinatePath G t) = -B.coordinatePath G t :=
  B.coefficients.velocityPath_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t


-- @@ L52-55 verbatim
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.velocityPath G t) = -B.velocityPath G t :=
  B.coefficients.physicalVelocity_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t


-- @@ L57-60 verbatim
theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (B.derivativePath G t) = -B.derivativePath G t :=
  B.coefficients.physicalDerivative_odd P (D.frame_even hF) (D.frameDerivative_even hF hM) hH
    (forcingPath G) (G.path_reflection_neg hraw) t


-- @@ L62-68 verbatim
theorem field_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.field G t (-x,((-θ : ℝ) : AddCircle P)) = -B.field G t (x,(θ : AddCircle P)) := by
  have he := representative_of_reflection P (B.velocityPath G t) (B.field G t)
    (B.field_ae G t) (smoothField_continuous P _ (B.field_smooth G t)) (-1)
    (by simpa only [neg_one_smul] using B.velocityPath_reflection_neg G hF hM hH hraw t)
    (x,(θ : AddCircle P))
  simpa only [Prod.neg_mk,AddCircle.coe_neg,neg_one_smul] using he


-- @@ L70-84 verbatim
theorem normalResidual_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.normalResidual G t (-x,((-θ : ℝ) : AddCircle P)) =
      -B.normalResidual G t (x,(θ : AddCircle P)) := by
  have hf : forceField G t (-x,((-θ : ℝ) : AddCircle P)) =
      -forceField G t (x,(θ : AddCircle P)) := by
    change pointField P (forcingPath G) G.path_orbit t (-x,((-θ : ℝ) : AddCircle P)) =
      -pointField P (forcingPath G) G.path_orbit t (x,(θ : AddCircle P))
    rw [← G.raw_eq t (-x) (-θ),← G.raw_eq t x θ]
    exact hraw t x θ
  change (⟪D.normal.field t (-x),forceField G t (-x,((-θ : ℝ) : AddCircle P))⟫_ℝ -
    2*⟪D.normal.field t (-x),D.M.field t (-x) (B.field G t (-x,((-θ : ℝ) : AddCircle P)))⟫_ℝ)/
    ‖D.normal.field t (-x)‖^2 = _
  rw [D.normal_even hF,hM,hf,B.field_odd G hF hM hH hraw]
  simp only [map_neg,inner_neg_right,normalResidual]
  ring


-- @@ L86-90 verbatim
theorem pressureField_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    B.pressureField G t (-x,((-θ : ℝ) : AddCircle P)) =
      B.pressureField G t (x,(θ : AddCircle P)) :=
  classicalPrimitive_joint_even P (B.normalResidual G t) (B.normalResidual_continuous G t)
    (B.normalResidual_mean_zero G t) (B.normalResidual_odd G hF hM hH hraw t) x θ


-- @@ L92-92 verbatim
end EulerTransversePacketProvider.HistoryData


-- @@ L94-94 verbatim
end

-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
@[expose] public section


-- @@ L101-101 verbatim
noncomputable section


-- @@ L103-103 verbatim
namespace EulerTransversePacketJoin


-- @@ L105-108 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing


-- @@ L110-118 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))


-- @@ L120-120 verbatim
include hF hM hH hraw


-- @@ L122-128 verbatim
theorem forwardInitial_reflection_neg :
    reflection P ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) =
      -((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) :=
  B.coordinatePath_reflection_neg (G.initial τ hτ hτT.le)
    (fun t x => hF (initialInclusion D.T τ hτT.le t) x)
    (fun t x => hM (initialInclusion D.T τ hτT.le t) x) hH
    (fun t x θ => hraw (initialInclusion D.T τ hτT.le t) x θ) ⟨τ,hτ.le,le_rfl⟩


-- @@ L130-130 verbatim
include hSym


-- @@ L132-138 verbatim
theorem futureVelocity_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection P (futureVelocity τ hτ hτT B G t) = -futureVelocity τ hτ hτT B G t :=
  (G.tail τ hτ.le hτT).velocityPath_reflection_neg (forwardInitial τ hτ hτT B G) hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (fun s x θ => hraw (tailInclusion D.T τ hτ.le s) x θ)
    (forwardInitial_reflection_neg τ hτ hτT B G hF hM hH hraw) t


-- @@ L140-148 verbatim
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (velocityPath τ hτ hτT B G t) = -velocityPath τ hτ hτT B G t := by
  apply join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B G)
    {u | reflection P u = -u} _ _ t
  · exact B.velocityPath_reflection_neg (G.initial τ hτ hτT.le)
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x) hH
      (fun s x θ => hraw (initialInclusion D.T τ hτT.le s) x θ)
  · exact futureVelocity_reflection_neg τ hτ hτT B G hSym hF hM hH hraw


-- @@ L150-153 verbatim
theorem vector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B G (t,(-x,-θ)) = -vector τ hτ hτT B G (t,(x,θ)) :=
  (vectorField τ hτ hτT B G).raw_odd_of_reflection_neg t
    (velocityPath_reflection_neg τ hτ hτT B G hSym hF hM hH hraw t) x θ


-- @@ L155-158 verbatim
theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B G (t,(-x,-θ)) = -vectorDerivative τ hτ hτT B G (t,(x,θ)) :=
  (vectorField τ hτ hτT B G).timeDerivative_odd (vectorDerivativeField τ hτ hτT B G)
    D.T_pos (vectorField_time τ hτ hτT B G) (vector_odd τ hτ hτT B G hSym hF hM hH hraw) t x θ


-- @@ L160-177 verbatim
theorem scalar_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B G (t,(-x,-θ)) = scalar τ hτ hτT B G (t,(x,θ)) := by
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [scalar_left τ hτ hτT B G th (-x) (-θ),scalar_left τ hτ hτT B G th x θ]
    exact B.pressureField_even (G.initial τ hτ hτT.le)
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x) hH
      (fun s x θ => hraw (initialInclusion D.T τ hτT.le s) x θ) th x θ
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    rw [scalar_right τ hτ hτT B G tr (-x) (-θ),scalar_right τ hτ hτT B G tr x θ]
    exact (G.tail τ hτ.le hτT).scalar_even (forwardInitial τ hτ hτT B G) hSym
      (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
      (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
      (fun s x θ => hraw (tailInclusion D.T τ hτ.le s) x θ)
      (forwardInitial_reflection_neg τ hτ hτT B G hF hM hH hraw) tf x θ


-- @@ L179-187 verbatim
theorem curlCorrector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    D.curlCorrector P (vector τ hτ hτT B G) (t,(-x,-θ)) =
      -D.curlCorrector P (vector τ hτ hτT B G) (t,(x,θ)) := by
  apply D.curlCorrector_odd P (vector τ hτ hτT B G) t
  · simpa only [Data.clamp_coe] using D.inverse_even hF t
  · exact (vectorField τ hτ hτT B G).raw_smooth t
  · exact vector_periodic τ hτ hτT B G t
  · exact vector_mean_zero τ hτ hτT B G t
  · exact vector_odd τ hτ hτT B G hSym hF hM hH hraw t


-- @@ L189-194 verbatim
theorem correctorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    correctorDerivative τ hτ hτT B G (t,(-x,-θ)) =
      -correctorDerivative τ hτ hτT B G (t,(x,θ)) :=
  (correctorField τ hτ hτT B G).timeDerivative_odd (correctorDerivativeField τ hτ hτT B G)
    D.T_pos (correctorField_time τ hτ hτT B G) (curlCorrector_odd τ hτ hτT B G hSym hF hM hH hraw)
        t x θ


-- @@ L196-196 verbatim
end EulerTransversePacketJoin
