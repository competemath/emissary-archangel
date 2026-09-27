/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity


-- @@ L12-12 verbatim
/-! Exact scalar homogeneity of the actual compact terminal-data primary. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerTransversePacketProvider.InitialData


-- @@ L21-21 verbatim
open EulerLpCylinderTranslation EulerCylinderAngleAverage


-- @@ L23-24 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] {D : Data U}


-- @@ L26-32 verbatim
/-- Smul, bundling `value`, `orbit`, `mean_zero`. -/
def smul (Y : InitialData P D) (a : ℝ) : InitialData P D where
  value := a • Y.value
  orbit := by simpa only [Submodule.coe_smul_of_tower,map_smul] using Y.orbit.const_smul a
  mean_zero := by
    change average P (a • (Y.value : CylinderL2 P U)) = 0
    rw [map_smul,Y.mean_zero,smul_zero]


-- @@ L34-34 verbatim
end EulerTransversePacketProvider.InitialData


-- @@ L36-36 verbatim
namespace EulerTransversePacketPrimary


-- @@ L38-39 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerTransversePacketProvider


-- @@ L41-45 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y Z : InitialData P D)
  (a : ℝ) (h : Z.value = a • Y.value)


-- @@ L47-47 verbatim
include h


-- @@ L49-55 verbatim
theorem forwardInitial_eq_smul : (forwardInitial τ hτ hτT B Z).value =
    a • (forwardInitial τ hτ hτT B Y).value := by
  apply Subtype.ext
  change B.coefficients.endpointCoordinate P (Z.value : CylinderL2 P U) ⟨τ,hτ.le,le_rfl⟩ =
    a • B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U) ⟨τ,hτ.le,le_rfl⟩
  have he : (Z.value : CylinderL2 P U) = a • (Y.value : CylinderL2 P U) := congrArg Subtype.val h
  rw [he,map_smul,ContinuousMap.smul_apply]


-- @@ L57-61 verbatim
theorem pastVelocity_eq_smul : pastVelocity τ hτ hτT B Z = a • pastVelocity τ hτ hτT B Y := by
  change B.coefficients.endpointVelocity P (Z.value : CylinderL2 P U) =
    a • B.coefficients.endpointVelocity P (Y.value : CylinderL2 P U)
  have he : (Z.value : CylinderL2 P U) = a • (Y.value : CylinderL2 P U) := congrArg Subtype.val h
  rw [he,map_smul]


-- @@ L63-67 verbatim
theorem pastDerivative_eq_smul : pastDerivative τ hτ hτT B Z = a • pastDerivative τ hτ hτT B Y := by
  change B.coefficients.endpointDerivative P (Z.value : CylinderL2 P U) =
    a • B.coefficients.endpointDerivative P (Y.value : CylinderL2 P U)
  have he : (Z.value : CylinderL2 P U) = a • (Y.value : CylinderL2 P U) := congrArg Subtype.val h
  rw [he,map_smul]


-- @@ L69-80 verbatim
theorem futureVelocity_eq_smul : futureVelocity τ hτ hτT B Z = a • futureVelocity τ hτ hτT B Y := by
  unfold futureVelocity
  rw [(zeroForcing (D.tail τ hτ.le hτT)).velocityPath_eq_smul
    (zeroForcing (D.tail τ hτ.le hτT))
    (forwardInitial τ hτ hτT B Y) (forwardInitial τ hτ hτT B Z) a
    (by
      apply ContinuousMap.ext
      intro t
      apply Subtype.ext
      change (0 : CylinderL2 P Space) = a • 0
      exact (smul_zero a).symm) (forwardInitial_eq_smul τ hτ hτT B Y Z a h)]
  exact (includePath P D.support D.support_measurable).map_smul a _


-- @@ L82-94 verbatim
theorem futureDerivative_eq_smul : futureDerivative τ hτ hτT B Z = a • futureDerivative τ hτ hτT B
    Y := by
  unfold futureDerivative
  rw [(zeroForcing (D.tail τ hτ.le hτT)).derivativePath_eq_smul
    (zeroForcing (D.tail τ hτ.le hτT))
    (forwardInitial τ hτ hτT B Y) (forwardInitial τ hτ hτT B Z) a
    (by
      apply ContinuousMap.ext
      intro t
      apply Subtype.ext
      change (0 : CylinderL2 P Space) = a • 0
      exact (smul_zero a).symm) (forwardInitial_eq_smul τ hτ hτT B Y Z a h)]
  exact (includePath P D.support D.support_measurable).map_smul a _


-- @@ L96-106 verbatim
theorem velocityPath_eq_smul : velocityPath τ hτ hτT B Z = a • velocityPath τ hτ hτT B Y := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.smul_apply]
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [velocityPath_left τ hτ hτT B Z th,velocityPath_left τ hτ hτT B Y th,
      pastVelocity_eq_smul τ hτ hτT B Y Z a h,ContinuousMap.smul_apply]
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    rw [velocityPath_right τ hτ hτT B Z tr,velocityPath_right τ hτ hτT B Y tr,
      futureVelocity_eq_smul τ hτ hτT B Y Z a h,ContinuousMap.smul_apply]


-- @@ L108-118 verbatim
theorem derivativePath_eq_smul : derivativePath τ hτ hτT B Z = a • derivativePath τ hτ hτT B Y := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.smul_apply]
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    rw [derivativePath_left τ hτ hτT B Z th,derivativePath_left τ hτ hτT B Y th,
      pastDerivative_eq_smul τ hτ hτT B Y Z a h,ContinuousMap.smul_apply]
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    rw [derivativePath_right τ hτ hτT B Z tr,derivativePath_right τ hτ hτT B Y tr,
      futureDerivative_eq_smul τ hτ hτT B Y Z a h,ContinuousMap.smul_apply]


-- @@ L120-120 verbatim
end EulerTransversePacketPrimary
