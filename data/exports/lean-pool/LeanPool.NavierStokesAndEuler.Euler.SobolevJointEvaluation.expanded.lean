/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation


-- @@ L11-11 verbatim
/-! Joint continuity of evaluation of genuine cylinder Sobolev fields. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerSobolevJointEvaluation


-- @@ L20-20 verbatim
open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevPointEvaluation


-- @@ L22-22 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L24-28 verbatim
/-- The actual point-evaluation operators have a uniform bound independent of the spatial point. -/
theorem pointEvaluation_norm_le (x : LiftDomain period) :
    ‖pointEvaluation period x‖ ≤ sobolevEmbeddingConstant period 3 :=
  (pointEvaluation period x).opNorm_le_bound
    (sobolevEmbeddingConstant_nonneg period 3) (fun u => representative_bound period u x)


-- @@ L30-41 verbatim
/-- Evaluation is jointly continuous in a genuine H3 field and a cylinder point. -/
theorem pointEvaluation_joint_continuous :
    Continuous (fun p : SobolevSpace period 3 × LiftDomain period =>
      pointEvaluation period p.2 p.1) := by
  apply continuous_prod_of_continuous_lipschitzWith _
    ⟨sobolevEmbeddingConstant period 3, sobolevEmbeddingConstant_nonneg period 3⟩
  · exact fun u => representative_continuous period u
  · intro x
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le
      (f := pointEvaluation period x)
      (K := ⟨sobolevEmbeddingConstant period 3, sobolevEmbeddingConstant_nonneg period 3⟩)
      (pointEvaluation_norm_le period x)


-- @@ L43-48 verbatim
/-- Every continuous genuine H3 path has a jointly continuous actual spatial representative. -/
theorem path_representative_joint_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 3)) :
    Continuous (fun p : T × LiftDomain period => pointEvaluation period p.2 (u p.1)) :=
  (pointEvaluation_joint_continuous period).comp
    ((u.continuous.comp continuous_fst).prodMk continuous_snd)


-- @@ L50-50 verbatim
end EulerSobolevJointEvaluation
