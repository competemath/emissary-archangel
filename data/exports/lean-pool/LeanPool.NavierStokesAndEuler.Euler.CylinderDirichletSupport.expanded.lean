/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.LpOperatorFieldAlgebra


-- @@ L14-14 verbatim
/-! Spatial support is preserved by the actual zero-endpoint history inverse. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerLpCylinderTranslation


-- @@ L23-24 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpCylinderPaths


-- @@ L26-28 verbatim
variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S)


-- @@ L30-33 verbatim
/-- Spatial cutoff, given by `cutoffOperator (liftMeasure P) (spatialSet P S)
(spatialSet_measurable P S hS)`. -/
def spatialCutoff : CylinderL2 P V →L[ℝ] CylinderL2 P V :=
  cutoffOperator (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS)


-- @@ L35-40 verbatim
theorem spatialCutoff_norm : ‖spatialCutoff (V := V) P S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖cutoff (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS) u‖ ≤ 1*‖u‖
  simpa only [one_mul] using cutoff_norm (liftMeasure P) (spatialSet P S) (spatialSet_measurable P
      S hS) u


-- @@ L42-45 verbatim
theorem spatialCutoff_fix (u : CylinderL2 P V) :
    u ∈ Supported P V S hS ↔ spatialCutoff P S hS u = u :=
  (mem_supportedSpace_iff (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS) u).trans
      eq_comm


-- @@ L47-49 verbatim
theorem spatialCutoff_adjoint [CompleteSpace V] :
    (spatialCutoff (V := V) P S hS).adjoint = spatialCutoff P S hS :=
  cutoffOperator_adjoint (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS)


-- @@ L51-51 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L53-59 verbatim
omit [CompactSpace K] in
theorem spatialCutoff_path_fix (f : C(K, CylinderL2 P V))
    (hf : ∀ t, f t ∈ Supported P V S hS) :
    (spatialCutoff P S hS).compLeftContinuous ℝ K f = f := by
  apply ContinuousMap.ext
  intro t
  exact (spatialCutoff_fix P S hS (f t)).1 (hf t)


-- @@ L61-61 verbatim
end EulerLpCylinderTranslation


-- @@ L63-63 verbatim
namespace EulerCylinderDirichlet.Coefficients


-- @@ L65-67 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerLpCylinderPaths EulerLpSupportedSubspace EulerTimeLp EulerTimeLpBoundedMap


-- @@ L69-72 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E) (S : Set Space) (hS : MeasurableSet S)


-- @@ L74-78 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem frame_cutoff (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frame P t (spatialCutoff P S hS u) = spatialCutoff P S hS (D.frame P t u) :=
  EulerLpOperatorField.full_cutoff (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (fieldLift P (D.Q t)) u


-- @@ L80-85 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem frameDerivative_cutoff (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frameDerivative P t (spatialCutoff P S hS u) = spatialCutoff P S hS (D.frameDerivative P t u)
        :=
  EulerLpOperatorField.full_cutoff (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (fieldLift P (D.Q₁ t)) u


-- @@ L87-91 verbatim
omit [CompleteSpace U] [CompleteSpace E] in
theorem hessian_cutoff (t : Icc (0 : ℝ) T) (u : CylinderL2 P E) :
    D.hessian P t (spatialCutoff P S hS u) = spatialCutoff P S hS (D.hessian P t u) :=
  EulerLpOperatorField.full_cutoff (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (fieldLift P (D.H t)) u


-- @@ L93-97 verbatim
theorem frame_cutoff_back (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frame P t ((spatialCutoff P S hS).adjoint u) =
      (spatialCutoff P S hS).adjoint (D.frame P t u) := by
  rw [spatialCutoff_adjoint,spatialCutoff_adjoint]
  exact D.frame_cutoff P S hS t u


-- @@ L99-103 verbatim
theorem frameDerivative_cutoff_back (t : Icc (0 : ℝ) T) (u : CylinderL2 P U) :
    D.frameDerivative P t ((spatialCutoff P S hS).adjoint u) =
      (spatialCutoff P S hS).adjoint (D.frameDerivative P t u) := by
  rw [spatialCutoff_adjoint,spatialCutoff_adjoint]
  exact D.frameDerivative_cutoff P S hS t u


-- @@ L105-111 verbatim
theorem velocityLp_cutoff (f : TimeLp T (CylinderL2 P E)) :
    D.velocityLp P (timeLift T (spatialCutoff P S hS) f) =
      timeLift T (spatialCutoff P S hS) (D.velocityLp P f) :=
  D.velocityLp_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f


-- @@ L113-119 verbatim
theorem velocityPath_cutoff (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.velocityPath P (timeLift T (spatialCutoff P S hS) f) t =
      spatialCutoff P S hS (D.velocityPath P f t) :=
  D.velocityPath_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f t


-- @@ L121-122 verbatim
variable (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
  (hf : ∀ t, f t ∈ Supported P E S hS)


-- @@ L124-133 verbatim
include hf in
theorem velocityPath_supported (t : Icc (0 : ℝ) T) :
    D.velocityPath P (pathLp T D.time_pos.le f) t ∈ Supported P U S hS := by
  apply (spatialCutoff_fix P S hS _).2
  have h := D.continuousVelocity_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f t
  rw [spatialCutoff_path_fix P S hS f hf] at h
  exact h.symm


-- @@ L135-144 verbatim
include hf in
theorem accelerationPath_supported (t : Icc (0 : ℝ) T) :
    D.accelerationPath P f t ∈ Supported P U S hS := by
  apply (spatialCutoff_fix P S hS _).2
  have h := D.accelerationPath_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f t
  rw [spatialCutoff_path_fix P S hS f hf] at h
  exact h.symm


-- @@ L146-155 verbatim
include hf in
theorem physicalVelocity_supported (t : Icc (0 : ℝ) T) :
    D.physicalVelocity P f t ∈ Supported P E S hS := by
  apply (spatialCutoff_fix P S hS _).2
  have h := D.physicalVelocity_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f t
  rw [spatialCutoff_path_fix P S hS f hf] at h
  exact h.symm


-- @@ L157-166 verbatim
include hf in
theorem physicalDerivative_supported (t : Icc (0 : ℝ) T) :
    D.physicalDerivative P f t ∈ Supported P E S hS := by
  apply (spatialCutoff_fix P S hS _).2
  have h := D.physicalDerivative_intertwines P D (spatialCutoff P S hS) (spatialCutoff P S hS)
    (D.frame_cutoff P S hS) (D.frameDerivative_cutoff P S hS)
    (D.frame_cutoff_back P S hS) (D.frameDerivative_cutoff_back P S hS)
    (D.hessian_cutoff P S hS) f t
  rw [spatialCutoff_path_fix P S hS f hf] at h
  exact h.symm


-- @@ L168-168 verbatim
end EulerCylinderDirichlet.Coefficients
