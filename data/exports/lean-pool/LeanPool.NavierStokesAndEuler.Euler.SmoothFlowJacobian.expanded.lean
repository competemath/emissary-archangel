/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
import LeanPool.NavierStokesAndEuler.Euler.ContinuousInverseDerivative
import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift


-- @@ L14-21 verbatim
/-!
# The genuine invertible Jacobian of the constructed nonlinear flow

Differentiating the path-space equation identifies its derivative with
the actual homogeneous linear evolution. The already constructed inverse
flow is therefore differentiable and smooth; its derivative is the actual
inverse fundamental operator, without an independent inverse assumption.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section



-- @@ L29-29 verbatim
open scoped ContDiff Topology


-- @@ L31-31 verbatim
namespace EulerSmoothBanachFlow


-- @@ L33-33 verbatim
open Set EulerContinuousTimeIntegral EulerLinearDuhamel


-- @@ L35-36 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)


-- @@ L38-42 verbatim
/-- Jacobian evolution, given by `constructedEvolution T hT (A.derivative.superposition
(pathFamily T hT A x))`. -/
def jacobianEvolution (x : E) :
    Evolution T hT (A.derivative.superposition (pathFamily T hT A x)) :=
  constructedEvolution T hT (A.derivative.superposition (pathFamily T hT A x))


-- @@ L44-50 verbatim
private theorem volterra_initialOperator {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}
    (U : Evolution T hT B) (v : E) :
    volterraOperator T hT B (U.initialOperator v) =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) v := by
  have h := U.solution_integral 0 v
  rw [U.solution_eq_operators, map_zero, add_zero, add_zero] at h
  exact sub_eq_iff_eq_add.mpr h


-- @@ L52-68 verbatim
theorem pathFamily_fderiv (x : E) :
    fderiv ℝ (pathFamily T hT A) x = (jacobianEvolution T hT A x).initialOperator := by
  have hp := ((pathFamily_contDiff T hT A).differentiable (by simp) x).hasFDerivAt
  have hc := (pathOperator_hasFDerivAt T hT A (pathFamily T hT A x)).comp x hp
  have he : (pathOperator T hT A) ∘ pathFamily T hT A =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) :=
    funext (pathOperator_pathFamily T hT A)
  rw [he] at hc
  have hconst := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := E) (F := C(Icc (0 : ℝ) T,E)) (x := x)
    (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T))
  have hD := hc.unique hconst
  apply ContinuousLinearMap.ext
  intro v
  apply (jacobianEvolution T hT A x).volterraOperator_injective
  rw [volterra_initialOperator]
  exact congrArg (fun L : E →L[ℝ] C(Icc (0 : ℝ) T,E) => L v) hD


-- @@ L70-73 verbatim
theorem jacobianEvolution_backward_initial (x : E) :
    (jacobianEvolution T hT A x).backward ⟨0,le_rfl,hT⟩ = ContinuousLinearMap.id ℝ E := by
  have h := (jacobianEvolution T hT A x).backward_forward ⟨0,le_rfl,hT⟩
  simpa only [jacobianEvolution, constructedEvolution_initial, ContinuousLinearMap.comp_id] using h


-- @@ L75-82 verbatim
theorem initialOperator_evaluation (x : E) (t : Icc (0 : ℝ) T) :
    (ContinuousMap.evalCLM ℝ t).comp (jacobianEvolution T hT A x).initialOperator =
      (jacobianEvolution T hT A x).forward t := by
  apply ContinuousLinearMap.ext
  intro v
  change (jacobianEvolution T hT A x).forward t
    ((jacobianEvolution T hT A x).backward ⟨0,le_rfl,hT⟩ v) = _
  rw [jacobianEvolution_backward_initial, ContinuousLinearMap.id_apply]


-- @@ L84-90 verbatim
theorem forward_hasFDerivAt_label (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (fun y => (flowData T hT A).forward t y)
      ((jacobianEvolution T hT A x).forward t) x := by
  have h := (ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp x
    (((pathFamily_contDiff T hT A).differentiable (by simp) x).hasFDerivAt)
  rw [pathFamily_fderiv, initialOperator_evaluation] at h
  exact h


-- @@ L92-95 verbatim
theorem forward_fderiv (t : Icc (0 : ℝ) T) (x : E) :
    fderiv ℝ (fun y => (flowData T hT A).forward t y) x =
      (jacobianEvolution T hT A x).forward t :=
  (forward_hasFDerivAt_label T hT A t x).fderiv


-- @@ L97-104 verbatim
/-- Jacobian equiv, constructed using `ContinuousLinearEquiv.equivOfInverse`. -/
def jacobianEquiv (t : Icc (0 : ℝ) T) (x : E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse ((jacobianEvolution T hT A x).forward t)
    ((jacobianEvolution T hT A x).backward t)
    (fun v => congrArg (fun L : E →L[ℝ] E => L v)
      ((jacobianEvolution T hT A x).backward_forward t))
    (fun v => congrArg (fun L : E →L[ℝ] E => L v)
      ((jacobianEvolution T hT A x).forward_backward t))


-- @@ L106-118 verbatim
theorem backward_hasFDerivAt_label (t : Icc (0 : ℝ) T) (x : E) :
    HasFDerivAt (fun y => (flowData T hT A).backward t y)
      ((jacobianEvolution T hT A ((flowData T hT A).backward t x)).backward t) x := by
  apply EulerContinuousInverseDerivative.hasFDerivAt_inverse
    (fun y => (flowData T hT A).forward t y) (fun y => (flowData T hT A).backward t y) x
    ((jacobianEvolution T hT A ((flowData T hT A).backward t x)).forward t)
  · exact ((flowData T hT A).backward_joint_continuous.comp
      (continuous_const.prodMk continuous_id)).continuousAt
  · exact forward_hasFDerivAt_label T hT A t _
  · exact Filter.Eventually.of_forall ((flowData T hT A).forward_backward t)
  · intro v
    exact congrArg (fun L : E →L[ℝ] E => L v)
      ((jacobianEvolution T hT A ((flowData T hT A).backward t x)).backward_forward t)


-- @@ L120-132 verbatim
theorem backward_contDiff (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y => (flowData T hT A).backward t y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (fun y => (flowData T hT A).backward t y)
    (fun y => (flowData T hT A).forward t y) id x ∞ (by simp)
    (((flowData T hT A).backward_joint_continuous.comp
      (continuous_const.prodMk continuous_id)).continuousAt)
    (forward_contDiff T hT A t).contDiffAt contDiff_id.contDiffAt
    (jacobianEquiv T hT A t ((flowData T hT A).backward t x))
  · exact forward_hasFDerivAt_label T hT A t _
  · exact (flowData T hT A).forward_backward t


-- @@ L134-134 verbatim
end EulerSmoothBanachFlow
